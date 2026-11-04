module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.AffineVect
public import StacksFrontier.Deformation.Examples.Linear.ModulePatching
public import StacksFrontier.RingTheory.MilnorPatching.OneGeneratorFrobenius
public import StacksFrontier.RingTheory.MilnorPatching.ProjectiveModules

/-!
# Milnor patching for the square of Stacks Example 0EVG

Let `A` be a commutative ring, let `f : A` and let `J ⊆ A` be an ideal. The square

```
A ⧸ (J ⊓ fA) ---> A ⧸ J
     |               |
     v               v
   A ⧸ fA  ---> A ⧸ (J + fA)
```

is a ring fibre product in which the right vertical map is surjective
(`MilnorPatching.OneGeneratorFrobenius.situation`), so Milnor patching for finite projective
modules (Stacks Tag 0D2J) applies to it. This file records the resulting statement in the form
the two-fibre-product comparison of vector bundles needs it: an equivalence between the category
`FinProj` of finite projective modules over the upper-left corner and the *categorical* pullback
of the two extension-of-scalars functors between the `FinProj` categories of the other three
corners.

## Main results

* `CategoryTheory.Limits.categoricalPullbackFullSubcategoryEquiv`: the full subcategory of a
  categorical pullback `CategoricalPullback F G` cut out by a property on each of the two
  components is the categorical pullback of the two restricted functors.
* `AlgebraicGeometry.FinProj.equivalenceOfRingEquiv`: an isomorphism of rings induces an
  equivalence of their categories of finite projective modules, by extension of scalars.
* `MilnorPatching.OneGeneratorFrobenius.exists_oneGeneratorFinProjEquivalence`: Milnor patching
  for the square above, stated with `AlgebraicGeometry.FinProj` and with Mathlib's
  `CategoryTheory.Limits.CategoricalPullback`, together with the identification of the two
  components of the equivalence with the two reductions.
* `MilnorPatching.OneGeneratorFrobenius.finProjComparison`: the *canonical* comparison functor
  from finite projective `A ⧸ (J ∩ fA)`-modules to the compatible pairs, carrying not only the
  two extensions of scalars but also the canonical identification of their two further
  extensions to `A ⧸ (J + fA)`.
* `MilnorPatching.OneGeneratorFrobenius.exists_oneGeneratorFinProjEquivalence'`: the
  strengthening of `exists_oneGeneratorFinProjEquivalence` in which the equivalence is
  identified with the canonical comparison functor, so that the structural isomorphism of the
  compatible pair is recorded as well.
* `MilnorPatching.OneGeneratorFrobenius.exists_oneGeneratorFinProj_obj`: the object-level
  consequence, that the canonical comparison functor is essentially surjective; an isomorphism
  in the categorical pullback packages the two reduction isomorphisms together with their
  compatibility over `A ⧸ (J + fA)`.

## Implementation notes

Both sides of `CategoryTheory.Limits.categoricalPullbackFullSubcategoryEquiv` carry the same
data — an object of each full subcategory and an isomorphism between their images — the only
difference being whether the isomorphism is taken in the ambient category or in the full
subcategory on the target property. Since `CategoryTheory.ObjectProperty.ι` is the induced
functor of a structure projection, the two are the same up to structure eta, so the two functors
are mutually inverse *definitionally* and the unit and counit are `Iso.refl`.

The transport along the isomorphism `A ⧸ (J ⊓ fA) ≃+* A ⧸ J ×_{A ⧸ (J + fA)} A ⧸ fA` of the
fourth corner uses `CategoryTheory.Equivalence.congrFullSubcategory`, whose hypothesis is an
equality of properties of objects; the two inclusions of that equality are extension of scalars
along the isomorphism and along its inverse.

Carrying the structural isomorphism of a compatible pair through the transport chain needs the
compatibility of `ModuleGlueing.extensionOfScalarsToPullback` with precomposition, which is
`ModuleGlueing.extensionOfScalarsToPullbackPrecomp`. That isomorphism cannot be assembled from
the composition isomorphisms of extension of scalars alone — it is an instance of their
associativity coherence — so it is proved on the generators `1 ⊗ x`, using
`Deformation.Examples.exists_extensionOfScalarsToPullback_iso`.

`MilnorPatching.OneGeneratorFrobenius.finProjComparison` is defined as the restriction of
`MilnorPatching.OneGeneratorFrobenius.moduleComparison` to the full subcategories of finite
projective modules, rather than assembled at the level of `AlgebraicGeometry.FinProj` out of
`AlgebraicGeometry.FinProj.extendScalarsComp` and
`AlgebraicGeometry.FinProj.extendScalarsCongr`: the two presentations are definitionally equal,
but the kernel does not check that equality within its heartbeat budget, whereas the present
definition makes `finProjComparison_comp_π₁`, `finProjComparison_comp_π₂` and
`finProjComparison_obj_iso_hom_hom` cheap.

## References

* [Stacks Project, Tag 0D2J](https://stacks.math.columbia.edu/tag/0D2J)
* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

section FullSubcategoryPullback

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  (F : A ⥤ B) (G : C ⥤ B)
  (P : ObjectProperty A) (Q : ObjectProperty C) (S : ObjectProperty B)
  (hF : ∀ a, P a → S (F.obj a)) (hG : ∀ c, Q c → S (G.obj c))

/-- The property of an object of `CategoricalPullback F G` that its first component satisfies
`P` and its second component satisfies `Q`. -/
abbrev categoricalPullbackProperty : ObjectProperty (CategoricalPullback F G) :=
  fun X ↦ P X.fst ∧ Q X.snd

/-- The functor from the full subcategory of `CategoricalPullback F G` on the objects whose two
components satisfy `P` and `Q` to the categorical pullback of the functors `F` and `G` restricted
to those subcategories: an object is sent to the same pair of objects, with its structural
isomorphism read in the full subcategory on `S`. -/
def categoricalPullbackFullSubcategoryFunctor :
    (categoricalPullbackProperty F G P Q).FullSubcategory ⥤
      CategoricalPullback (ObjectProperty.lift S (P.ι ⋙ F) (fun a ↦ hF a.1 a.2))
        (ObjectProperty.lift S (Q.ι ⋙ G) (fun c ↦ hG c.1 c.2)) where
  obj X :=
    { fst := ⟨X.obj.fst, X.property.1⟩
      snd := ⟨X.obj.snd, X.property.2⟩
      iso :=
        { hom := ObjectProperty.homMk X.obj.iso.hom
          inv := ObjectProperty.homMk X.obj.iso.inv
          hom_inv_id := ObjectProperty.hom_ext _ X.obj.iso.hom_inv_id
          inv_hom_id := ObjectProperty.hom_ext _ X.obj.iso.inv_hom_id } }
  map f :=
    { fst := ObjectProperty.homMk f.hom.fst
      snd := ObjectProperty.homMk f.hom.snd
      w := ObjectProperty.hom_ext _ f.hom.w }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The structural isomorphism of the image of an object under
`CategoryTheory.Limits.categoricalPullbackFullSubcategoryFunctor` is, on underlying objects, the
structural isomorphism of that object. -/
@[simp]
lemma categoricalPullbackFullSubcategoryFunctor_obj_iso_hom_hom
    (X : (categoricalPullbackProperty F G P Q).FullSubcategory) :
    (((categoricalPullbackFullSubcategoryFunctor F G P Q S hF hG).obj X).iso.hom).hom =
      X.obj.iso.hom :=
  rfl

/-- The functor inverse to `CategoryTheory.Limits.categoricalPullbackFullSubcategoryFunctor`: an
object of the categorical pullback of the restricted functors is the same pair of objects
together with the image in the ambient category of its structural isomorphism. -/
def categoricalPullbackFullSubcategoryInverse :
    CategoricalPullback (ObjectProperty.lift S (P.ι ⋙ F) (fun a ↦ hF a.1 a.2))
        (ObjectProperty.lift S (Q.ι ⋙ G) (fun c ↦ hG c.1 c.2)) ⥤
      (categoricalPullbackProperty F G P Q).FullSubcategory where
  obj X :=
    { obj :=
        { fst := X.fst.obj
          snd := X.snd.obj
          iso := S.ι.mapIso X.iso }
      property := ⟨X.fst.property, X.snd.property⟩ }
  map f := ObjectProperty.homMk
    { fst := f.fst.hom
      snd := f.snd.hom
      w := S.ι.congr_map f.w }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The full subcategory of a categorical pullback on the objects whose two components satisfy
given properties is the categorical pullback of the restricted functors.** Both sides consist of
an object of each of the two full subcategories together with an isomorphism between their
images, read either in the ambient category or in the full subcategory on the target property. -/
def categoricalPullbackFullSubcategoryEquiv :
    (categoricalPullbackProperty F G P Q).FullSubcategory ≌
      CategoricalPullback (ObjectProperty.lift S (P.ι ⋙ F) (fun a ↦ hF a.1 a.2))
        (ObjectProperty.lift S (Q.ι ⋙ G) (fun c ↦ hG c.1 c.2)) :=
  .mk (categoricalPullbackFullSubcategoryFunctor F G P Q S hF hG)
    (categoricalPullbackFullSubcategoryInverse F G P Q S hF hG) (Iso.refl _) (Iso.refl _)

/-- The equivalence of
`CategoryTheory.Limits.categoricalPullbackFullSubcategoryEquiv` is compatible with the first
projection: forgetting the property after projecting is projecting after forgetting. -/
lemma categoricalPullbackFullSubcategoryEquiv_functor_comp_π₁ :
    (categoricalPullbackFullSubcategoryEquiv F G P Q S hF hG).functor ⋙
        CategoricalPullback.π₁ _ _ ⋙ P.ι =
      (categoricalPullbackProperty F G P Q).ι ⋙
        CategoricalPullback.π₁ F G :=
  rfl

/-- The equivalence of
`CategoryTheory.Limits.categoricalPullbackFullSubcategoryEquiv` is compatible with the second
projection: forgetting the property after projecting is projecting after forgetting. -/
lemma categoricalPullbackFullSubcategoryEquiv_functor_comp_π₂ :
    (categoricalPullbackFullSubcategoryEquiv F G P Q S hF hG).functor ⋙
        CategoricalPullback.π₂ _ _ ⋙ Q.ι =
      (categoricalPullbackProperty F G P Q).ι ⋙
        CategoricalPullback.π₂ F G :=
  rfl

end FullSubcategoryPullback

end CategoryTheory.Limits

namespace ModuleGlueing

universe u

open scoped ChangeOfRings

section Precompose

variable {R R₀ R₁ R₂ R₃ : Type u}
  [CommRing R] [CommRing R₀] [CommRing R₁] [CommRing R₂] [CommRing R₃]

/-- **Transporting an extension of scalars along an equality of ring maps fixes the
generators.** -/
theorem extendScalars_eqToIso_hom_app_one_tmul {φ ψ : R₀ →+* R₃} (h : φ = ψ)
    (M : ModuleCat.{u} R₀) (x : M) :
    (eqToIso (congrArg ModuleCat.extendScalars h)).hom.app M ((1 : R₃) ⊗ₜ[R₀, φ] x) =
      (1 : R₃) ⊗ₜ[R₀, ψ] x := by
  cases h
  rfl

/-- **The structural isomorphism of `ModuleGlueing.extensionOfScalarsToPullback` on the
generators.** Read through the two identifications of the extensions of scalars along the two
composites to the lower-right corner, it is the transport along `comm`, so on the generator
`1 ⊗ x` the two iterated generators `1 ⊗ (1 ⊗ x)` correspond. -/
theorem extensionOfScalarsToPullback_iso_hom_one_tmul
    (toB : R₀ →+* R₁) (toA' : R₀ →+* R₂) (BtoA : R₁ →+* R₃) (A'toA : R₂ →+* R₃)
    (comm : BtoA.comp toB = A'toA.comp toA') (M : ModuleCat.{u} R₀) (x : M) :
    ((extensionOfScalarsToPullback.{u, u, u, u, u} toB toA' BtoA A'toA comm).obj M).iso.hom
        ((extendScalarsComp.{u, u, u, u} toB BtoA).hom.app M
          ((1 : R₃) ⊗ₜ[R₀, BtoA.comp toB] x)) =
      (extendScalarsComp.{u, u, u, u} toA' A'toA).hom.app M
        ((1 : R₃) ⊗ₜ[R₀, A'toA.comp toA'] x) := by
  have hinv : (extendScalarsComp.{u, u, u, u} toB BtoA).inv.app M
      ((extendScalarsComp.{u, u, u, u} toB BtoA).hom.app M
        ((1 : R₃) ⊗ₜ[R₀, BtoA.comp toB] x)) = (1 : R₃) ⊗ₜ[R₀, BtoA.comp toB] x :=
    ((extendScalarsComp.{u, u, u, u} toB BtoA).app M).toLinearEquiv.symm_apply_apply _
  show ((extendScalarsComp.{u, u, u, u} toB BtoA).inv.app M ≫
      (eqToIso (congrArg ModuleCat.extendScalars comm)).hom.app M ≫
      (extendScalarsComp.{u, u, u, u} toA' A'toA).hom.app M)
      ((extendScalarsComp.{u, u, u, u} toB BtoA).hom.app M
        ((1 : R₃) ⊗ₜ[R₀, BtoA.comp toB] x)) = _
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, hinv]
  exact congrArg _ (extendScalars_eqToIso_hom_app_one_tmul comm M x)

/-- **The compatibility over the lower-right corner, from the generators.** Two identifications
of the two extensions of scalars of `N` whose images over the lower-right corner agree on the
generators form a morphism in the categorical pullback out of
`ModuleGlueing.extensionOfScalarsToPullback`. -/
theorem extensionOfScalarsToPullback_w
    (toB : R₀ →+* R₁) (toA' : R₀ →+* R₂) (BtoA : R₁ →+* R₃) (A'toA : R₂ →+* R₃)
    (comm : BtoA.comp toB = A'toA.comp toA') (N : ModuleCat.{u} R₀)
    (Y₁ : ModuleCat.{u} R₁) (Y₂ : ModuleCat.{u} R₂)
    (e : (ModuleCat.extendScalars.{u, u, u} BtoA).obj Y₁ ≅
      (ModuleCat.extendScalars.{u, u, u} A'toA).obj Y₂)
    (a : (ModuleCat.extendScalars.{u, u, u} toB).obj N ≅ Y₁)
    (b : (ModuleCat.extendScalars.{u, u, u} toA').obj N ≅ Y₂)
    (hab : ∀ n : N, e.hom ((1 : R₃) ⊗ₜ[R₁, BtoA] a.hom ((1 : R₁) ⊗ₜ[R₀, toB] n)) =
      (1 : R₃) ⊗ₜ[R₂, A'toA] b.hom ((1 : R₂) ⊗ₜ[R₀, toA'] n)) :
    (ModuleCat.extendScalars.{u, u, u} BtoA).map a.hom ≫ e.hom =
      ((extensionOfScalarsToPullback.{u, u, u, u, u} toB toA' BtoA A'toA comm).obj N).iso.hom ≫
        (ModuleCat.extendScalars.{u, u, u} A'toA).map b.hom := by
  obtain ⟨i, hfst, hsnd⟩ :=
    Deformation.Examples.exists_extensionOfScalarsToPullback_iso toB toA' BtoA A'toA comm N
      { fst := Y₁, snd := Y₂, iso := e } a b hab
  rw [← hfst, ← hsnd]
  exact i.hom.w

/-- **The comparison into the categorical pullback only depends on the two maps out of the
upper-left corner.** -/
theorem extensionOfScalarsToPullback_congr {toB toB' : R₀ →+* R₁} {toA' toA'' : R₀ →+* R₂}
    (BtoA : R₁ →+* R₃) (A'toA : R₂ →+* R₃) (h₁ : toB = toB') (h₂ : toA' = toA'')
    (comm : BtoA.comp toB = A'toA.comp toA') (comm' : BtoA.comp toB' = A'toA.comp toA'') :
    extensionOfScalarsToPullback.{u, u, u, u, u} toB toA' BtoA A'toA comm =
      extensionOfScalarsToPullback.{u, u, u, u, u} toB' toA'' BtoA A'toA comm' := by
  subst h₁ h₂
  rfl

/-- The value at a single module of
`ModuleGlueing.extensionOfScalarsToPullbackPrecomp`: the two identifications of the extensions of
scalars along the two composites, together with their compatibility over the lower-right
corner. -/
noncomputable def extensionOfScalarsToPullbackPrecompApp
    (σ : R →+* R₀) (toB : R₀ →+* R₁) (toA' : R₀ →+* R₂) (BtoA : R₁ →+* R₃) (A'toA : R₂ →+* R₃)
    (comm : BtoA.comp toB = A'toA.comp toA')
    (comm' : BtoA.comp (toB.comp σ) = A'toA.comp (toA'.comp σ)) (N : ModuleCat.{u} R) :
    (extensionOfScalarsToPullback.{u, u, u, u, u} (toB.comp σ) (toA'.comp σ) BtoA A'toA
        comm').obj N ≅
      (ModuleCat.extendScalars.{u, u, u} σ ⋙
        extensionOfScalarsToPullback.{u, u, u, u, u} toB toA' BtoA A'toA comm).obj N :=
  CategoricalPullback.mkIso
    ((extendScalarsComp.{u, u, u, u} σ toB).app N)
    ((extendScalarsComp.{u, u, u, u} σ toA').app N)
    (extensionOfScalarsToPullback_w (toB.comp σ) (toA'.comp σ) BtoA A'toA comm' N
      ((ModuleCat.extendScalars.{u, u, u} toB).obj
        ((ModuleCat.extendScalars.{u, u, u} σ).obj N))
      ((ModuleCat.extendScalars.{u, u, u} toA').obj
        ((ModuleCat.extendScalars.{u, u, u} σ).obj N))
      ((extensionOfScalarsToPullback.{u, u, u, u, u} toB toA' BtoA A'toA comm).obj
        ((ModuleCat.extendScalars.{u, u, u} σ).obj N)).iso
      ((extendScalarsComp.{u, u, u, u} σ toB).app N)
      ((extendScalarsComp.{u, u, u, u} σ toA').app N)
      (fun n ↦ by
        have key := extensionOfScalarsToPullback_iso_hom_one_tmul toB toA' BtoA A'toA comm
          ((ModuleCat.extendScalars.{u, u, u} σ).obj N) ((1 : R₀) ⊗ₜ[R, σ] n)
        rw [extendScalarsComp_hom_app_one_tmul.{u, u, u, u} toB BtoA
            ((ModuleCat.extendScalars.{u, u, u} σ).obj N) ((1 : R₀) ⊗ₜ[R, σ] n),
          extendScalarsComp_hom_app_one_tmul.{u, u, u, u} toA' A'toA
            ((ModuleCat.extendScalars.{u, u, u} σ).obj N) ((1 : R₀) ⊗ₜ[R, σ] n)] at key
        simp only [Iso.app_hom]
        rw [extendScalarsComp_hom_app_one_tmul.{u, u, u, u} σ toB N n,
          extendScalarsComp_hom_app_one_tmul.{u, u, u, u} σ toA' N n]
        exact key))

/-- **Extension of scalars into a categorical pullback is compatible with precomposition.** The
comparison for the square whose two maps out of the upper-left corner have been precomposed with
`σ` is extension of scalars along `σ` followed by the original comparison. -/
noncomputable def extensionOfScalarsToPullbackPrecomp
    (σ : R →+* R₀) (toB : R₀ →+* R₁) (toA' : R₀ →+* R₂) (BtoA : R₁ →+* R₃) (A'toA : R₂ →+* R₃)
    (comm : BtoA.comp toB = A'toA.comp toA')
    (comm' : BtoA.comp (toB.comp σ) = A'toA.comp (toA'.comp σ)) :
    extensionOfScalarsToPullback.{u, u, u, u, u} (toB.comp σ) (toA'.comp σ) BtoA A'toA comm' ≅
      ModuleCat.extendScalars.{u, u, u} σ ⋙
        extensionOfScalarsToPullback.{u, u, u, u, u} toB toA' BtoA A'toA comm :=
  NatIso.ofComponents
    (extensionOfScalarsToPullbackPrecompApp σ toB toA' BtoA A'toA comm comm')
    (fun φ ↦ CategoricalPullback.hom_ext
      ((extendScalarsComp.{u, u, u, u} σ toB).hom.naturality φ)
      ((extendScalarsComp.{u, u, u, u} σ toA').hom.naturality φ))

end Precompose

end ModuleGlueing

namespace AlgebraicGeometry

universe u

/-- **Finite projectivity only depends on the isomorphism class of a module.** -/
instance finiteProjectiveProperty_isClosedUnderIsomorphisms (R : CommRingCat.{u}) :
    (finiteProjectiveProperty R).IsClosedUnderIsomorphisms where
  of_iso e h := by
    obtain ⟨_, _⟩ := h
    exact ⟨Module.Finite.equiv e.toLinearEquiv, Module.Projective.of_equiv' e.toLinearEquiv⟩

section RingEquiv

variable {R S : CommRingCat.{u}}

/-- **Extension of scalars along an isomorphism of rings is an equivalence of module
categories**, with inverse the extension of scalars along the inverse isomorphism. -/
noncomputable def moduleCatEquivalenceOfRingEquiv (e : R ≃+* S) :
    ModuleCat.{u} R ≌ ModuleCat.{u} S :=
  .mk (ModuleCat.extendScalars.{u, u, u} e.toRingHom)
    (ModuleCat.extendScalars.{u, u, u} e.symm.toRingHom)
    ((ModuleCat.extendScalarsId R).symm ≪≫
      eqToIso (congrArg ModuleCat.extendScalars e.symm_toRingHom_comp_toRingHom.symm) ≪≫
      ModuleCat.extendScalarsComp e.toRingHom e.symm.toRingHom)
    ((ModuleCat.extendScalarsComp e.symm.toRingHom e.toRingHom).symm ≪≫
      eqToIso (congrArg ModuleCat.extendScalars e.toRingHom_comp_symm_toRingHom) ≪≫
      ModuleCat.extendScalarsId S)

/-- **An isomorphism of rings induces an equivalence of their categories of finite projective
modules**, by extension of scalars. -/
noncomputable def FinProj.equivalenceOfRingEquiv (e : R ≃+* S) :
    FinProj R ≌ FinProj S :=
  (moduleCatEquivalenceOfRingEquiv e).congrFullSubcategory
    (P := finiteProjectiveProperty R) (Q := finiteProjectiveProperty S) (by
      funext M
      refine propext ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · exact ObjectProperty.prop_of_iso _
          ((moduleCatEquivalenceOfRingEquiv e).unitIso.app M).symm
          (finiteProjectiveProperty_extendScalars (CommRingCat.ofHom e.symm.toRingHom) ⟨_, h⟩)
      · exact finiteProjectiveProperty_extendScalars (CommRingCat.ofHom e.toRingHom) ⟨M, h⟩)

/-- The equivalence `AlgebraicGeometry.FinProj.equivalenceOfRingEquiv` is extension of scalars:
composing its functor with the inclusion of the full subcategory of finite projective modules
recovers `ModuleCat.extendScalars`. -/
lemma FinProj.equivalenceOfRingEquiv_functor_comp_ι (e : R ≃+* S) :
    (FinProj.equivalenceOfRingEquiv e).functor ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙ ModuleCat.extendScalars.{u, u, u} e.toRingHom :=
  rfl

end RingEquiv

section Composition

variable {R S T : CommRingCat.{u}}

namespace FinProj

/-- **Extension of scalars on finite projective modules is compatible with composition**: the
extension along `φ ≫ ψ` is the extension along `φ` followed by the extension along `ψ`. This is
`ModuleGlueing.extendScalarsComp` restricted to the full subcategories of finite projective
modules. -/
noncomputable def extendScalarsComp (φ : R ⟶ S) (ψ : S ⟶ T) :
    extendScalars (φ ≫ ψ) ≅ extendScalars φ ⋙ extendScalars ψ :=
  NatIso.ofComponents
    (fun L ↦ ObjectProperty.isoMk _
      ((ModuleGlueing.extendScalarsComp.{u, u, u, u} φ.hom ψ.hom).app L.obj))
    (fun {L L'} g ↦ by
      apply (ObjectProperty.ι _).map_injective
      exact (ModuleGlueing.extendScalarsComp.{u, u, u, u} φ.hom ψ.hom).hom.naturality g.hom)

/-- The comparison isomorphism of `AlgebraicGeometry.FinProj.extendScalarsComp` is the ambient
one of `ModuleGlueing.extendScalarsComp` on underlying modules. -/
@[simp]
lemma extendScalarsComp_hom_app_hom (φ : R ⟶ S) (ψ : S ⟶ T) (L : FinProj R) :
    ((extendScalarsComp φ ψ).hom.app L).hom =
      (ModuleGlueing.extendScalarsComp.{u, u, u, u} φ.hom ψ.hom).hom.app L.obj :=
  rfl

/-- **Equal ring maps induce the same extension of scalars on finite projective modules.** -/
noncomputable def extendScalarsCongr {φ ψ : R ⟶ S} (h : φ = ψ) :
    extendScalars φ ≅ extendScalars ψ :=
  NatIso.ofComponents
    (fun L ↦ ObjectProperty.isoMk _
      ((eqToIso (congrArg (fun α : R ⟶ S ↦ ModuleCat.extendScalars.{u, u, u} α.hom) h)).app
        L.obj))
    (fun {L L'} g ↦ by
      subst h
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The isomorphism of `AlgebraicGeometry.FinProj.extendScalarsCongr` is the transport of
`ModuleCat.extendScalars` along the same equality, on underlying modules. -/
@[simp]
lemma extendScalarsCongr_hom_app_hom {φ ψ : R ⟶ S} (h : φ = ψ) (L : FinProj R) :
    ((extendScalarsCongr h).hom.app L).hom =
      (eqToIso (congrArg (fun α : R ⟶ S ↦ ModuleCat.extendScalars.{u, u, u} α.hom) h)).hom.app
        L.obj :=
  rfl

/-- `AlgebraicGeometry.FinProj.extendScalarsCongr` is the transport of
`AlgebraicGeometry.FinProj.extendScalars` along the equality of ring maps. -/
lemma extendScalarsCongr_eq_eqToIso {φ ψ : R ⟶ S} (h : φ = ψ) :
    extendScalarsCongr h = eqToIso (congrArg extendScalars h) := by
  subst h
  rfl

end FinProj

end Composition

end AlgebraicGeometry

namespace MilnorPatching.OneGeneratorFrobenius

open AlgebraicGeometry ModuleGlueing

universe u

/-- **The first projection of the Milnor square's fibre product is the reduction to `A ⧸ J`.**
Read through the identification `MilnorPatching.OneGeneratorFrobenius.fibreProductEquiv` of the
fourth corner with `A ⧸ (J ⊓ fA)`, the first projection of `A ⧸ J ×_{A ⧸ (J + fA)} A ⧸ fA` is
the quotient map `A ⧸ (J ⊓ fA) → A ⧸ J`. -/
theorem pullbackCone_fst_comp_fibreProductEquiv {A : Type u} [CommRing A] (f : A) (J : Ideal A) :
    ((situation f J).pullbackCone.fst.hom).comp (fibreProductEquiv f J).toRingHom =
      Ideal.Quotient.factor (inf_le_left : J ⊓ Ideal.span {f} ≤ J) :=
  RingHom.ext fun z ↦ fibreProductEquiv_fst f J z

/-- **The second projection of the Milnor square's fibre product is the reduction to `A ⧸ fA`.**
Read through the identification `MilnorPatching.OneGeneratorFrobenius.fibreProductEquiv` of the
fourth corner with `A ⧸ (J ⊓ fA)`, the second projection of
`A ⧸ J ×_{A ⧸ (J + fA)} A ⧸ fA` is the quotient map `A ⧸ (J ⊓ fA) → A ⧸ fA`. -/
theorem pullbackCone_snd_comp_fibreProductEquiv {A : Type u} [CommRing A] (f : A) (J : Ideal A) :
    ((situation f J).pullbackCone.snd.hom).comp (fibreProductEquiv f J).toRingHom =
      Ideal.Quotient.factor (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f}) :=
  RingHom.ext fun z ↦ fibreProductEquiv_snd f J z

/-- Extension of scalars along `toBase` preserves finite projectivity. -/
private theorem finiteProjectiveProperty_toBase {A : Type u} [CommRing A] (f : A) (J : Ideal A) :
    ∀ a, finiteProjectiveProperty (CommRingCat.of (A ⧸ J)) a →
      finiteProjectiveProperty (CommRingCat.of (A ⧸ (J ⊔ Ideal.span {f})))
        ((ModuleCat.extendScalars.{u, u, u} (CommRingCat.ofHom (toBase f J)).hom).obj a) :=
  fun a ha ↦ finiteProjectiveProperty_extendScalars (CommRingCat.ofHom (toBase f J)) ⟨a, ha⟩

/-- Extension of scalars along `surjection` preserves finite projectivity. -/
private theorem finiteProjectiveProperty_surjection {A : Type u} [CommRing A] (f : A)
    (J : Ideal A) :
    ∀ a, finiteProjectiveProperty (CommRingCat.of (A ⧸ Ideal.span {f})) a →
      finiteProjectiveProperty (CommRingCat.of (A ⧸ (J ⊔ Ideal.span {f})))
        ((ModuleCat.extendScalars.{u, u, u} (CommRingCat.ofHom (surjection f J)).hom).obj a) :=
  fun a ha ↦ finiteProjectiveProperty_extendScalars (CommRingCat.ofHom (surjection f J)) ⟨a, ha⟩

/-- A functor of finite projective modules which agrees, on underlying modules, with extension of
scalars along `e` and then along `p` is extension of scalars along their composite `q`. -/
private theorem nonempty_iso_extendScalars_of_comp {R S X : CommRingCat.{u}} (e : R ≃+* S)
    (p : S →+* X) (q : R →+* X) (h : p.comp e.toRingHom = q) (F : FinProj R ⥤ FinProj X)
    (i : F ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ ModuleCat.extendScalars.{u, u, u} e.toRingHom ⋙
        ModuleCat.extendScalars.{u, u, u} p) :
    Nonempty (F ≅ FinProj.extendScalars (CommRingCat.ofHom q)) :=
  ⟨((finiteProjectiveProperty X).fullyFaithfulι.whiskeringRight (FinProj R)).preimageIso
    (i ≪≫ Functor.isoWhiskerLeft (ObjectProperty.ι _) (ModuleCat.extendScalarsComp _ _).symm ≪≫
      eqToIso (congrArg (fun φ ↦ ObjectProperty.ι (finiteProjectiveProperty R) ⋙
        ModuleCat.extendScalars.{u, u, u} φ) h))⟩

/-- **Milnor patching for the square of Stacks Example 0EVG.** Extension of scalars identifies
the finite projective modules over `A ⧸ (J ∩ fA)` with the compatible pairs over `A ⧸ J` and
`A ⧸ fA`. The two natural isomorphisms record that the equivalence is the canonical one: its two
components are extension of scalars along the two reduction maps out of `A ⧸ (J ∩ fA)`. -/
theorem exists_oneGeneratorFinProjEquivalence (A : Type u) [CommRing A] (f : A) (J : Ideal A) :
    ∃ q : FinProj (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f}))) ≌
        CategoricalPullback
          (FinProj.extendScalars (CommRingCat.ofHom (toBase f J)))
          (FinProj.extendScalars (CommRingCat.ofHom (surjection f J))),
      Nonempty (q.functor ⋙ CategoricalPullback.π₁ _ _ ≅
          FinProj.extendScalars (CommRingCat.ofHom
            (Ideal.Quotient.factor (inf_le_left : J ⊓ Ideal.span {f} ≤ J)))) ∧
        Nonempty (q.functor ⋙ CategoricalPullback.π₂ _ _ ≅
          FinProj.extendScalars (CommRingCat.ofHom
            (Ideal.Quotient.factor
              (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f})))) := by
  obtain ⟨q₀, ⟨iso₀⟩⟩ := MilnorPatching.finiteProjectiveModulesEquivalenceOverFibreProduct
    (toBase f J) (surjection f J) (Ideal.map (Ideal.Quotient.mk (Ideal.span {f})) J)
    (situation f J)
  let c := categoricalPullbackFullSubcategoryEquiv
    (ModuleCat.extendScalars.{u, u, u} (toBase f J))
    (ModuleCat.extendScalars.{u, u, u} (surjection f J))
    (finiteProjectiveProperty (CommRingCat.of (A ⧸ J)))
    (finiteProjectiveProperty (CommRingCat.of (A ⧸ Ideal.span {f})))
    (finiteProjectiveProperty (CommRingCat.of (A ⧸ (J ⊔ Ideal.span {f}))))
    (finiteProjectiveProperty_toBase f J) (finiteProjectiveProperty_surjection f J)
  let t := FinProj.equivalenceOfRingEquiv
    (R := CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))
    (S := CommRingCat.of ((situation f J).fibreProduct)) (fibreProductEquiv f J)
  exact ⟨t.trans (q₀.trans c),
    nonempty_iso_extendScalars_of_comp _ _ _ (pullbackCone_fst_comp_fibreProductEquiv f J) _
      (Functor.isoWhiskerLeft t.functor (Functor.isoWhiskerRight iso₀.symm
        (CategoricalPullback.π₁ _ _))),
    nonempty_iso_extendScalars_of_comp _ _ _ (pullbackCone_snd_comp_fibreProductEquiv f J) _
      (Functor.isoWhiskerLeft t.functor (Functor.isoWhiskerRight iso₀.symm
        (CategoricalPullback.π₂ _ _)))⟩

/-- **The two reductions out of `A ⧸ (J ∩ fA)` agree over `A ⧸ (J + fA)`.** Both composites are
the quotient map `A ⧸ (J ∩ fA) → A ⧸ (J + fA)`. -/
theorem toBase_comp_factor_eq {A : Type u} [CommRing A] (f : A) (J : Ideal A) :
    (toBase f J).comp (Ideal.Quotient.factor (inf_le_left : J ⊓ Ideal.span {f} ≤ J)) =
      (surjection f J).comp (Ideal.Quotient.factor
        (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f})) := by
  ext
  simp

/-- `MilnorPatching.OneGeneratorFrobenius.toBase_comp_factor_eq` read for the underlying
homomorphisms of the morphisms of `CommRingCat`. -/
theorem ofHom_toBase_comp_factor_eq {A : Type u} [CommRing A] (f : A) (J : Ideal A) :
    (CommRingCat.ofHom (toBase f J)).hom.comp
        (CommRingCat.ofHom
          (Ideal.Quotient.factor (inf_le_left : J ⊓ Ideal.span {f} ≤ J))).hom =
      (CommRingCat.ofHom (surjection f J)).hom.comp
        (CommRingCat.ofHom (Ideal.Quotient.factor
          (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f}))).hom :=
  toBase_comp_factor_eq f J

/-- The comparison into the categorical pullback for the square of Stacks Example 0EVG, at the
level of *all* modules: extension of scalars along the two reductions out of `A ⧸ (J ∩ fA)`,
together with the canonical identification of the two further extensions to `A ⧸ (J + fA)`. -/
noncomputable abbrev moduleComparison (A : Type u) [CommRing A] (f : A) (J : Ideal A) :
    ModuleCat.{u} (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f}))) ⥤
      CategoricalPullback
        (ModuleCat.extendScalars.{u, u, u} (CommRingCat.ofHom (toBase f J)).hom)
        (ModuleCat.extendScalars.{u, u, u} (CommRingCat.ofHom (surjection f J)).hom) :=
  ModuleGlueing.extensionOfScalarsToPullback.{u, u, u, u, u}
    (CommRingCat.ofHom (Ideal.Quotient.factor (inf_le_left : J ⊓ Ideal.span {f} ≤ J))).hom
    (CommRingCat.ofHom (Ideal.Quotient.factor
      (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f}))).hom
    (CommRingCat.ofHom (toBase f J)).hom (CommRingCat.ofHom (surjection f J)).hom
    (ofHom_toBase_comp_factor_eq f J)

/-- The property of a compatible pair over `A ⧸ J` and `A ⧸ fA` that both of its components are
finite projective. -/
abbrev finProjPairProperty (A : Type u) [CommRing A] (f : A) (J : Ideal A) :
    ObjectProperty (CategoricalPullback
      (ModuleCat.extendScalars.{u, u, u} (CommRingCat.ofHom (toBase f J)).hom)
      (ModuleCat.extendScalars.{u, u, u} (CommRingCat.ofHom (surjection f J)).hom)) :=
  categoricalPullbackProperty _ _
    (finiteProjectiveProperty (CommRingCat.of (A ⧸ J)))
    (finiteProjectiveProperty (CommRingCat.of (A ⧸ Ideal.span {f})))

/-- **The two descriptions of a compatible pair of finite projective modules agree.** A pair of
finite projective modules over `A ⧸ J` and over `A ⧸ fA` together with an isomorphism of their
extensions to `A ⧸ (J + fA)` is the same thing whether the isomorphism is taken between all
`A ⧸ (J + fA)`-modules or in `AlgebraicGeometry.FinProj`. This is
`CategoryTheory.Limits.categoricalPullbackFullSubcategoryEquiv` for the square of Stacks Example
0EVG. -/
noncomputable def finProjPairEquiv (A : Type u) [CommRing A] (f : A) (J : Ideal A) :
    (finProjPairProperty A f J).FullSubcategory ≌
      CategoricalPullback
        (FinProj.extendScalars (CommRingCat.ofHom (toBase f J)))
        (FinProj.extendScalars (CommRingCat.ofHom (surjection f J))) :=
  categoricalPullbackFullSubcategoryEquiv
    (ModuleCat.extendScalars.{u, u, u} (CommRingCat.ofHom (toBase f J)).hom)
    (ModuleCat.extendScalars.{u, u, u} (CommRingCat.ofHom (surjection f J)).hom)
    (finiteProjectiveProperty (CommRingCat.of (A ⧸ J)))
    (finiteProjectiveProperty (CommRingCat.of (A ⧸ Ideal.span {f})))
    (finiteProjectiveProperty (CommRingCat.of (A ⧸ (J ⊔ Ideal.span {f}))))
    (fun a ha ↦ finiteProjectiveProperty_extendScalars
      (CommRingCat.ofHom (toBase f J)) ⟨a, ha⟩)
    (fun a ha ↦ finiteProjectiveProperty_extendScalars
      (CommRingCat.ofHom (surjection f J)) ⟨a, ha⟩)

/-- The canonical functor from finite projective `A ⧸ (J ∩ fA)`-modules to the compatible pairs
over `A ⧸ J` and `A ⧸ fA`: extension of scalars along the two quotient maps, together with the
canonical identification of the two further extensions to `A ⧸ (J + fA)`. It is the restriction
of `MilnorPatching.OneGeneratorFrobenius.moduleComparison` to the full subcategories of finite
projective modules. -/
noncomputable def finProjComparison (A : Type u) [CommRing A] (f : A) (J : Ideal A) :
    FinProj (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f}))) ⥤
      CategoricalPullback
        (FinProj.extendScalars (CommRingCat.ofHom (toBase f J)))
        (FinProj.extendScalars (CommRingCat.ofHom (surjection f J))) :=
  ObjectProperty.lift (finProjPairProperty A f J)
      (ObjectProperty.ι (finiteProjectiveProperty (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))) ⋙
        moduleComparison A f J)
      (fun L ↦ ⟨finiteProjectiveProperty_extendScalars
          (CommRingCat.ofHom
            (Ideal.Quotient.factor (inf_le_left : J ⊓ Ideal.span {f} ≤ J))) L,
        finiteProjectiveProperty_extendScalars
          (CommRingCat.ofHom (Ideal.Quotient.factor
            (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f}))) L⟩) ⋙
    (finProjPairEquiv A f J).functor

/-- The first component of the canonical comparison
`MilnorPatching.OneGeneratorFrobenius.finProjComparison` is extension of scalars along the
reduction to `A ⧸ J`. -/
lemma finProjComparison_comp_π₁ (A : Type u) [CommRing A] (f : A) (J : Ideal A) :
    finProjComparison A f J ⋙ CategoricalPullback.π₁ _ _ =
      FinProj.extendScalars (CommRingCat.ofHom
        (Ideal.Quotient.factor (inf_le_left : J ⊓ Ideal.span {f} ≤ J))) :=
  rfl

/-- The second component of the canonical comparison
`MilnorPatching.OneGeneratorFrobenius.finProjComparison` is extension of scalars along the
reduction to `A ⧸ fA`. -/
lemma finProjComparison_comp_π₂ (A : Type u) [CommRing A] (f : A) (J : Ideal A) :
    finProjComparison A f J ⋙ CategoricalPullback.π₂ _ _ =
      FinProj.extendScalars (CommRingCat.ofHom
        (Ideal.Quotient.factor (inf_le_right : J ⊓ Ideal.span {f} ≤ Ideal.span {f}))) :=
  rfl

/-- **The structural isomorphism of the canonical comparison is the canonical identification of
the two extensions of scalars to `A ⧸ (J + fA)`**: on underlying modules it is the one carried by
`ModuleGlueing.extensionOfScalarsToPullback`. -/
lemma finProjComparison_obj_iso_hom_hom (A : Type u) [CommRing A] (f : A) (J : Ideal A)
    (L : FinProj (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))) :
    (((finProjComparison A f J).obj L).iso.hom).hom =
      (((moduleComparison A f J).obj L.obj).iso).hom :=
  categoricalPullbackFullSubcategoryFunctor_obj_iso_hom_hom _ _ _ _ _
    (finiteProjectiveProperty_toBase f J) (finiteProjectiveProperty_surjection f J) _

/-- **Stacks Tag 0D2J for the square of Stacks Example 0EVG, with the canonical comparison.**
Extension of scalars is an equivalence from the finite projective `A ⧸ (J ∩ fA)`-modules onto the
compatible pairs over `A ⧸ J` and `A ⧸ fA`, and the equivalence *is* the canonical comparison
functor `MilnorPatching.OneGeneratorFrobenius.finProjComparison`. In particular the structural
isomorphism carried by the compatible pair attached to a module is the canonical identification
of its two further extensions to `A ⧸ (J + fA)`. -/
theorem exists_oneGeneratorFinProjEquivalence' (A : Type u) [CommRing A] (f : A) (J : Ideal A) :
    ∃ q : FinProj (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f}))) ≌
        CategoricalPullback
          (FinProj.extendScalars (CommRingCat.ofHom (toBase f J)))
          (FinProj.extendScalars (CommRingCat.ofHom (surjection f J))),
      Nonempty (q.functor ≅ finProjComparison A f J) := by
  obtain ⟨q₀, ⟨iso₀⟩⟩ := MilnorPatching.finiteProjectiveModulesEquivalenceOverFibreProduct
    (toBase f J) (surjection f J) (Ideal.map (Ideal.Quotient.mk (Ideal.span {f})) J)
    (situation f J)
  let t := FinProj.equivalenceOfRingEquiv
    (R := CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))
    (S := CommRingCat.of ((situation f J).fibreProduct)) (fibreProductEquiv f J)
  have comm : (toBase f J).comp (situation f J).pullbackCone.fst.hom =
      (surjection f J).comp (situation f J).pullbackCone.snd.hom :=
    congrArg CommRingCat.Hom.hom (situation f J).pullbackCone.condition
  have comm' : (toBase f J).comp
        ((situation f J).pullbackCone.fst.hom.comp (fibreProductEquiv f J).toRingHom) =
      (surjection f J).comp
        ((situation f J).pullbackCone.snd.hom.comp (fibreProductEquiv f J).toRingHom) :=
    RingHom.ext fun z ↦ DFunLike.congr_fun comm (fibreProductEquiv f J z)
  have hE := ModuleGlueing.extensionOfScalarsToPullback_congr (toBase f J) (surjection f J)
    (pullbackCone_fst_comp_fibreProductEquiv f J) (pullbackCone_snd_comp_fibreProductEquiv f J)
    comm' (toBase_comp_factor_eq f J)
  let ρ := ModuleGlueing.extensionOfScalarsToPullbackPrecomp
    (fibreProductEquiv f J).toRingHom
    (situation f J).pullbackCone.fst.hom (situation f J).pullbackCone.snd.hom
    (toBase f J) (surjection f J) comm comm'
  refine ⟨(t.trans q₀).trans (finProjPairEquiv A f J), ⟨?_⟩⟩
  refine Functor.isoWhiskerRight ?_ (finProjPairEquiv A f J).functor
  refine ((finProjPairProperty A f J).fullyFaithfulι.whiskeringRight
    (FinProj (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f}))))).preimageIso ?_
  exact Functor.isoWhiskerLeft t.functor iso₀.symm ≪≫
    (Functor.isoWhiskerLeft
      (ObjectProperty.ι (finiteProjectiveProperty
        (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f})))))
      (eqToIso hE.symm ≪≫ ρ)).symm

/-- **Essential surjectivity of the canonical comparison for the square of Stacks Example
0EVG.** Every compatible pair consisting of a finite projective `A ⧸ J`-module and a finite
projective `A ⧸ fA`-module is the canonical comparison of a finite projective
`A ⧸ (J ∩ fA)`-module, by an isomorphism *in the categorical pullback*: the two reduction
isomorphisms it provides are compatible over `A ⧸ (J + fA)`. -/
theorem exists_oneGeneratorFinProj_obj (A : Type u) [CommRing A] (f : A) (J : Ideal A)
    (Y : CategoricalPullback
      (FinProj.extendScalars (CommRingCat.ofHom (toBase f J)))
      (FinProj.extendScalars (CommRingCat.ofHom (surjection f J)))) :
    ∃ L : FinProj (CommRingCat.of (A ⧸ (J ⊓ Ideal.span {f}))),
      Nonempty ((finProjComparison A f J).obj L ≅ Y) := by
  obtain ⟨q, ⟨e⟩⟩ := exists_oneGeneratorFinProjEquivalence' A f J
  exact ⟨q.inverse.obj Y, ⟨(e.app (q.inverse.obj Y)).symm ≪≫ q.counitIso.app Y⟩⟩

end MilnorPatching.OneGeneratorFrobenius

end
