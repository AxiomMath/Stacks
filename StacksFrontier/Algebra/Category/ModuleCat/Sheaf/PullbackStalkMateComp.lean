module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMate

/-!
# The stalk formula for a pullback is compatible with composition

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes and `x` a point of `X`. The stalk
formula `Stacks.ModuleSkyscraper.pullbackStalkIso`,

`(f^*N)_x ≅ 𝒪_{X,x} ⊗_{𝒪_{Y,f x}} N_{f x}`,

can be applied twice — along `g` at `f x` and then along `f` at `x` — or once, along `f ≫ g`.
The two agree, through the composition isomorphisms
`AlgebraicGeometry.Scheme.Modules.pullbackComp` for pullback and `extendScalarsStalkComp` for
extension of scalars along the germ maps.

## Main definitions

* `Stacks.ModuleSkyscraper.restrictScalarsStalkComp`: restriction of scalars along the germ map
  of `f ≫ g` at `x` is restriction along the germ map of `f` at `x` followed by restriction along
  the germ map of `g` at `f x`.
* `Stacks.ModuleSkyscraper.extendScalarsStalkComp`: the corresponding isomorphism for extension
  of scalars, induced on left adjoints.

## Main results

* `Stacks.CategoryTheory.mateEquiv_vComp_whiskerLeft_whiskerRight`: the mate of a vertical
  composite of squares, whiskered by comparisons of composite left adjoints, is the horizontal
  composite of the mates, whiskered by their conjugates.
* `Stacks.ModuleSkyscraper.pushStalkMap_comp_app`: the germ map of `f ≫ g` at `x` is the germ
  map of `g` at `f x` followed by the germ map of `f` at `x`.
* `Stacks.ModuleSkyscraper.pushStalkMap_comp`: the same, as an equality of 2-squares.
* `Stacks.ModuleSkyscraper.pullbackStalkIso_comp_app`: the stalk formula for `f ≫ g` at a module
  `N` is the stalk formula for `g` at `f x`, extended along the germ map of `f`, followed by the
  stalk formula for `f` at `x`, read through the two composition isomorphisms.
* `Stacks.ModuleSkyscraper.pullbackStalkIso_comp`: the same as an equality of 2-squares, and
  `Stacks.ModuleSkyscraper.pullbackStalkIso_comp_iso`, the same as an equality of isomorphisms of
  functors.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped CategoryTheory.TwoSquare

namespace Stacks.CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

/-- If the conjugate of `e.hom` across two adjunctions is `e'.hom`, then the conjugate of `e.inv`
across them in the other order is `e'.inv`. -/
theorem conjugateEquiv_inv_of_hom (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (e : L₂ ≅ L₁) (e' : R₁ ≅ R₂)
    (h : conjugateEquiv adj₁ adj₂ e.hom = e'.hom) :
    conjugateEquiv adj₂ adj₁ e.inv = e'.inv :=
  congrArg Iso.inv (Iso.ext (α := conjugateIsoEquiv adj₁ adj₂ e) (β := e') h)

end

section

variable {C₀ : Type u₁} {C₁ : Type u₂} {C₂ : Type u₃}
  {D₀ : Type u₄} {D₁ : Type u₅} {D₂ : Type u₆}
  [Category.{v₁} C₀] [Category.{v₂} C₁] [Category.{v₃} C₂]
  [Category.{v₄} D₀] [Category.{v₅} D₁] [Category.{v₆} D₂]
  {F₀₁ : C₀ ⥤ C₁} {G₁₀ : C₁ ⥤ C₀} {F₁₂ : C₁ ⥤ C₂} {G₂₁ : C₂ ⥤ C₁}
  {F₀₂ : C₀ ⥤ C₂} {G₂₀ : C₂ ⥤ C₀}
  {H₀₁ : D₀ ⥤ D₁} {K₁₀ : D₁ ⥤ D₀} {H₁₂ : D₁ ⥤ D₂} {K₂₁ : D₂ ⥤ D₁}
  {H₀₂ : D₀ ⥤ D₂} {K₂₀ : D₂ ⥤ D₀}
  {S₀ : C₀ ⥤ D₀} {S₁ : C₁ ⥤ D₁} {S₂ : C₂ ⥤ D₂}

/-- Suppose given a `2 × 2` grid of categories in which all four horizontal functors `F₀₁`, `F₁₂`,
`H₀₁`, `H₁₂` and the two "long" horizontal functors `F₀₂`, `H₀₂` are left adjoints, together with
comparisons `u : F₀₁ ⋙ F₁₂ ⟶ F₀₂` and `v : H₀₂ ⟶ H₀₁ ⋙ H₁₂`.

Then the mate of the vertical composite of two squares, whiskered by `u` and `v` so as to be a
square on `F₀₂` and `H₀₂`, is the horizontal composite of the two mates, whiskered by the
conjugates of `u` and `v`. -/
theorem mateEquiv_vComp_whiskerLeft_whiskerRight
    (a₀₁ : F₀₁ ⊣ G₁₀) (a₁₂ : F₁₂ ⊣ G₂₁) (a₀₂ : F₀₂ ⊣ G₂₀)
    (b₀₁ : H₀₁ ⊣ K₁₀) (b₁₂ : H₁₂ ⊣ K₂₁) (b₀₂ : H₀₂ ⊣ K₂₀)
    (α : TwoSquare S₀ F₀₁ H₀₁ S₁) (β : TwoSquare S₁ F₁₂ H₁₂ S₂)
    (u : F₀₁ ⋙ F₁₂ ⟶ F₀₂) (v : H₀₂ ⟶ H₀₁ ⋙ H₁₂) :
    mateEquiv a₀₂ b₀₂ (((α ≫ᵥ β).whiskerLeft u).whiskerRight v) =
      (((mateEquiv a₁₂ b₁₂ β) ≫ₕ (mateEquiv a₀₁ b₀₁ α)).whiskerTop
          (conjugateEquiv a₀₂ (a₀₁.comp a₁₂) u)).whiskerBottom
        (conjugateEquiv (b₀₁.comp b₁₂) b₀₂ v) := by
  rw [mateEquiv_conjugateEquiv_vcomp, conjugateEquiv_mateEquiv_vcomp, mateEquiv_hcomp]

end

section

variable {E₁ : Type u₁} {E₂ : Type u₂} {E₃ : Type u₃}
  {E₄ : Type u₄} {E₅ : Type u₅} {E₆ : Type u₆}
  [Category.{v₁} E₁] [Category.{v₂} E₂] [Category.{v₃} E₃]
  [Category.{v₄} E₄] [Category.{v₅} E₅] [Category.{v₆} E₆]
  {T : E₁ ⥤ E₂} {L : E₁ ⥤ E₃} {R : E₂ ⥤ E₄} {B : E₃ ⥤ E₄}
  {T' : E₂ ⥤ E₅} {R' : E₅ ⥤ E₆} {B' : E₄ ⥤ E₆} {T₀ : E₁ ⥤ E₅} {B₀ : E₃ ⥤ E₆}

/-- A horizontal composite of 2-squares, whiskered at the top and at the bottom, read at an object,
is a composite of four morphisms. -/
theorem whiskerBottom_whiskerTop_hComp_app (w : TwoSquare T L R B) (w' : TwoSquare T' R R' B')
    (α : T₀ ⟶ T ⋙ T') (β : B ⋙ B' ⟶ B₀) (M : E₁) :
    (((w ≫ₕ w').whiskerTop α).whiskerBottom β).app M =
      R'.map (α.app M) ≫ w'.app (T.obj M) ≫ B'.map (w.app M) ≫
        β.app (L.obj M) := by
  simp [TwoSquare.whiskerBottom_app, TwoSquare.whiskerTop_app, TwoSquare.hComp_app]

end

end Stacks.CategoryTheory

namespace Stacks.ModuleSkyscraper

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)

/-! ### The germ map of a composite -/

/-- As a homomorphism of rings, the germ map of `f ≫ g` at `x` is the germ map of `g` at `f x`
followed by the germ map of `f` at `x`. -/
theorem stalkMap_hom_comp :
    ((f ≫ g).stalkMap x).hom = (f.stalkMap x).hom.comp (g.stalkMap (f x)).hom :=
  congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp f g x)

/-- Reading an `𝒪_{X,x}`-module as an `𝒪_{Z,g (f x)}`-module along the germ map of `f ≫ g` is
reading it as an `𝒪_{Y,f x}`-module along the germ map of `f` and then as an `𝒪_{Z,g (f x)}`-module
along the germ map of `g`. The underlying map is the identity. -/
noncomputable def restrictScalarsStalkComp :
    ModuleCat.restrictScalars.{u} ((f ≫ g).stalkMap x).hom ≅
      ModuleCat.restrictScalars.{u} (f.stalkMap x).hom ⋙
        ModuleCat.restrictScalars.{u} (g.stalkMap (f x)).hom :=
  ModuleCat.restrictScalarsComp' (g.stalkMap (f x)).hom (f.stalkMap x).hom
    ((f ≫ g).stalkMap x).hom (stalkMap_hom_comp f g x)

/-- Base change of an `𝒪_{Z,g (f x)}`-module along the germ map of `g` at `f x` and then along the
germ map of `f` at `x` is base change along the germ map of `f ≫ g` at `x`. This is the isomorphism
of left adjoints induced by `restrictScalarsStalkComp`. -/
noncomputable def extendScalarsStalkComp :
    ModuleCat.extendScalars.{u} (g.stalkMap (f x)).hom ⋙
        ModuleCat.extendScalars.{u} (f.stalkMap x).hom ≅
      ModuleCat.extendScalars.{u} ((f ≫ g).stalkMap x).hom :=
  Adjunction.leftAdjointCompIso
    (ModuleCat.extendRestrictScalarsAdj (g.stalkMap (f x)).hom)
    (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom)
    (ModuleCat.extendRestrictScalarsAdj ((f ≫ g).stalkMap x).hom)
    (restrictScalarsStalkComp f g x).symm

/-- Under the mate correspondence between natural transformations of left adjoints and of the
corresponding right adjoints, the composition isomorphism for extension of scalars along the germ
maps corresponds to the one for restriction of scalars. -/
theorem conjugateEquiv_extendScalarsStalkComp_inv :
    conjugateEquiv ((ModuleCat.extendRestrictScalarsAdj (g.stalkMap (f x)).hom).comp
        (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom))
      (ModuleCat.extendRestrictScalarsAdj ((f ≫ g).stalkMap x).hom)
      (extendScalarsStalkComp f g x).inv = (restrictScalarsStalkComp f g x).inv :=
  Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

/-- The conjugate of the hom of the pullback composition isomorphism
`AlgebraicGeometry.Scheme.Modules.pullbackComp` is the inverse of the pushforward composition
isomorphism `AlgebraicGeometry.Scheme.Modules.pushforwardComp`. -/
theorem conjugateEquiv_pullbackComp_hom :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f))
      (Scheme.Modules.pullbackComp f g).hom = (Scheme.Modules.pushforwardComp f g).inv :=
  Stacks.CategoryTheory.conjugateEquiv_inv_of_hom _ _ (Scheme.Modules.pullbackComp f g).symm
    (Scheme.Modules.pushforwardComp f g) (Scheme.Modules.conjugateEquiv_pullbackComp_inv f g)

/-! ### The germ map composes -/

/-- The stalk functor on `𝒪_X`-modules computed on a germ: a morphism of modules is applied to the
section and the germ is taken afterwards. -/
theorem modulesStalkFunctor_map_germ {W : Scheme.{u}} (p : W) {M N : W.Modules} (φ : M ⟶ N)
    (U : W.Opens) (hp : p ∈ U) (t : Γ(M, U)) :
    ((modulesStalkFunctor W p).map φ) ((M.presheaf.germ U p hp) t) =
      (N.presheaf.germ U p hp) ((φ.val.app (op U)).hom t) :=
  stalkMapLinear_germ _ p U hp t

/-- A section of `M` over `(f ≫ g)⁻¹V` is a section of `(f ≫ g)_*M` over `V`, and its germ at
`g (f x)` is sent to its germ at `x` either in one step — by the germ map of `f ≫ g` — or in two,
by the germ map of `g` at `f x` and then the germ map of `f` at `x`. -/
theorem pushStalkMap_comp_app (M : X.Modules) :
    (pushStalkMap (f ≫ g) x).app M =
      (modulesStalkFunctor Z ((f ≫ g) x)).map ((Scheme.Modules.pushforwardComp f g).inv.app M) ≫
        (pushStalkMap g (f x)).app ((Scheme.Modules.pushforward f).obj M) ≫
        (ModuleCat.restrictScalars (g.stalkMap (f x)).hom).map ((pushStalkMap f x).app M) ≫
        (restrictScalarsStalkComp f g x).inv.app ((modulesStalkFunctor X x).obj M) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
  obtain ⟨V, hV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    ((Scheme.Modules.pushforward (f ≫ g)).obj M).presheaf s
  change _ = ((restrictScalarsStalkComp f g x).inv.app ((modulesStalkFunctor X x).obj M))
      (((ModuleCat.restrictScalars (g.stalkMap (f x)).hom).map ((pushStalkMap f x).app M))
        (((pushStalkMap g (f x)).app ((Scheme.Modules.pushforward f).obj M))
          (((modulesStalkFunctor Z ((f ≫ g) x)).map
              ((Scheme.Modules.pushforwardComp f g).inv.app M))
            ((((Scheme.Modules.pushforward (f ≫ g)).obj M).presheaf.germ V ((f ≫ g) x) hV) t))))
  rw [pushStalkMap_germ (f ≫ g) x M V hV t, modulesStalkFunctor_map_germ]
  erw [pushStalkMap_germ g (f x) ((Scheme.Modules.pushforward f).obj M) V hV t,
    pushStalkMap_germ f x M (g ⁻¹ᵁ V) hV t]
  rfl

/-- The germ map of `f ≫ g` at `x` is the germ map of `g` at `f x` followed by the germ map of `f`
at `x`, as an equality of 2-squares. -/
theorem pushStalkMap_comp :
    TwoSquare.mk _ _ _ _ (pushStalkMap (f ≫ g) x) =
      ((TwoSquare.mk _ _ _ _ (pushStalkMap f x) ≫ₕ
          TwoSquare.mk _ _ _ _ (pushStalkMap g (f x))).whiskerTop
            (Scheme.Modules.pushforwardComp f g).inv).whiskerBottom
        (restrictScalarsStalkComp f g x).inv := by
  refine NatTrans.ext (funext fun M ↦ (pushStalkMap_comp_app f g x M).trans ?_)
  exact (Stacks.CategoryTheory.whiskerBottom_whiskerTop_hComp_app _ _ _ _ M).symm

/-! ### Tag 0098 composes -/

/-- The stalk formula is compatible with composition, as an equality of 2-squares. Both sides are
squares on the pullback along `f ≫ g` and the extension of scalars along the germ map of `f ≫ g`;
the right-hand side is the vertical composite of the stalk formula for `g` at `f x` with the stalk
formula for `f` at `x`, whiskered by the two composition isomorphisms so as to be a square of that
shape. -/
theorem pullbackStalkIso_comp :
    TwoSquare.mk _ _ _ _ (pullbackStalkIso (f ≫ g) x).hom =
      ((TwoSquare.mk _ _ _ _ (pullbackStalkIso g (f x)).hom ≫ᵥ
          TwoSquare.mk _ _ _ _ (pullbackStalkIso f x).hom).whiskerLeft
            (Scheme.Modules.pullbackComp f g).hom).whiskerRight
        (extendScalarsStalkComp f g x).inv := by
  refine (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (ModuleCat.extendRestrictScalarsAdj ((f ≫ g).stalkMap x).hom)).injective
      ((pushStalkMap_comp f g x).trans ?_)
  rw [← conjugateEquiv_pullbackComp_hom, ← conjugateEquiv_extendScalarsStalkComp_inv]
  exact (Stacks.CategoryTheory.mateEquiv_vComp_whiskerLeft_whiskerRight _ _ _ _ _ _ _ _ _ _).symm

/-- The stalk formula is compatible with composition, on a module. For an `𝒪_Z`-module `N`, the
isomorphism

`𝒪_{X,x} ⊗_{𝒪_{Z,g (f x)}} N_{g (f x)} ≅ ((f ≫ g)^*N)_x`

for `f ≫ g` is: the composition isomorphism for extension of scalars along the germ maps, then the
stalk formula for `g` at `f x` with scalars extended along the germ map of `f`, then the stalk
formula for `f` at `x` applied to `g^*N`, then the stalk at `x` of the composition isomorphism for
pullback. -/
theorem pullbackStalkIso_comp_app (N : Z.Modules) :
    (pullbackStalkIso (f ≫ g) x).hom.app N =
      (extendScalarsStalkComp f g x).inv.app
          ((modulesStalkFunctor Z (g (f x))).obj N) ≫
        (ModuleCat.extendScalars (f.stalkMap x).hom).map
          ((pullbackStalkIso g (f x)).hom.app N) ≫
        (pullbackStalkIso f x).hom.app ((Scheme.Modules.pullback g).obj N) ≫
        (modulesStalkFunctor X x).map ((Scheme.Modules.pullbackComp f g).hom.app N) := by
  simpa only [TwoSquare.whiskerRight_app, TwoSquare.whiskerLeft_app, TwoSquare.vComp_app,
    Category.assoc] using
    congrArg (fun w ↦ NatTrans.app w N) (pullbackStalkIso_comp f g x)

/-- The stalk formula is compatible with composition, as an equality of isomorphisms of functors:
the two-step stalk computation of `g^* ⋙ f^*` is the one-step computation for `f ≫ g`, read through
the composition isomorphisms `AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`extendScalarsStalkComp`. -/
theorem pullbackStalkIso_comp_iso :
    Functor.isoWhiskerLeft (modulesStalkFunctor Z (g (f x))) (extendScalarsStalkComp f g x) ≪≫
        pullbackStalkIso (f ≫ g) x =
      Functor.isoWhiskerRight (pullbackStalkIso g (f x))
          (ModuleCat.extendScalars (f.stalkMap x).hom) ≪≫
        Functor.isoWhiskerLeft (Scheme.Modules.pullback g) (pullbackStalkIso f x) ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.pullbackComp f g) (modulesStalkFunctor X x) := by
  refine Iso.ext (NatTrans.ext (funext fun N ↦ ?_))
  change (extendScalarsStalkComp f g x).hom.app ((modulesStalkFunctor Z (g (f x))).obj N) ≫
      (pullbackStalkIso (f ≫ g) x).hom.app N =
    (ModuleCat.extendScalars (f.stalkMap x).hom).map ((pullbackStalkIso g (f x)).hom.app N) ≫
      (pullbackStalkIso f x).hom.app ((Scheme.Modules.pullback g).obj N) ≫
        (modulesStalkFunctor X x).map ((Scheme.Modules.pullbackComp f g).hom.app N)
  rw [pullbackStalkIso_comp_app f g x N, Iso.hom_inv_id_app_assoc]

end Stacks.ModuleSkyscraper

end
