module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.CategoryTheory.Comma.Over.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of presheaves of modules to a slice category has both adjoints

Let `O` be a presheaf of rings on a category `C` and let `U` be an object of `C`. Restriction
along the forgetful functor `C/U ⥤ C` carries a presheaf of `O`-modules to a presheaf of
modules over the restricted presheaf of rings, and this restriction functor `j_U^*` has both a
left adjoint `j_{U!}` and a right adjoint `j_{U*}`.

Both adjoints are the pointwise Kan extension formulas, and both are constructed here by hand
rather than taken from Mathlib: Mathlib's existence instance for the left adjoint of
`PresheafOfModules.pushforward` is available only when the two sites are small and the object,
morphism, module and ring universes all coincide, whereas nothing here bounds the ring universe
against the others. Over `X` the left adjoint is the coproduct `⨁_{p : X ⟶ U} M(p)` of the
sections of `M` over all objects of `C/U` with source `X`, and the right adjoint is the limit of
`N` over the comma category of objects of `C/U` under `X`, with scalars restricted along the
structure map of each index.

## Main definitions

* `Stacks.Sites.OverModules.overRingPresheaf`: the restriction of the presheaf of rings to the
  slice category over an object.
* `Stacks.Sites.OverModules.restrictionFunctor`: restriction of presheaves of modules, `j_U^*`.
* `Stacks.Sites.OverModules.extensionPresheaf`: the coproduct presheaf, `j_{U!} M`.
* `Stacks.Sites.OverModules.extensionFunctor`: the extension functor `j_{U!}` as a functor,
  assembled from the hom-set bijection `extensionHomEquiv`.
* `Stacks.Sites.OverModules.extensionFunctorAdjunction`: its adjunction with restriction.
* `Stacks.Sites.OverModules.directImage`: the limit functor, `j_{U*}`.
* `Stacks.Sites.OverModules.PresheafModuleAdjunctionsOver`: the two functors together with
  their adjunctions with restriction, as a single bundle.

## Main results

* `Stacks.Sites.OverModules.extensionHomEquiv` and
  `Stacks.Sites.OverModules.restrictionDirectImageAdjunction`: the two adjunctions.
* `Stacks.Sites.OverModules.presheafModuleAdjunctionsOver`: restriction along `C/U ⥤ C` has a
  left adjoint and a right adjoint, i.e. the adjoint triple `j_{U!} ⊣ j_U^* ⊣ j_{U*}`.
* `Stacks.Sites.OverModules.restriction_isLeftAdjoint` and
  `Stacks.Sites.OverModules.restriction_isRightAdjoint`: the same two facts as instances.

## Implementation notes

Every family and diagram here is indexed by an object of `Cᵒᵖ`, never of `C`, and its values
are ascribed the type `ModuleCat (O.obj X)` at the point of definition. This is forced rather
than stylistic: a presheaf of `O`-modules must have `ModuleCat (O.obj X)` as its module of
sections over `X : Cᵒᵖ`, whereas a coproduct or limit of a family indexed over `C` carries its
`HasColimit`/`HasLimit` instance in `ModuleCat (O.obj (op V))`. Those two are definitionally
equal, but the equality is not available to unification, which cannot unfold
`CategoryTheory.Limits.getColimitCocone`; indexing by `Cᵒᵖ` makes the instances match
syntactically, which is what lets the proofs below rewrite with `Sigma.ι_desc`, `limit.lift_π`
and `limit.w`.

For the same reason every morphism whose source or target needs an identification between two
spellings of one carrier is given a name — `extensionSummandRestriction`,
`extensionDescComponent`, `coneComponent`, `coneApply`, `directImageLift` — so that the
identification is performed once, at definition time, and does not have to be seen through by a
later `rw` or `change`. Each naturality square is stated as its own lemma about those named
morphisms and the corresponding structure field is then discharged by `exact`.

The module universe is a free parameter `a` throughout, subject only to `UnivLE.{v, a}` for the
coproducts and `UnivLE.{max u v, a}` for the limits; the bundled statement instantiates it at
`max u v m` with `m` free. The ring universe `w` is unconstrained.

## References

* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w m a

namespace Stacks.Sites.OverModules

variable {C : Type u} [Category.{v} C]

/-- The restriction of a presheaf of rings to the slice category over `U`. -/
abbrev overRingPresheaf (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) : (Over U)ᵒᵖ ⥤ RingCat.{w} :=
  (Over.forget U).op ⋙ O

/-- Restriction of presheaves of modules along `Over.forget U`, i.e. `j_U^*`. -/
@[stacks 03EJ "`j_U^* : PMod(O) ⥤ PMod(O_U)`"]
abbrev restrictionFunctor (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) :
    PresheafOfModules.{a, v, u, w} O ⥤
      PresheafOfModules.{a, v, max u v, w} (overRingPresheaf O U) :=
  PresheafOfModules.pushforward₀.{a} (Over.forget U) O

section Extension

variable (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)
  (M : PresheafOfModules.{a, v, max u v, w} (overRingPresheaf O U))

/-- The family of modules indexed by the maps from `X.unop` to `U`. -/
abbrev extensionSummands (X : Cᵒᵖ) : (X.unop ⟶ U) → ModuleCat.{a, w} (O.obj X) :=
  fun p => M.obj (op (Over.mk p))

variable [UnivLE.{v, a}]

/-- The restriction map of `M` from the summand indexed by `p` to the one indexed by
`f.unop ≫ p`, with its source and target spelled in terms of `O.obj X` and `O.map f`. -/
noncomputable def extensionSummandRestriction {X Y : Cᵒᵖ} (f : X ⟶ Y) (p : X.unop ⟶ U) :
    extensionSummands O U M X p ⟶
      (ModuleCat.restrictScalars (O.map f).hom).obj
        (extensionSummands O U M Y (f.unop ≫ p)) :=
  M.map (Over.homMk f.unop : Over.mk (f.unop ≫ p) ⟶ Over.mk p).op

/-- The restriction maps of `extensionPresheaf`. -/
noncomputable def extensionRestriction {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (∐ extensionSummands O U M X) ⟶
      (ModuleCat.restrictScalars (O.map f).hom).obj (∐ extensionSummands O U M Y) :=
  Sigma.desc fun p =>
    extensionSummandRestriction O U M f p ≫
      (ModuleCat.restrictScalars (O.map f).hom).map
        (Sigma.ι (extensionSummands O U M Y) (f.unop ≫ p))

/-- `extensionRestriction` precomposed with the inclusion of the summand indexed by `p`. -/
@[reassoc]
lemma ι_comp_extensionRestriction {X Y : Cᵒᵖ} (f : X ⟶ Y) (p : X.unop ⟶ U) :
    Sigma.ι (extensionSummands O U M X) p ≫ extensionRestriction O U M f =
      extensionSummandRestriction O U M f p ≫
        (ModuleCat.restrictScalars (O.map f).hom).map
          (Sigma.ι (extensionSummands O U M Y) (f.unop ≫ p)) :=
  Sigma.ι_desc _ _

/-- `extensionRestriction` on an element of the summand indexed by `p`, with the target
summand index given as any `q` equal to `f.unop ≫ p`. -/
@[simp]
lemma extensionRestriction_ι_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (p : X.unop ⟶ U)
    (q : Y.unop ⟶ U) (h : f.unop ≫ p = q) (x : M.obj (op (Over.mk p))) :
    extensionRestriction O U M f (Sigma.ι (extensionSummands O U M X) p x) =
      Sigma.ι (extensionSummands O U M Y) q
        (M.restrictₛₗ (Over.homMk f.unop h : Over.mk q ⟶ Over.mk p).op x) := by
  subst q
  exact ConcreteCategory.congr_hom (ι_comp_extensionRestriction O U M f p) x

/-- The presheaf of `O`-modules whose sections over `X` are the direct sum of the sections of
`M` over all objects `p : X.unop ⟶ U` of `C/U`. This is `j_{U!} M`. -/
noncomputable def extensionPresheaf : PresheafOfModules.{a, v, u, w} O where
  obj X := ∐ extensionSummands O U M X
  map f := extensionRestriction O U M f
  map_id X := by
    apply Sigma.hom_ext; intro p; ext x
    change extensionRestriction O U M (𝟙 X) (Sigma.ι (extensionSummands O U M X) p x) =
      Sigma.ι (extensionSummands O U M X) p x
    rw [extensionRestriction_ι_apply O U M (𝟙 X) p p (Category.id_comp p)]
    change Sigma.ι (extensionSummands O U M X) p (M.map (𝟙 _) x) = _
    rw [M.map_id]
    rfl
  map_comp {X Y Z} f g := by
    apply Sigma.hom_ext; intro p; ext x
    change extensionRestriction O U M (f ≫ g) (Sigma.ι (extensionSummands O U M X) p x) =
      extensionRestriction O U M g
        (extensionRestriction O U M f (Sigma.ι (extensionSummands O U M X) p x))
    rw [extensionRestriction_ι_apply O U M (f ≫ g) p (g.unop ≫ f.unop ≫ p)
      (Category.assoc _ _ _), extensionRestriction_ι_apply O U M f p (f.unop ≫ p) rfl,
      extensionRestriction_ι_apply O U M g (f.unop ≫ p) (g.unop ≫ f.unop ≫ p) rfl]
    change @Eq (↑(∐ extensionSummands O U M Z)) _ _
    exact congrArg
      (fun t : M.obj (op (Over.mk (g.unop ≫ f.unop ≫ p))) =>
        Sigma.ι (extensionSummands O U M Z) (g.unop ≫ f.unop ≫ p) t)
      (M.map_comp_apply
        (Over.homMk f.unop : Over.mk (f.unop ≫ p) ⟶ Over.mk p).op
        (Over.homMk g.unop : Over.mk (g.unop ≫ f.unop ≫ p) ⟶ Over.mk (f.unop ≫ p)).op x)

/-- The canonical map from `M` to the restriction of `extensionPresheaf M`, given over
`p : X ⟶ U` by the inclusion of the summand indexed by `p`. -/
noncomputable def extensionUnit :
    M ⟶ (restrictionFunctor O U).obj (extensionPresheaf O U M) where
  app A := Sigma.ι (extensionSummands O U M (op A.unop.left)) A.unop.hom
  naturality {A B} f := by
    ext x
    change Sigma.ι (extensionSummands O U M (op B.unop.left)) B.unop.hom
        (M.restrictₛₗ f x) =
      extensionRestriction O U M f.unop.left.op
        (Sigma.ι (extensionSummands O U M (op A.unop.left)) A.unop.hom x)
    rw [extensionRestriction_ι_apply O U M f.unop.left.op A.unop.hom B.unop.hom
      (Over.w f.unop)]
    rfl

/-- The map `M ⟶ j_U^* N` determined by a map `j_{U!} M ⟶ N`. -/
noncomputable def extensionHomForward {N : PresheafOfModules.{a, v, u, w} O}
    (α : extensionPresheaf O U M ⟶ N) : M ⟶ (restrictionFunctor O U).obj N :=
  extensionUnit O U M ≫ (restrictionFunctor O U).map α

/-- The component of a map `α : M ⟶ j_U^* N` at the object `p : X.unop ⟶ U` of `C/U`, with its
source and target spelled as `extensionSummands O U M X p` and `N.obj X`. -/
noncomputable def extensionDescComponent {N : PresheafOfModules.{a, v, u, w} O}
    (α : M ⟶ (restrictionFunctor O U).obj N) (X : Cᵒᵖ) (p : X.unop ⟶ U) :
    extensionSummands O U M X p ⟶ N.obj X :=
  α.app (op (Over.mk p))

/-- The naturality square for the map out of the direct sum determined by `α`, stated for
`extensionRestriction` so that every coproduct in it carries the same instance. -/
lemma extensionRestriction_comp_desc {N : PresheafOfModules.{a, v, u, w} O}
    (α : M ⟶ (restrictionFunctor O U).obj N) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    extensionRestriction O U M f ≫
        (ModuleCat.restrictScalars (O.map f).hom).map
          (Sigma.desc (extensionDescComponent O U M α Y)) =
      Sigma.desc (extensionDescComponent O U M α X) ≫ N.map f := by
  refine Sigma.hom_ext _ _ fun p => ?_
  rw [ι_comp_extensionRestriction_assoc, ← Functor.map_comp, Sigma.ι_desc,
    Sigma.ι_desc_assoc]
  exact α.naturality _

/-- The map `j_{U!} M ⟶ N` determined by a map `M ⟶ j_U^* N`. -/
noncomputable def extensionHomBackward {N : PresheafOfModules.{a, v, u, w} O}
    (α : M ⟶ (restrictionFunctor O U).obj N) : extensionPresheaf O U M ⟶ N where
  app X := Sigma.desc (extensionDescComponent O U M α X)
  naturality {_ _} f := extensionRestriction_comp_desc O U M α f

/-- `extensionHomBackward` precomposed with the inclusion of the summand indexed by `p`. -/
lemma ι_comp_extensionHomBackward {N : PresheafOfModules.{a, v, u, w} O}
    (α : M ⟶ (restrictionFunctor O U).obj N) (X : Cᵒᵖ) (p : X.unop ⟶ U) :
    Sigma.ι (extensionSummands O U M X) p ≫ (extensionHomBackward O U M α).app X =
      α.app (op (Over.mk p)) :=
  Sigma.ι_desc _ _

/-- Extension by zero is left adjoint to restriction, in hom-set form. -/
noncomputable def extensionHomEquiv (N : PresheafOfModules.{a, v, u, w} O) :
    (extensionPresheaf O U M ⟶ N) ≃ (M ⟶ (restrictionFunctor O U).obj N) where
  toFun := extensionHomForward O U M
  invFun := extensionHomBackward O U M
  left_inv α := by
    apply PresheafOfModules.hom_ext; intro X
    apply Sigma.hom_ext; intro p
    rw [ι_comp_extensionHomBackward]
    rfl
  right_inv α := PresheafOfModules.hom_ext fun A =>
    ι_comp_extensionHomBackward O U M α (op A.unop.left) A.unop.hom

/-- The bijection `extensionHomEquiv` is natural in the target presheaf. -/
lemma extensionHomEquiv_naturality (N N' : PresheafOfModules.{a, v, u, w} O) (g : N ⟶ N')
    (h : extensionPresheaf O U M ⟶ N) :
    extensionHomEquiv O U M N' (h ≫ g) =
      extensionHomEquiv O U M N h ≫ (restrictionFunctor O U).map g := by
  change extensionUnit O U M ≫ (restrictionFunctor O U).map (h ≫ g) =
    (extensionUnit O U M ≫ (restrictionFunctor O U).map h) ≫
      (restrictionFunctor O U).map g
  rw [Functor.map_comp, Category.assoc]

end Extension

section ExtensionFunctor

variable (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) [UnivLE.{v, a}]

/-- Extension of presheaves of modules from the slice category over `U`, as a functor: the
functor `j_{U!}` whose value at `M` is the direct-sum presheaf `extensionPresheaf O U M` and
whose action on morphisms is forced by the hom-set bijection `extensionHomEquiv`. -/
@[stacks 03EJ "`j_{U!} : PMod(O_U) ⥤ PMod(O)`"]
noncomputable def extensionFunctor :
    PresheafOfModules.{a, v, max u v, w} (overRingPresheaf O U) ⥤
      PresheafOfModules.{a, v, u, w} O :=
  Adjunction.leftAdjointOfEquiv (G := restrictionFunctor O U)
    (F_obj := fun M => extensionPresheaf O U M) (e := fun M N => extensionHomEquiv O U M N)
    (fun M N N' g h => extensionHomEquiv_naturality O U M N N' g h)

/-- Extension from the slice category is left adjoint to restriction. -/
@[stacks 03EJ "`j_{U!}` is left adjoint to `j_U^*`"]
noncomputable def extensionFunctorAdjunction :
    extensionFunctor.{v, u, w, a} O U ⊣ restrictionFunctor O U :=
  Adjunction.adjunctionOfEquivLeft _ _

end ExtensionFunctor

section DirectImage

variable (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)
  (M : PresheafOfModules.{a, v, max u v, w} (overRingPresheaf O U))

/-- The diagram over which the sections of `j_{U*} M` at `X` are a limit: the index category
is the comma category of objects of `C/U` under `X`, and the value at `i` is `M` at the
corresponding object of `C/U`, with scalars restricted along `i`. -/
noncomputable def directImageDiagram (X : Cᵒᵖ) :
    StructuredArrow X (Over.forget U).op ⥤ ModuleCat.{a, w} (O.obj X) where
  obj i := (ModuleCat.restrictScalars (O.map i.hom).hom).obj (M.obj i.right)
  map {i j} g := by
    let ρi := (O.map i.hom).hom
    let ρj := (O.map j.hom).hom
    let θ := (O.map ((Over.forget U).op.map g.right)).hom
    have hρ : ρj = θ.comp ρi := by
      have h := congrArg (fun k => (O.map k).hom) (StructuredArrow.w g)
      simpa [ρi, ρj, θ, Functor.map_comp, RingCat.hom_comp] using h.symm
    let : Module (O.obj X) (M.obj i.right) := Module.compHom _ ρi
    let : Module (O.obj X) (M.obj j.right) := Module.compHom _ ρj
    exact ModuleCat.ofHom
      { toFun := M.map g.right
        map_add' := map_add _
        map_smul' := by
          intro r x
          change M.map g.right (ρi r • x) = ρj r • M.map g.right x
          calc
            _ = ((overRingPresheaf O U).map g.right).hom (ρi r) • M.map g.right x :=
              M.map_smul g.right (ρi r) x
            _ = θ (ρi r) • M.map g.right x := rfl
            _ = ρj r • M.map g.right x := by
              have hr : θ (ρi r) = ρj r := by
                simpa [RingHom.comp_apply] using (congrArg (fun k : _ →+* _ => k r) hρ).symm
              rw [hr] }
  map_id i := by
    ext x
    change M.map (𝟙 i.right) x = x
    rw [PresheafOfModules.map_id]
    rfl
  map_comp g h := by
    ext x
    change M.map (g.right ≫ h.right) x = M.map h.right (M.map g.right x)
    exact PresheafOfModules.map_comp_apply _ _ _ _

variable [UnivLE.{max u v, a}]

/-- The sections of `j_{U*} M` over `X`. -/
noncomputable abbrev directImageFiberValue (X : Cᵒᵖ) : ModuleCat.{a, w} (O.obj X) :=
  limit (directImageDiagram O U M X)

end DirectImage

section IndexMap

variable (U : C)

/-- Reindexing the comma categories along `f : X ⟶ Y` in `Cᵒᵖ`. -/
def directImageIndexMap {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    StructuredArrow Y (Over.forget U).op ⥤ StructuredArrow X (Over.forget U).op where
  obj i := StructuredArrow.mk (f ≫ i.hom)
  map {i j} g := StructuredArrow.homMk g.right (by
    simpa only [StructuredArrow.mk, StructuredArrow.hom, Category.assoc] using
      congrArg (fun k => f ≫ k) g.w)

/-- The index object attached to an object of `C/U` by the identity. -/
def directImageIdentityIndex (A : (Over U)ᵒᵖ) :
    StructuredArrow (op A.unop.left) (Over.forget U).op :=
  StructuredArrow.mk (Y := A) (𝟙 (op A.unop.left))

end IndexMap

section Comparison

variable (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)
  (M : PresheafOfModules.{a, v, max u v, w} (overRingPresheaf O U))

/-- At an index `i` over `Y`, reindexing the diagram along `f : X ⟶ Y` is restriction of
scalars along `O.map f`. This is `restrictScalarsComp'App` for
`O.map (f ≫ i.hom) = O.map i.hom ∘ O.map f`. -/
noncomputable def directImageComparisonIso {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (i : StructuredArrow Y (Over.forget U).op) :
    (directImageDiagram O U M X).obj ((directImageIndexMap U f).obj i) ≅
      (ModuleCat.restrictScalars (O.map f).hom).obj
        ((directImageDiagram O U M Y).obj i) :=
  ModuleCat.restrictScalarsComp'App (O.map f).hom (O.map i.hom).hom
    (O.map (f ≫ i.hom)).hom (congrArg RingCat.Hom.hom (O.map_comp f i.hom))
    (M.obj i.right)

/-- The comparison isomorphism `directImageComparisonIso` is the identity on elements. -/
lemma directImageComparisonIso_hom_apply {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (i : StructuredArrow Y (Over.forget U).op)
    (x : (directImageDiagram O U M X).obj ((directImageIndexMap U f).obj i)) :
    (directImageComparisonIso O U M f i).hom x = x := rfl

/-- Reindexing the diagram along `f` is restriction of scalars along `O.map f`, naturally in
the index. -/
noncomputable def directImageDiagramIso {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    directImageIndexMap U f ⋙ directImageDiagram O U M X ≅
      directImageDiagram O U M Y ⋙ ModuleCat.restrictScalars (O.map f).hom :=
  NatIso.ofComponents (directImageComparisonIso O U M f) (by
    intro i j g
    ext x
    rfl)

/-- The components of `directImageDiagramIso` are the comparison isomorphisms. -/
lemma directImageDiagramIso_hom_app {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (i : StructuredArrow Y (Over.forget U).op) :
    (directImageDiagramIso O U M f).hom.app i = (directImageComparisonIso O U M f i).hom :=
  rfl

variable [UnivLE.{max u v, a}]

/-- The cone exhibiting `directImageFiberValue O U M X` over the reindexed diagram. -/
noncomputable def directImageMapCone {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Cone (directImageDiagram O U M Y ⋙
      ModuleCat.restrictScalars (O.map f).hom) where
  pt := directImageFiberValue O U M X
  π :=
    { app := fun i => limit.π (directImageDiagram O U M X)
        ((directImageIndexMap U f).obj i) ≫ (directImageDiagramIso O U M f).hom.app i
      naturality := by
        intro i j g
        have hnat := (directImageDiagramIso O U M f).hom.naturality g
        simp only [Functor.const_obj_map]
        rw [← limit.w (directImageDiagram O U M X) ((directImageIndexMap U f).map g),
          Category.assoc, Category.assoc]
        exact congrArg (fun k => limit.π (directImageDiagram O U M X)
          ((directImageIndexMap U f).obj i) ≫ k) hnat }

/-- The restriction maps of `j_{U*} M`. -/
noncomputable def directImageMap {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    directImageFiberValue O U M X ⟶
      (ModuleCat.restrictScalars (O.map f).hom).obj (directImageFiberValue O U M Y) := by
  let σ := (O.map f).hom
  let D := directImageDiagram O U M Y
  let : PreservesLimit D (ModuleCat.restrictScalars σ) :=
    ModuleCat.preservesLimit_restrictScalars σ D
  exact limit.lift (D ⋙ ModuleCat.restrictScalars σ) (directImageMapCone O U M f) ≫
    (preservesLimitIso (ModuleCat.restrictScalars σ) D).inv

/-- `directImageMap` followed by a projection of the target limit is a projection of the
source limit, at the reindexed object. -/
@[reassoc]
lemma directImageMap_comp_π {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (i : StructuredArrow Y (Over.forget U).op) :
    directImageMap O U M f ≫
        (ModuleCat.restrictScalars (O.map f).hom).map
          (limit.π (directImageDiagram O U M Y) i) =
      limit.π (directImageDiagram O U M X) ((directImageIndexMap U f).obj i) ≫
        (directImageComparisonIso O U M f i).hom := by
  let σ := (O.map f).hom
  let D := directImageDiagram O U M Y
  let : PreservesLimit D (ModuleCat.restrictScalars σ) :=
    ModuleCat.preservesLimit_restrictScalars σ D
  change (limit.lift (D ⋙ ModuleCat.restrictScalars σ) (directImageMapCone O U M f) ≫
      (preservesLimitIso (ModuleCat.restrictScalars σ) D).inv) ≫
      (ModuleCat.restrictScalars σ).map (limit.π D i) = _
  rw [Category.assoc, preservesLimitIso_inv_π, limit.lift_π]
  rfl

/-- `directImageMap` read on elements through the projections. -/
lemma directImageMap_projection {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (i : StructuredArrow Y (Over.forget U).op) (x : directImageFiberValue O U M X) :
    (limit.π (directImageDiagram O U M Y) i).hom ((directImageMap O U M f).hom x) =
      (limit.π (directImageDiagram O U M X)
        ((directImageIndexMap U f).obj i)).hom x := by
  exact ConcreteCategory.congr_hom (directImageMap_comp_π O U M f i) x

end Comparison

section Presheaf

variable (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) [UnivLE.{max u v, a}]
  (M : PresheafOfModules.{a, v, max u v, w} (overRingPresheaf O U))

/-- The presheaf of `O`-modules whose sections over `X` are the limit of `M` over the comma
category of objects of `C/U` under `X`. This is `j_{U*} M`. -/
noncomputable def directImagePresheaf : PresheafOfModules.{a, v, u, w} O where
  obj X := directImageFiberValue O U M X
  map f := directImageMap O U M f
  map_id X := by
    apply ModuleCat.hom_ext
    ext x
    apply Limits.Concrete.limit_ext (directImageDiagram O U M X)
    intro i
    have hw := congrArg (fun k : ModuleCat.Hom _ _ => k.hom x)
      (limit.w (directImageDiagram O U M X)
        (StructuredArrow.homMk (𝟙 i.right) (by simp [directImageIndexMap]) :
          (directImageIndexMap U (𝟙 X)).obj i ⟶ i))
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at hw
    have hid : ∀ y : (directImageDiagram O U M X).obj
        ((directImageIndexMap U (𝟙 X)).obj i),
        ((directImageDiagram O U M X).map
          (StructuredArrow.homMk (𝟙 i.right) (by simp [directImageIndexMap]) :
            (directImageIndexMap U (𝟙 X)).obj i ⟶ i)).hom y = y := by
      intro y
      change (M.map (𝟙 i.right)).hom y = y
      rw [M.map_id]
      rfl
    rw [hid] at hw
    change (limit.π (directImageDiagram O U M X) i).hom
        ((directImageMap O U M (𝟙 X)).hom x) =
      (limit.π (directImageDiagram O U M X) i).hom x
    rw [directImageMap_projection O U M (𝟙 X) i x]
    exact hw
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    ext x
    apply Limits.Concrete.limit_ext (directImageDiagram O U M Z)
    intro i
    have hw := congrArg (fun k : ModuleCat.Hom _ _ => k.hom x)
      (limit.w (directImageDiagram O U M X)
        (StructuredArrow.homMk (𝟙 i.right) (by simp [directImageIndexMap]) :
          (directImageIndexMap U (f ≫ g)).obj i ⟶
            (directImageIndexMap U f).obj ((directImageIndexMap U g).obj i)))
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at hw
    have hid : ∀ y : (directImageDiagram O U M X).obj
        ((directImageIndexMap U (f ≫ g)).obj i),
        ((directImageDiagram O U M X).map
          (StructuredArrow.homMk (𝟙 i.right) (by simp [directImageIndexMap]) :
            (directImageIndexMap U (f ≫ g)).obj i ⟶
              (directImageIndexMap U f).obj ((directImageIndexMap U g).obj i))).hom y = y := by
      intro y
      change (M.map (𝟙 i.right)).hom y = y
      rw [M.map_id]
      rfl
    rw [hid] at hw
    change (limit.π (directImageDiagram O U M Z) i).hom
        ((directImageMap O U M (f ≫ g)).hom x) =
      (limit.π (directImageDiagram O U M Z) i).hom
        ((directImageMap O U M g).hom ((directImageMap O U M f).hom x))
    rw [directImageMap_projection O U M (f ≫ g) i x,
      directImageMap_projection O U M g i ((directImageMap O U M f).hom x),
      directImageMap_projection O U M f ((directImageIndexMap U g).obj i) x]
    exact hw

end Presheaf

section Functor

variable (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) [UnivLE.{max u v, a}]
  {M N P : PresheafOfModules.{a, v, max u v, w} (overRingPresheaf O U)}

/-- A morphism of presheaves of modules on `C/U` induces a morphism of the diagrams whose
limits are the sections of the direct images. -/
noncomputable def directImageDiagramMap (α : M ⟶ N) (X : Cᵒᵖ) :
    directImageDiagram O U M X ⟶ directImageDiagram O U N X where
  app i := (ModuleCat.restrictScalars (O.map i.hom).hom).map (α.app i.right)
  naturality := by
    intro i j g
    ext x
    change (α.app j.right).hom ((M.map g.right).hom x) =
      (N.map g.right).hom ((α.app i.right).hom x)
    exact PresheafOfModules.naturality_apply α g.right x

/-- The cone used to define `directImageMapOnModules`. -/
noncomputable def directImageMapOnModulesCone (α : M ⟶ N) (X : Cᵒᵖ) :
    Cone (directImageDiagram O U N X) where
  pt := directImageFiberValue O U M X
  π :=
    { app := fun i => limit.π (directImageDiagram O U M X) i ≫
        (directImageDiagramMap O U α X).app i
      naturality := by
        intro i j g
        simp only [Functor.const_obj_map]
        rw [← limit.w (directImageDiagram O U M X) g, Category.assoc,
          (directImageDiagramMap O U α X).naturality g, ← Category.assoc]
        cat_disch }

/-- The map on sections of the direct images induced by `α`. -/
noncomputable def directImageMapOnModules (α : M ⟶ N) (X : Cᵒᵖ) :
    directImageFiberValue O U M X ⟶ directImageFiberValue O U N X :=
  limit.lift (directImageDiagram O U N X) (directImageMapOnModulesCone O U α X)

/-- `directImageMapOnModules` followed by the projection at `i` is the projection at `i`
followed by `α` at the object indexed by `i`. -/
@[reassoc]
lemma directImageMapOnModules_comp_π (α : M ⟶ N) (X : Cᵒᵖ)
    (i : StructuredArrow X (Over.forget U).op) :
    directImageMapOnModules O U α X ≫ limit.π (directImageDiagram O U N X) i =
      limit.π (directImageDiagram O U M X) i ≫ (directImageDiagramMap O U α X).app i :=
  limit.lift_π (directImageMapOnModulesCone O U α X) i

/-- `directImageMapOnModules` read on elements through the projections: it is `α` at the
object of `C/U` indexed by `i`. -/
lemma directImageMapOnModules_projection (α : M ⟶ N) (X : Cᵒᵖ)
    (i : StructuredArrow X (Over.forget U).op) (x : directImageFiberValue O U M X) :
    (limit.π (directImageDiagram O U N X) i).hom
        ((directImageMapOnModules O U α X).hom x) =
      (α.app i.right).hom ((limit.π (directImageDiagram O U M X) i).hom x) :=
  ConcreteCategory.congr_hom (directImageMapOnModules_comp_π O U α X i) x

/-- The naturality square of `directImageMapOnModules` in the object of `C`. -/
lemma directImageMap_comp_mapOnModules (α : M ⟶ N) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    directImageMap O U M f ≫
        (ModuleCat.restrictScalars (O.map f).hom).map
          (directImageMapOnModules O U α Y) =
      directImageMapOnModules O U α X ≫ directImageMap O U N f := by
  apply ModuleCat.hom_ext
  ext x
  apply Limits.Concrete.limit_ext (directImageDiagram O U N Y)
  intro i
  change (limit.π (directImageDiagram O U N Y) i).hom
      ((directImageMapOnModules O U α Y).hom ((directImageMap O U M f).hom x)) =
    (limit.π (directImageDiagram O U N Y) i).hom
      ((directImageMap O U N f).hom ((directImageMapOnModules O U α X).hom x))
  rw [directImageMapOnModules_projection O U α Y i ((directImageMap O U M f).hom x),
    directImageMap_projection O U M f i x,
    directImageMap_projection O U N f i ((directImageMapOnModules O U α X).hom x),
    directImageMapOnModules_projection O U α X ((directImageIndexMap U f).obj i) x]
  rfl

end Functor

section FunctorDef

variable (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) [UnivLE.{max u v, a}]

/-- The direct-image functor `j_{U*}` on presheaves of modules. -/
@[stacks 03EJ "`j_{U*} : PMod(O_U) ⥤ PMod(O)`"]
noncomputable def directImage :
    PresheafOfModules.{a, v, max u v, w} (overRingPresheaf O U) ⥤
      PresheafOfModules.{a, v, u, w} O where
  obj M := directImagePresheaf O U M
  map {M N} α :=
    { app := fun X => directImageMapOnModules O U α X
      naturality := fun {_ _} f => directImageMap_comp_mapOnModules O U α f }
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    ext x
    apply Limits.Concrete.limit_ext (directImageDiagram O U M X)
    intro i
    change (limit.π (directImageDiagram O U M X) i).hom
        ((directImageMapOnModules O U (𝟙 M) X).hom x) =
      (limit.π (directImageDiagram O U M X) i).hom x
    rw [directImageMapOnModules_projection O U (𝟙 M) X i x]
    rfl
  map_comp {M N P} α β := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    ext x
    apply Limits.Concrete.limit_ext (directImageDiagram O U P X)
    intro i
    change (limit.π (directImageDiagram O U P X) i).hom
        ((directImageMapOnModules O U (α ≫ β) X).hom x) =
      (limit.π (directImageDiagram O U P X) i).hom
        ((directImageMapOnModules O U β X).hom
          ((directImageMapOnModules O U α X).hom x))
    rw [directImageMapOnModules_projection O U (α ≫ β) X i x,
      directImageMapOnModules_projection O U β X i
        ((directImageMapOnModules O U α X).hom x),
      directImageMapOnModules_projection O U α X i x]
    rfl

end FunctorDef

section Adjunction

variable (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) [UnivLE.{max u v, a}]

variable {M : PresheafOfModules.{a, v, u, w} O}
  {N : PresheafOfModules.{a, v, max u v, w} (overRingPresheaf O U)}

/-- Transporting an element of the limit along a map of index objects. -/
lemma limit_π_map_apply {X : Cᵒᵖ} {i j : StructuredArrow X (Over.forget U).op} (δ : i ⟶ j)
    (z : directImageFiberValue O U N X) :
    ((directImageDiagram O U N X).map δ).hom
        ((limit.π (directImageDiagram O U N X) i).hom z) =
      (limit.π (directImageDiagram O U N X) j).hom z := by
  exact ConcreteCategory.congr_hom (limit.w (directImageDiagram O U N X) δ) z

omit [UnivLE.{max u v, a}] in
/-- The component of `η : j_U^* M ⟶ N` at the object of `C/U` indexed by `i`, with its source
spelled as `M.obj ((Over.forget U).op.obj i.right)`. Naming it performs that identification
once, where the elaborator can still see it. -/
noncomputable def coneComponent (η : (restrictionFunctor O U).obj M ⟶ N) {X : Cᵒᵖ}
    (i : StructuredArrow X (Over.forget U).op) :
    M.obj ((Over.forget U).op.obj i.right) ⟶ N.obj i.right :=
  η.app i.right

omit [UnivLE.{max u v, a}] in
/-- The value of the cone of `η` at the index `i` on an element. All the retyping between the
`restrictScalars` spellings of the carriers is done here, once. -/
noncomputable def coneApply (η : (restrictionFunctor O U).obj M ⟶ N) {X : Cᵒᵖ}
    (i : StructuredArrow X (Over.forget U).op) (x : M.obj X) : N.obj i.right :=
  (coneComponent O U η i).hom ((M.map i.hom).hom x)

/-- The cone over the direct-image diagram determined by a map `j_U^* M ⟶ N`. -/
noncomputable def directImageConeFromHom (η : (restrictionFunctor O U).obj M ⟶ N) (X : Cᵒᵖ) :
    Cone (directImageDiagram O U N X) where
  pt := M.obj X
  π :=
    { app := fun i => M.map i.hom ≫
        (ModuleCat.restrictScalars (O.map i.hom).hom).map (coneComponent O U η i)
      naturality := by
        intro i j g
        ext x
        change (coneComponent O U η j).hom ((M.map j.hom).hom x) =
          (N.map g.right).hom ((coneComponent O U η i).hom ((M.map i.hom).hom x))
        rw [← StructuredArrow.w g, PresheafOfModules.map_comp_apply]
        exact PresheafOfModules.naturality_apply η g.right _ }

/-- The map on sections determined by `η`, with its source spelled as `M.obj X`. -/
noncomputable def directImageLift (η : (restrictionFunctor O U).obj M ⟶ N) (X : Cᵒᵖ) :
    M.obj X ⟶ directImageFiberValue O U N X :=
  limit.lift (directImageDiagram O U N X) (directImageConeFromHom O U η X)

/-- `directImageLift` followed by the projection at `i` is the leg at `i` of the cone of `η`. -/
@[reassoc]
lemma directImageLift_comp_π (η : (restrictionFunctor O U).obj M ⟶ N) (X : Cᵒᵖ)
    (i : StructuredArrow X (Over.forget U).op) :
    directImageLift O U η X ≫ limit.π (directImageDiagram O U N X) i =
      (directImageConeFromHom O U η X).π.app i :=
  limit.lift_π (directImageConeFromHom O U η X) i

/-- `directImageLift` read on elements through the projection at `i`: it is `coneApply`. -/
lemma directImageLift_π_apply (η : (restrictionFunctor O U).obj M ⟶ N) (X : Cᵒᵖ)
    (i : StructuredArrow X (Over.forget U).op) (x : M.obj X) :
    (limit.π (directImageDiagram O U N X) i).hom ((directImageLift O U η X).hom x) =
      coneApply O U η i x := by
  exact ConcreteCategory.congr_hom (directImageLift_comp_π O U η X i) x

/-- The map `M ⟶ j_{U*} N` determined by a map `j_U^* M ⟶ N`. -/
noncomputable def directImageHomForward (η : (restrictionFunctor O U).obj M ⟶ N) :
    M ⟶ (directImage O U).obj N where
  app X := directImageLift O U η X
  naturality := by
    intro X Y f
    apply ModuleCat.hom_ext
    ext x
    apply Limits.Concrete.limit_ext (directImageDiagram O U N Y)
    intro i
    set y : M.obj Y := (M.map f).hom x with hy
    change (limit.π (directImageDiagram O U N Y) i).hom
        ((directImageLift O U η Y).hom y) =
      (limit.π (directImageDiagram O U N Y) i).hom
        ((directImageMap O U N f).hom ((directImageLift O U η X).hom x))
    rw [directImageMap_projection O U N f i, directImageLift_π_apply,
      directImageLift_π_apply]
    change (coneComponent O U η i).hom ((M.map i.hom).hom y) =
      (coneComponent O U η i).hom ((M.map (f ≫ i.hom)).hom x)
    rw [hy]
    exact congrArg (fun z => (coneComponent O U η i).hom z)
      (M.map_comp_apply f i.hom x).symm

/-- The map `j_U^* M ⟶ N` determined by a map `M ⟶ j_{U*} N`: evaluate at the index given by
the identity. -/
noncomputable def directImageHomBackward (β : M ⟶ (directImage O U).obj N) :
    (restrictionFunctor O U).obj M ⟶ N where
  app A :=
    β.app ((Over.forget U).op.obj A) ≫
      limit.π (directImageDiagram O U N ((Over.forget U).op.obj A))
        (directImageIdentityIndex U A) ≫
      (ModuleCat.restrictScalarsId'App (O.map (𝟙 ((Over.forget U).op.obj A))).hom
        (congrArg RingCat.Hom.hom (O.map_id ((Over.forget U).op.obj A))) (N.obj A)).hom
  naturality := by
    intro A B f
    apply ModuleCat.hom_ext
    ext x
    set f₀ : (Over.forget U).op.obj A ⟶ (Over.forget U).op.obj B :=
      (Over.forget U).op.map f with hf₀
    set z : directImageFiberValue O U N ((Over.forget U).op.obj A) :=
      (β.app ((Over.forget U).op.obj A)).hom x with hz
    change (limit.π (directImageDiagram O U N ((Over.forget U).op.obj B))
        (directImageIdentityIndex U B)).hom
        ((β.app ((Over.forget U).op.obj B)).hom ((M.map f₀).hom x)) =
      (N.map f).hom
        ((limit.π (directImageDiagram O U N ((Over.forget U).op.obj A))
          (directImageIdentityIndex U A)).hom z)
    rw [PresheafOfModules.naturality_apply β f₀ x]
    change (limit.π (directImageDiagram O U N ((Over.forget U).op.obj B))
        (directImageIdentityIndex U B)).hom
        ((directImageMap O U N f₀).hom z) = _
    rw [directImageMap_projection O U N f₀ (directImageIdentityIndex U B) z]
    exact (limit_π_map_apply O U
      (StructuredArrow.homMk f (by simp [directImageIdentityIndex,
          directImageIndexMap, hf₀]) :
        directImageIdentityIndex U A ⟶
          (directImageIndexMap U f₀).obj (directImageIdentityIndex U B)) z).symm

/-- `coneApply` for `directImageHomBackward β`: it is `β` followed by the projection at the
index given by the identity. -/
lemma coneApply_directImageHomBackward (β : M ⟶ (directImage O U).obj N) {X : Cᵒᵖ}
    (i : StructuredArrow X (Over.forget U).op) (x : M.obj X) :
    coneApply O U (directImageHomBackward O U β) i x =
      (limit.π (directImageDiagram O U N ((Over.forget U).op.obj i.right))
        (directImageIdentityIndex U i.right)).hom
          ((β.app ((Over.forget U).op.obj i.right)).hom ((M.map i.hom).hom x)) := rfl

/-- Restriction is left adjoint to the direct image, in hom-set form. -/
noncomputable def directImageHomEquiv (M : PresheafOfModules.{a, v, u, w} O)
    (N : PresheafOfModules.{a, v, max u v, w} (overRingPresheaf O U)) :
    ((restrictionFunctor O U).obj M ⟶ N) ≃ (M ⟶ (directImage O U).obj N) where
  toFun := directImageHomForward O U
  invFun := directImageHomBackward O U
  left_inv η := by
    apply PresheafOfModules.hom_ext
    intro A
    apply ModuleCat.hom_ext
    ext x
    set y : M.obj ((Over.forget U).op.obj A) := x with hy
    change (limit.π (directImageDiagram O U N ((Over.forget U).op.obj A))
        (directImageIdentityIndex U A)).hom
        ((directImageLift O U η ((Over.forget U).op.obj A)).hom y) = (η.app A).hom y
    rw [directImageLift_π_apply]
    change (η.app A).hom ((M.map (𝟙 ((Over.forget U).op.obj A))).hom y) = _
    rw [M.map_id]
    rfl
  right_inv β := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    ext x
    apply Limits.Concrete.limit_ext (directImageDiagram O U N X)
    intro i
    set zx : directImageFiberValue O U N X := (β.app X).hom x with hzx
    change (limit.π (directImageDiagram O U N X) i).hom
        ((directImageLift O U (directImageHomBackward O U β) X).hom x) =
      (limit.π (directImageDiagram O U N X) i).hom zx
    rw [directImageLift_π_apply, coneApply_directImageHomBackward,
      PresheafOfModules.naturality_apply β i.hom x]
    change (limit.π (directImageDiagram O U N ((Over.forget U).op.obj i.right))
        (directImageIdentityIndex U i.right)).hom
        ((directImageMap O U N i.hom).hom zx) = _
    rw [directImageMap_projection O U N i.hom
      (directImageIdentityIndex U i.right) zx]
    have hw := limit_π_map_apply O U
      (StructuredArrow.homMk (𝟙 i.right) (by simp [directImageIdentityIndex,
          directImageIndexMap]) :
        (directImageIndexMap U i.hom).obj (directImageIdentityIndex U i.right) ⟶ i) zx
    have hid : ∀ y : (directImageDiagram O U N X).obj
        ((directImageIndexMap U i.hom).obj (directImageIdentityIndex U i.right)),
        ((directImageDiagram O U N X).map
          (StructuredArrow.homMk (𝟙 i.right) (by simp [directImageIdentityIndex,
              directImageIndexMap]) :
            (directImageIndexMap U i.hom).obj (directImageIdentityIndex U i.right) ⟶
              i)).hom y = y := by
      intro y
      change (N.map (𝟙 i.right)).hom y = y
      rw [N.map_id]
      rfl
    rw [hid] at hw
    exact hw

/-- Restriction along `Over.forget U` is left adjoint to the direct image. -/
@[stacks 03EJ "`j_{U*}` is right adjoint to `j_U^*`"]
noncomputable def restrictionDirectImageAdjunction :
    restrictionFunctor O U ⊣ directImage O U :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N => directImageHomEquiv O U M N
      homEquiv_naturality_left_symm := by
        intro M M' N g h
        apply PresheafOfModules.hom_ext
        intro A
        apply ModuleCat.hom_ext
        ext x
        rfl
      homEquiv_naturality_right := by
        intro M N N' f g
        apply PresheafOfModules.hom_ext
        intro X
        apply ModuleCat.hom_ext
        ext x
        apply Limits.Concrete.limit_ext (directImageDiagram O U N' X)
        intro i
        change (limit.π (directImageDiagram O U N' X) i).hom
            ((directImageLift O U (f ≫ g) X).hom x) =
          (limit.π (directImageDiagram O U N' X) i).hom
            ((directImageMapOnModules O U g X).hom
              ((directImageLift O U f X).hom x))
        rw [directImageLift_π_apply,
          directImageMapOnModules_projection O U g X i,
          directImageLift_π_apply]
        rfl }

end Adjunction

/-- The left and right adjoints of restriction of presheaves of modules from `C` to `C/U`.
The fields `extension` and `directImage` are respectively the functors denoted `j_{U!}` and
`j_{U*}` in the Stacks Project. -/
structure PresheafModuleAdjunctionsOver (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) where
  /-- Extension from `C/U`, denoted `j_{U!}`. -/
  extension : PresheafOfModules.{max u v m} (overRingPresheaf O U) ⥤
    PresheafOfModules.{max u v m} O
  /-- Direct image from `C/U`, denoted `j_{U*}`. -/
  directImage : PresheafOfModules.{max u v m} (overRingPresheaf O U) ⥤
    PresheafOfModules.{max u v m} O
  /-- Extension is left adjoint to restriction. -/
  extensionRestriction : extension ⊣
    PresheafOfModules.pushforward₀.{max u v m} (Over.forget U) O
  /-- Direct image is right adjoint to restriction. -/
  restrictionDirectImage :
    PresheafOfModules.pushforward₀.{max u v m} (Over.forget U) O ⊣ directImage

/-- Restriction of presheaves of modules to `C/U` has both an extension left adjoint and a
direct-image right adjoint: the coproduct construction `extensionFunctor` and the limit
construction `directImage`, with their adjunctions. -/
@[stacks 03EJ "the adjoint triple `j_{U!} ⊣ j_U^* ⊣ j_{U*}`"]
noncomputable def presheafModuleAdjunctionsOver (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) :
    PresheafModuleAdjunctionsOver.{v, u, w, m} O U where
  extension := extensionFunctor.{v, u, w, max u v m} O U
  directImage := directImage.{v, u, w, max u v m} O U
  extensionRestriction := extensionFunctorAdjunction.{v, u, w, max u v m} O U
  restrictionDirectImage := restrictionDirectImageAdjunction.{v, u, w, max u v m} O U

/-- The left adjoint in the canonical bundle is the coproduct construction. -/
lemma presheafModuleAdjunctionsOver_extension (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) :
    (presheafModuleAdjunctionsOver.{v, u, w, m} O U).extension =
      extensionFunctor.{v, u, w, max u v m} O U :=
  rfl

/-- The right adjoint in the canonical bundle is the limit construction. -/
lemma presheafModuleAdjunctionsOver_directImage (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) :
    (presheafModuleAdjunctionsOver.{v, u, w, m} O U).directImage =
      directImage.{v, u, w, max u v m} O U :=
  rfl

/-- Restriction is a left adjoint, with no bound on the ring universe. -/
instance restriction_isLeftAdjoint (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) :
    (PresheafOfModules.pushforward₀.{max u v m} (Over.forget U) O).IsLeftAdjoint :=
  (presheafModuleAdjunctionsOver.{v, u, w, m} O U).restrictionDirectImage.isLeftAdjoint

/-- Restriction is a right adjoint, with no bound on the ring universe. -/
instance restriction_isRightAdjoint (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) :
    (PresheafOfModules.pushforward₀.{max u v m} (Over.forget U) O).IsRightAdjoint :=
  (presheafModuleAdjunctionsOver.{v, u, w, m} O U).extensionRestriction.isRightAdjoint

end Stacks.Sites.OverModules

end
