module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings

/-!
# The mixed tensor product of presheaves of modules and base-change cancellation

Let `f : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site `(C, J)`.  Let `H` be a
presheaf of `O₂`-modules and `G` a presheaf of `O₁`-modules.  The sections `H(X) ⊗_{O₁(X)} G(X)`
of their tensor product over the *smaller* sheaf of rings carry an action of the *larger* one,
through the first factor: this is Mathlib's `TensorProduct.leftModule`, the module structure that
`TensorProduct.AlgebraTensorModule` is written for.  This file assembles those sections into a
presheaf of `O₂`-modules and proves the base-change cancellation

`H ⊗_{O₂} (O₂ ⊗_{O₁} G) ≅ H ⊗_{O₁} G`

as presheaves of **`O₂`**-modules, naturally in `H`.

## Main definitions

* `Stacks.MixedBaseChange.mixedTensorObj`: **the mixed tensor product**
  `(H, G) ↦ (X ↦ H(X) ⊗_{O₁(X)} G(X))` as a presheaf of `O₂`-modules.
* `Stacks.MixedBaseChange.mixedTensorRight`: the mixed tensor product with `G` fixed, as a
  functor on presheaves of `O₂`-modules.
* `Stacks.MixedBaseChange.mixedBaseChange`: **base-change cancellation, `O₂`-linearly.**
* `Stacks.MixedBaseChange.mixedBaseChangeNatIso`: the same as an isomorphism of functors on
  presheaves of `O₂`-modules.
* `Stacks.MixedBaseChange.mixedSheafTensorRight`: the sheafification of the mixed tensor
  product, i.e. `Stacks.SheafOfModules.Tensor.sheafTensor` with its two factors over *different*
  sheaves of rings.
* `Stacks.MixedBaseChange.mixedSheafBaseChangeNatIso`: **base-change cancellation for sheaves of
  modules, `O₂`-linearly**, with
  `(Stacks.SheafOfModules.Tensor.sheafTensor O₂).flip.obj ((extendScalars f).obj G)` — the
  functor whose exactness Stacks 05V4 proves — on the left.

## Main results

* `Stacks.MixedBaseChange.restrictScalars_mixedTensorObj` and
  `restrictScalars_mixedTensorRight`: **the restriction of scalars of the mixed tensor product is
  the tensor product over `O₁` of the restriction**, by definition.  This is what makes the
  object above a lift of the one the single-ring development already has, rather than a second,
  unrelated tensor product.
* `Stacks.MixedBaseChange.restrictScalars_mixedBaseChange`: **the restriction of scalars of
  `mixedBaseChange` is `Stacks.FlatChangeOfRings.baseChange`.**  Together with the previous
  statement this is what gives the construction content: the `O₂`-linear cancellation is a lift
  of the `O₁`-linear one that `Stacks.FlatChangeOfRings` already uses, and not merely some
  `O₂`-linear isomorphism between two objects chosen to make one exist.
* `Stacks.MixedBaseChange.restrictScalarsMixedSheafTensorRight`: the same identification after
  sheafification, given the identification of sheafification with restriction of scalars.  That
  hypothesis is
  `Stacks.Cohomology.MixedDerivedTensor.sheafifyCommutesRestrictScalars`, which is proved
  unconditionally; it is a hypothesis here only because that file is downstream of this one.

## Implementation notes

**Why the carrier is the restriction, not a fresh tensor product.**  `mixedObj` is
`Stacks.tensorObj ((PresheafOfModules.restrictScalars (ringPresheafMap f)).obj H) G` — the
*existing* objectwise tensor product of the restriction of `H` with `G` — re-equipped with the
`O₂(X)`-action `TensorProduct.leftModule`, and `mixedMap` is the *existing* restriction map
re-typed as an `O₂(X)`-semilinear one.  Nothing about the underlying presheaf of abelian groups
is rebuilt.  This is what makes `restrictScalars_mixedTensorObj` hold by `rfl`: restriction of
scalars of `TensorProduct.leftModule` over `O₂(X)` is `TensorProduct.leftModule` over `O₁(X)`,
because `Module.compHom` of the `O₂(X)`-action on `H(X)` is the `O₁(X)`-action on `H(X)` that the
restriction of `H` already carries.  Building a fresh `PresheafOfModules` with carrier
`H(X) ⊗_{O₁(X)} G(X)` instead would make every comparison with the single-ring development a
transport.

**Where the `O₂`-linearity comes from.**  Only from `Stacks.FlatChangeOfRings.tensorBaseChange`,
which is `TensorProduct.AlgebraTensorModule.cancelBaseChange` and is `O₂(X)`-linear on the nose.
`Stacks.FlatChangeOfRings.baseChangeApp` discards that linearity with
`LinearEquiv.restrictScalars`, because its target is a presheaf of `O₁`-modules; here the target
is a presheaf of `O₂`-modules and the `LinearEquiv` is used as it stands.  So the two
constructions share their only mathematical input, and `restrictScalars_mixedBaseChange` holds by
`rfl` for the same reason that `restrictScalars_mixedTensorObj` does.

**The `O₁(X)`-module structure on `H(X)`.**  It is supplied as `Module.compHom` of `f` at `X`,
which is exactly the structure `ModuleCat.restrictScalars` puts on the restriction of `H(X)`;
`IsScalarTower` then holds by `rfl` on scalars.  Supplying it any other way — for instance by
`Algebra.toModule` of the algebra structure — would break the `rfl`s above.

**The site plays no role.**  Everything here is objectwise, so the hypotheses on `J` are only
those needed to *spell* a morphism of sheaves of rings as a morphism of presheaves of rings, and
the sheaf-level statement is sheafification applied to the presheaf-level one.

**Where this is used.**  `Stacks.MixedBaseChange.mixedSheafTensor` makes the mixed tensor
product a bifunctor and proves the cancellation natural in the second factor as well; the
derived tensor product over `f⁻¹O'` with values in `D(O)` built from it, and Stacks 08I6 and
08DE in `D(O)`, are in `MixedDerivedTensor.LinearDerivedMixedTensor` under
`StacksDraft.CategoryTheory.Sites.Cohomology.DerivedPullback`, and in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.MixedDerivedTensorOnARingedSpace`.

## References

* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe v u w

namespace Stacks.MixedBaseChange

open Stacks Stacks.FlatChangeOfRings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (f : O₁ ⟶ O₂)

/-! ## Transferring an identity of morphisms to sections

Every proof below reduces an obligation about the mixed tensor product to the corresponding,
already proved, obligation about `Stacks.tensorObj` — the two have the same underlying maps of
abelian groups.  The reduction is always "the two morphisms are equal, hence agree on a section",
and these two lemmas state that implication at a fully explicit type, so that the definitional
identification happens in one `exact` rather than in the unification of a `congrArg`. -/

/-- Equal morphisms of modules agree on elements. -/
lemma hom_apply_congr {R : Type w} [Ring R] {M N : ModuleCat.{w} R} {α β : M ⟶ N} (h : α = β)
    (t : M) : (ModuleCat.Hom.hom α) t = (ModuleCat.Hom.hom β) t := by rw [h]

/-- Equal morphisms of presheaves of modules agree on sections. -/
lemma app_apply_congr {R : Cᵒᵖ ⥤ RingCat.{w}} {M N : PresheafOfModules.{w} R} {α β : M ⟶ N}
    (h : α = β) (X : Cᵒᵖ) (t : M.obj X) :
    (ModuleCat.Hom.hom (PresheafOfModules.Hom.app α X)) t =
      (ModuleCat.Hom.hom (PresheafOfModules.Hom.app β X)) t := by rw [h]

/-! ## The mixed tensor product of presheaves of modules -/

section Presheaf

variable (H : PresheafOfModules.{w} (ringPresheaf O₂.obj))
  (G : PresheafOfModules.{w} (ringPresheaf O₁.obj))

/-- `H` read as a presheaf of `O₁`-modules. -/
noncomputable abbrev restrict : PresheafOfModules.{w} (ringPresheaf O₁.obj) :=
  (PresheafOfModules.restrictScalars (ringPresheafMap f)).obj H

/-- **The action of `O₂(X)` on `H(X) ⊗_{O₁(X)} G(X)`**, through the first factor.  This is
`TensorProduct.leftModule`, the module structure `TensorProduct.AlgebraTensorModule` is written
for; the `O₁(X)`-action on `H(X)` it is compatible with is the one the restriction of `H`
carries. -/
@[instance_reducible]
noncomputable def sectionModule (X : Cᵒᵖ) :
    Module ((ringPresheaf O₂.obj).obj X) ((tensorObj (restrict f H) G).obj X) := by
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := (f.hom.app X).hom.toAlgebra
  letI : Module (O₁.obj.obj X) (H.obj X) := Module.compHom _ (f.hom.app X).hom
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (H.obj X) :=
    IsScalarTower.of_algebraMap_smul (by intro r x; rfl)
  exact inferInstanceAs (Module (O₂.obj.obj X) (H.obj X ⊗[O₁.obj.obj X] G.obj X))

/-- The sections of the mixed tensor product over `X`: the sections of `H ⊗_{O₁} G` with their
`O₂(X)`-action. -/
noncomputable abbrev mixedObj (X : Cᵒᵖ) : ModuleCat.{w} ((ringPresheaf O₂.obj).obj X) :=
  @ModuleCat.of ((ringPresheaf O₂.obj).obj X) _ ((tensorObj (restrict f H) G).obj X) _
    (sectionModule f H G X)

/-- The restriction map of the mixed tensor product: the restriction map of `H ⊗_{O₁} G`, which
is `O₂(X)`-semilinear along `O₂(X) ⟶ O₂(Y)` because `H`'s restriction map is. -/
noncomputable def mixedMap {X Y : Cᵒᵖ} (g : X ⟶ Y) :
    mixedObj f H G X ⟶
      (ModuleCat.restrictScalars ((ringPresheaf O₂.obj).map g).hom).obj (mixedObj f H G Y) := by
  letI : Module ((ringPresheaf O₂.obj).obj X)
      ((restrict f H).obj X ⊗[(ringPresheaf O₁.obj).obj X] G.obj X) := sectionModule f H G X
  letI : Module ((ringPresheaf O₂.obj).obj Y)
      ((restrict f H).obj Y ⊗[(ringPresheaf O₁.obj).obj Y] G.obj Y) := sectionModule f H G Y
  letI : Module ((ringPresheaf O₂.obj).obj X)
      ((restrict f H).obj Y ⊗[(ringPresheaf O₁.obj).obj Y] G.obj Y) :=
    Module.compHom _ ((ringPresheaf O₂.obj).map g).hom
  refine ModuleCat.ofHom (X := mixedObj f H G X)
    (Y := (ModuleCat.restrictScalars ((ringPresheaf O₂.obj).map g).hom).obj (mixedObj f H G Y))
    (show ((restrict f H).obj X ⊗[(ringPresheaf O₁.obj).obj X] G.obj X)
        →ₗ[(ringPresheaf O₂.obj).obj X]
        ((restrict f H).obj Y ⊗[(ringPresheaf O₁.obj).obj Y] G.obj Y) from
      { toFun := TensorProduct.map ((restrict f H).restrictₛₗ g) (G.restrictₛₗ g)
        map_add' := map_add _
        map_smul' := ?_ })
  intro s t
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]
  | tmul a x =>
    exact congrArg
      (fun b : (restrict f H).obj Y ↦
        b ⊗ₜ[(ringPresheaf O₁.obj).obj Y] (G.restrictₛₗ g x))
      (H.map_smul g s (a : H.obj X))

/-- **The mixed tensor product of presheaves of modules**: `X ↦ H(X) ⊗_{O₁(X)} G(X)`, as a
presheaf of `O₂`-modules.  The `O₂`-action is through the first factor.  Compare Mathlib's
`TensorProduct.AlgebraTensorModule`, of which this is the presheaf-level analogue. -/
noncomputable def mixedTensorObj : PresheafOfModules.{w} (ringPresheaf O₂.obj) where
  obj X := mixedObj f H G X
  map g := mixedMap f H G g
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    exact hom_apply_congr ((tensorObj (restrict f H) G).map_id X) t
  map_comp g h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    exact hom_apply_congr ((tensorObj (restrict f H) G).map_comp g h) t

/-- **The restriction of scalars of the mixed tensor product is the tensor product over `O₁` of
the restriction.**  By definition: the carrier and the restriction maps are literally those of
`Stacks.tensorObj (restrict f H) G`, and restricting `TensorProduct.leftModule` over `O₂(X)`
along `f` gives `TensorProduct.leftModule` over `O₁(X)`. -/
theorem restrictScalars_mixedTensorObj :
    (PresheafOfModules.restrictScalars (ringPresheafMap f)).obj (mixedTensorObj f H G) =
      tensorObj (restrict f H) G :=
  rfl

end Presheaf

/-! ## Functoriality in the module over the larger ring -/

section Functor

variable (G : PresheafOfModules.{w} (ringPresheaf O₁.obj))

/-- The mixed tensor product of a morphism of presheaves of `O₂`-modules with the identity of
`G`: on sections it is the tensor product of the two maps, which is `O₂(X)`-linear because each
component of the morphism is. -/
noncomputable def mixedHom {H H' : PresheafOfModules.{w} (ringPresheaf O₂.obj)} (φ : H ⟶ H') :
    mixedTensorObj f H G ⟶ mixedTensorObj f H' G where
  app X := by
    letI : Module ((ringPresheaf O₂.obj).obj X)
        ((restrict f H).obj X ⊗[(ringPresheaf O₁.obj).obj X] G.obj X) := sectionModule f H G X
    letI : Module ((ringPresheaf O₂.obj).obj X)
        ((restrict f H').obj X ⊗[(ringPresheaf O₁.obj).obj X] G.obj X) := sectionModule f H' G X
    refine ModuleCat.ofHom (X := mixedObj f H G X) (Y := mixedObj f H' G X)
      (show ((restrict f H).obj X ⊗[(ringPresheaf O₁.obj).obj X] G.obj X)
          →ₗ[(ringPresheaf O₂.obj).obj X]
          ((restrict f H').obj X ⊗[(ringPresheaf O₁.obj).obj X] G.obj X) from
        { toFun := TensorProduct.map
            ((((PresheafOfModules.restrictScalars (ringPresheafMap f)).map φ).app X).hom)
            LinearMap.id
          map_add' := map_add _
          map_smul' := ?_ })
    intro s t
    induction t using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]
    | tmul a x =>
      exact congrArg
        (fun b : (restrict f H').obj X ↦ b ⊗ₜ[(ringPresheaf O₁.obj).obj X] x)
        ((φ.app X).hom.map_smul s (a : H.obj X))
  naturality := by
    intro X Y g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    exact hom_apply_congr
      (((tensorRight G).map
        ((PresheafOfModules.restrictScalars (ringPresheafMap f)).map φ)).naturality g) t

/-- **The mixed tensor product with `G`, as a functor** on presheaves of `O₂`-modules.  This is
the `O₂`-valued analogue of `Stacks.tensorRight G`. -/
noncomputable def mixedTensorRight :
    PresheafOfModules.{w} (ringPresheaf O₂.obj) ⥤ PresheafOfModules.{w} (ringPresheaf O₂.obj) where
  obj H := mixedTensorObj f H G
  map φ := mixedHom f G φ
  map_id H := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    exact app_apply_congr
      ((tensorRight G).map_id ((PresheafOfModules.restrictScalars (ringPresheafMap f)).obj H)) X t
  map_comp φ ψ := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    exact app_apply_congr
      ((tensorRight G).map_comp
        ((PresheafOfModules.restrictScalars (ringPresheafMap f)).map φ)
        ((PresheafOfModules.restrictScalars (ringPresheafMap f)).map ψ)) X t

/-- **The restriction of scalars of the mixed tensor product functor is the tensor product with
`G` of the restriction**, as functors.  By definition, like
`Stacks.MixedBaseChange.restrictScalars_mixedTensorObj`. -/
theorem restrictScalars_mixedTensorRight :
    mixedTensorRight f G ⋙ PresheafOfModules.restrictScalars (ringPresheafMap f) =
      PresheafOfModules.restrictScalars (ringPresheafMap f) ⋙ tensorRight G :=
  rfl

end Functor

/-! ## Base-change cancellation, `O₂`-linearly -/

section BaseChange

variable (H : PresheafOfModules.{w} (ringPresheaf O₂.obj))
  (G : PresheafOfModules.{w} (ringPresheaf O₁.obj))

/-- The component at `X` of the `O₂`-linear base-change cancellation: it is
`Stacks.FlatChangeOfRings.tensorBaseChange`, i.e.
`TensorProduct.AlgebraTensorModule.cancelBaseChange`, used *without*
`LinearEquiv.restrictScalars`. -/
noncomputable def mixedBaseChangeApp (X : Cᵒᵖ) :
    (tensorObj H ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj G)).obj X ≅
      (mixedTensorObj f H G).obj X := by
  letI : Algebra (O₁.obj.obj X) (O₂.obj.obj X) := (f.hom.app X).hom.toAlgebra
  letI : Module (O₁.obj.obj X) (H.obj X) := Module.compHom _ (f.hom.app X).hom
  letI : IsScalarTower (O₁.obj.obj X) (O₂.obj.obj X) (H.obj X) :=
    IsScalarTower.of_algebraMap_smul (by intro r x; rfl)
  exact LinearEquiv.toModuleIso
    (tensorBaseChange (R := O₁.obj.obj X) (S := O₂.obj.obj X) (G := G.obj X) (H := H.obj X))

/-- **Base-change cancellation for presheaves of modules, `O₂`-linearly**:

`H ⊗_{O₂} (O₂ ⊗_{O₁} G) ≅ H ⊗_{O₁} G`

as presheaves of `O₂`-modules.  `Stacks.FlatChangeOfRings.baseChange` is the restriction of
scalars of this (`restrictScalars_mixedBaseChange`). -/
noncomputable def mixedBaseChange :
    tensorObj H ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj G) ≅
      mixedTensorObj f H G := by
  refine PresheafOfModules.isoMk (mixedBaseChangeApp f H G) ?_
  intro X Y g
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact fun t ↦ hom_apply_congr ((baseChange f G H).hom.naturality g) t

/-- **The restriction of scalars of the `O₂`-linear cancellation is the `O₁`-linear one** of
`Stacks.FlatChangeOfRings.baseChange`.  Both are
`TensorProduct.AlgebraTensorModule.cancelBaseChange` on sections, the one before and the other
after `LinearEquiv.restrictScalars`, so this is `rfl` once `restrictScalars_mixedTensorObj` is. -/
theorem restrictScalars_mixedBaseChange :
    (PresheafOfModules.restrictScalars (ringPresheafMap f)).map (mixedBaseChange f H G).hom =
      (baseChange f G H).hom :=
  rfl

end BaseChange

/-! ## Naturality in the module over the larger ring -/

section NatIso

variable (G : PresheafOfModules.{w} (ringPresheaf O₁.obj))

/-- The `O₂`-linear cancellation is natural in the first tensor factor. -/
lemma mixedBaseChange_naturality
    {H H' : PresheafOfModules.{w} (ringPresheaf O₂.obj)} (φ : H ⟶ H') :
    (tensorRight ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj G)).map φ ≫
        (mixedBaseChange f H' G).hom =
      (mixedBaseChange f H G).hom ≫ (mixedTensorRight f G).map φ := by
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  exact app_apply_congr (baseChange_naturality f G φ) X t

/-- **The `O₂`-linear base-change cancellation as an isomorphism of functors** on presheaves of
`O₂`-modules.  This is the `O₂`-valued lift of
`Stacks.FlatChangeOfRings.baseChangeNatIso`. -/
noncomputable def mixedBaseChangeNatIso :
    tensorRight ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings f.hom).obj G) ≅
      mixedTensorRight f G :=
  NatIso.ofComponents (fun H ↦ mixedBaseChange f H G)
    (fun φ ↦ mixedBaseChange_naturality f G φ)

end NatIso

/-! ## The sheaf-level statement

Sheafification of the presheaf-level mixed tensor product, and the base-change cancellation
read at it.  Nothing new is proved here: the comparison is the presheaf-level one sheafified,
composed with `Stacks.FlatChangeOfRings.tensorRightExtendScalarsIso`, which says that tensoring
and sheafifying does not distinguish the sectionwise extension of scalars `O₂ ⊗_{p,O₁} G` from
its sheafification `O₂ ⊗_{O₁} G`. -/

section Sheaf

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (G : SheafOfModules.{w} (commRingSheafToRingSheaf O₁))

/-- **The mixed tensor product of sheaves of modules**: `H ↦ (H ⊗_{O₁} G)^#`, a sheaf of
`O₂`-modules.  This is `Stacks.SheafOfModules.Tensor.sheafTensor` with the two factors taken over
*different* sheaves of rings, which the single-ring tensor product of this repository cannot
express. -/
noncomputable def mixedSheafTensorRight :
    SheafOfModules.{w} (commRingSheafToRingSheaf O₂) ⥤
      SheafOfModules.{w} (commRingSheafToRingSheaf O₂) :=
  SheafOfModules.forget (commRingSheafToRingSheaf O₂) ⋙
    mixedTensorRight f G.val ⋙ moduleSheafification O₂

/-- **Base-change cancellation for sheaves of modules, `O₂`-linearly**:

`H ⊗_{O₂} (O₂ ⊗_{O₁} G) ≅ H ⊗_{O₁} G`

as sheaves of `O₂`-modules, naturally in `H`, with the right-hand side the mixed tensor product
over the *smaller* sheaf of rings carrying its `O₂`-action.  The left-hand side is
`Stacks.SheafOfModules.Tensor.sheafTensor` with its right factor fixed at the extension of
scalars of `G`, i.e. the functor whose exactness is what Stacks 05V4 proves. -/
noncomputable def mixedSheafBaseChangeNatIso :
    (Stacks.SheafOfModules.Tensor.sheafTensor O₂).flip.obj ((extendScalars f).obj G) ≅
      mixedSheafTensorRight f G :=
  Functor.isoWhiskerLeft (SheafOfModules.forget (commRingSheafToRingSheaf O₂))
      (tensorRightExtendScalarsIso f G).symm ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.forget (commRingSheafToRingSheaf O₂))
      (Functor.isoWhiskerRight (mixedBaseChangeNatIso f G.val) (moduleSheafification O₂))

/-- **The restriction of scalars of the mixed tensor product of sheaves is the tensor product
over `O₁` of the restriction**, given the identification `e` of sheafification with restriction of
scalars.  At presheaf level this is `restrictScalars_mixedTensorRight`, an equality; sheafifying
needs `e`, which is exactly
`Stacks.Cohomology.MixedDerivedTensor.sheafifyCommutesRestrictScalars` — proved there
unconditionally, and taken as a hypothesis here only because that file sits downstream of this
one in the import order. -/
noncomputable def restrictScalarsMixedSheafTensorRight
    (e : PresheafOfModules.restrictScalars (ringPresheafMap f) ⋙ moduleSheafification O₁ ≅
      moduleSheafification O₂ ⋙ SheafOfModules.restrictScalars.{w} (ringSheafMap f)) :
    mixedSheafTensorRight f G ⋙ SheafOfModules.restrictScalars.{w} (ringSheafMap f) ≅
      SheafOfModules.restrictScalars.{w} (ringSheafMap f) ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor O₁).flip.obj G :=
  Functor.isoWhiskerLeft
    (SheafOfModules.forget (commRingSheafToRingSheaf O₂) ⋙ mixedTensorRight f G.val) e.symm

end Sheaf

end Stacks.MixedBaseChange
