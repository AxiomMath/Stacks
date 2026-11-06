module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackUnivLE
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The direct image of sheaves of modules along a cocontinuous functor of sites

Let `w : X ⥤ Y` be a cocontinuous functor of sites, so that it gives rise to a morphism of topoi
`f : Sh(X) ⟶ Sh(Y)` whose direct image `f_* = {}_sw` is right Kan extension along `w.op`
(Stacks 00XO), that is, `CategoryTheory.Functor.sheafPushforwardCocontinuous`. Let `O_X` and
`O_Y` be sheaves of rings on `X` and on `Y` and let `f^♯ : O_Y ⟶ {}_sw O_X` make `f` a morphism
of ringed topoi. This file constructs the direct image of sheaves of modules,
`f_* : Mod(O_X) ⥤ Mod(O_Y)`, and its left adjoint, the inverse image
`f^* G = O_X ⊗_{f^{-1}O_Y} f^{-1}G`.

The underlying sheaf of abelian groups of `f_* M` is `{}_sw` of the underlying sheaf of abelian
groups of `M`, *on the nose*: the construction puts an `O_Y`-module structure on the right Kan
extension itself rather than transporting one along an isomorphism.

## Main definitions

* `Stacks.SheafOfModules.ranπ`: the leg at `(U, ψ : V ⟶ w(U))` of the limit cone that computes
  the right Kan extension along `w.op` at `V`.
* `Stacks.SheafOfModules.ranSMul`: scalar multiplication by a section of `O_Y` on the right Kan
  extension along `w.op` of the underlying presheaf of abelian groups of a presheaf of
  `O_X`-modules; it is the unique endomorphism acting on the leg at `(U, ψ)` through the
  corresponding section of `O_X`.
* `Stacks.SheafOfModules.ranPushforward`: the direct image of *presheaves* of modules, a functor
  `Mod(O_X) ⥤ Mod(O_Y)` on presheaves of modules whose underlying presheaf of abelian groups is
  right Kan extension along `w.op`.
* `Stacks.SheafOfModules.pushforwardCocontinuous`: the direct image
  `f_* : Mod(O_X) ⥤ Mod(O_Y)` of sheaves of modules.
* `Stacks.SheafOfModules.ranUnitRing`: the tautological structure map `T ⟶ {}_sw (w^{-1}T)` of a
  presheaf of rings `T` on the target site, the unit of the right Kan extension adjunction.
* `Stacks.SheafOfModules.structureMapRestrict`: the ring map `w^{-1}O_Y ⟶ O_X` adjoint to
  `f^♯ : O_Y ⟶ {}_sw O_X`.
* `Stacks.SheafOfModules.inverseImageCocontinuous`: the inverse image
  `f^* : Mod(O_Y) ⥤ Mod(O_X)`, `f^* G = O_X ⊗_{f^{-1}O_Y} f^{-1}G`.

## Main results

* `Stacks.SheafOfModules.pushforwardCocontinuous_comp_toSheaf`: the underlying sheaf of abelian
  groups of `f_* M` is `{}_sw` of the underlying sheaf of abelian groups of `M`, as an equality
  of functors `Mod(O_X) ⥤ Sh(Y, Ab)`.
* `Stacks.SheafOfModules.pushforward₀RanPushforwardAdjunction`: restriction of presheaves of
  modules along `w` is left adjoint to the direct image of presheaves of modules for the
  tautological structure map.
* `Stacks.SheafOfModules.ranPushforwardAdjunction`: the direct image of presheaves of modules
  for an arbitrary structure map `f^♯` has a left adjoint, namely restriction along `w` followed
  by base change along `structureMapRestrict`.
The adjunction `f^* ⊣ f_*` on sheaves of modules — so that `f_*` is a right adjoint, which is
condition (1) of Stacks 0FN3 for the morphism of *ringed* topoi attached to a cocontinuous
functor of sites — is `Stacks.SheafOfModules.inverseImageCocontinuousAdjunction` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InverseImageCocontinuous.lean`, which imports
this file.

## Implementation notes

The module structure is built from the pointwise description of the right Kan extension. For
`V : Yᵒᵖ`, the category `StructuredArrow V w.op` of pairs `(U, ψ : V ⟶ w.op(U))` indexes a limit
cone whose point is `({}_sw M)(V)` and whose leg at `(U, ψ)` is `ranπ`, namely
`({}_sw M).map ψ` followed by the counit; that this cone is a limit is
`CategoryTheory.Functor.isPointwiseRightKanExtensionRanCounit`. Scalar multiplication by
`r : O_Y(V)` is defined by the universal property of that cone, from the endomorphisms of the
legs given by scalar multiplication by the images of `r` under the ring maps
`O_Y(V) ⟶ ({}_sw O_X)(V) ⟶ O_X(U)`, the first being `f^♯` and the second the corresponding leg
for `O_X`. The three compatibilities that make this work — that the legs form a cone, that the
ring-valued legs form a cone, and that `f^♯` is natural — are exactly what the cone condition,
the ring axioms and the semilinearity of the restriction maps of `f_* M` need.

Working with the legs of that cone rather than with
`CategoryTheory.Functor.ranObjObjIsoLimit` keeps the comparison with the functoriality of
`{}_sw` definitional: the identity `({}_sw M).map g ≫ ranπ (U, ψ) = ranπ (U, g ≫ ψ)` is
functoriality of `{}_sw M`, and it is what makes the restriction maps semilinear.

Since the module structure is carried by the right Kan extension itself,
`CategoryTheory.PresheafOfModules.ofPresheaf` applies, and the underlying presheaf of abelian
groups of the result is the right Kan extension by `ofPresheaf_presheaf`, an equality. The
direct image on sheaves of modules is then this construction on underlying presheaves of
modules, the sheaf condition being
`CategoryTheory.ran_isSheaf_of_isCocontinuous`, and the comparison of underlying sheaves of
abelian groups is an equality of functors.

The left adjoint is built in two steps, both at the level of presheaves of modules, and then
sheafified. First, for the *tautological* structure map `ranUnitRing`, where the presheaf of
rings on the source is the restriction `w^{-1}T` of the one on the target, the right Kan
extension adjunction of abelian presheaves is linear and lifts to presheaves of modules: the
unit and the counit are the abelian ones, their linearity being read off the legs, where the
tautological structure map cuts out the restriction maps of `T` (`scalarπ_ranUnitRing`), and the
two triangle identities are the abelian ones, the forgetful functor to abelian presheaves being
faithful. The left adjoint there is `PresheafOfModules.pushforward₀`, restriction along `w`.
Second, an arbitrary structure map `f^♯ : O_Y ⟶ {}_sw O_X` has an adjoint ring map
`structureMapRestrict : w^{-1}O_Y ⟶ O_X`, and the direct image for `f^♯` is the direct image for
the tautological structure map applied to the restriction of scalars along it: the two have the
same underlying presheaf of abelian groups and, since `f^♯` cuts out at the leg `(U, ψ)` the
restriction map of `O_Y` along `ψ` followed by `structureMapRestrict`
(`scalarπ_eq_structureMapRestrict`), the same module structure, so the identity of the right Kan
extension is an isomorphism of presheaves of modules
(`restrictScalarsStructureMapRestrictCompRanPushforwardIso`). Composing with the base change that
`PresheafOfModules.pullback` provides as the left adjoint of that restriction of scalars gives
`ranPushforwardAdjunction`. Base change needs the source site and the presheaves of rings to be
small in the universe of the module sections, which is
`PresheafOfModules.isRightAdjoint_pushforward_of_univLE` and is carried as `UnivLE` hypotheses;
nothing is assumed about the existence of an adjoint.

On sheaves the adjunction is that one composed with the sheafification of presheaves of modules
and restricted along the fully faithful inclusion of sheaves of modules into presheaves of
modules on the target site, which `CategoryTheory.Adjunction.restrictFullyFaithful` performs;
both comparison isomorphisms it asks for are the identity, the direct image of a sheaf of
modules being the presheaf-level direct image of its underlying presheaf of modules on the nose.
Sheafification needs `HasWeakSheafify` and `WEqualsLocallyBijective` for abelian sheaves on the
*source* site, again a condition on the site and the universe.

## References

* [Stacks Project, Tag 0FN3](https://stacks.math.columbia.edu/tag/0FN3), whose setting this is;
  the morphism of topoi attached to a cocontinuous functor is Stacks 00XO.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe v r v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

namespace Stacks.SheafOfModules

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y] (w : X ⥤ Y)

section Leg

variable {A : Type u₃} [Category.{v₃} A] {B : Type u₄} [Category.{v₄} B] (L : A ⥤ B)
  {H : Type*} [Category H] [∀ F : A ⥤ H, L.HasRightKanExtension F] (N : A ⥤ H)

/-- The leg at `(a, ψ : b ⟶ L(a))` of the limit cone computing the right Kan extension of `N`
along `L` at `b`: the restriction map of the Kan extension along `ψ`, followed by the counit. -/
def ranπ (b : B) (j : StructuredArrow b L) : (L.ran.obj N).obj b ⟶ N.obj j.right :=
  (L.ran.obj N).map j.hom ≫ (L.ranCounit.app N).app j.right

/-- Restricting along `f : b ⟶ b'` and taking the leg at `(a, ψ)` is the leg at `(a, f ≫ ψ)`:
functoriality of the Kan extension. -/
@[reassoc]
lemma ranπ_map {b b' : B} (f : b ⟶ b') (j : StructuredArrow b' L) :
    (L.ran.obj N).map f ≫ ranπ L N b' j = ranπ L N b ((StructuredArrow.map f).obj j) := by
  dsimp only [ranπ]
  rw [← Functor.map_comp_assoc]
  rfl

/-- The legs form a cone: the leg at `(a₁, ψ₁)` followed by `N` applied to a morphism
`(a₁, ψ₁) ⟶ (a₂, ψ₂)` is the leg at `(a₂, ψ₂)`. -/
@[reassoc]
lemma ranπ_naturality {b : B} {j₁ j₂ : StructuredArrow b L} (φ : j₁ ⟶ j₂) :
    ranπ L N b j₁ ≫ N.map φ.right = ranπ L N b j₂ := by
  have := ((Functor.RightExtension.mk (L.ran.obj N) (L.ranCounit.app N)).coneAt b).π.naturality φ
  simpa [ranπ] using this.symm

/-- The legs are natural in `N`. -/
@[reassoc]
lemma ranπ_map_functor {N₁ N₂ : A ⥤ H} (φ : N₁ ⟶ N₂) (b : B) (j : StructuredArrow b L) :
    (L.ran.map φ).app b ≫ ranπ L N₂ b j = ranπ L N₁ b j ≫ φ.app j.right := by
  have h : (L.ran.map φ).app (L.obj j.right) ≫ (L.ranCounit.app N₂).app j.right
      = (L.ranCounit.app N₁).app j.right ≫ φ.app j.right :=
    congr_app (L.ranCounit.naturality φ) j.right
  dsimp only [ranπ]
  rw [← NatTrans.naturality_assoc, Category.assoc, h]

/-- The cone of `ranπ` is a limit cone, the chosen right Kan extension being pointwise. -/
def ranIsLimit [L.HasPointwiseRightKanExtension N] (b : B) :
    IsLimit ((Functor.RightExtension.mk (L.ran.obj N) (L.ranCounit.app N)).coneAt b) :=
  L.isPointwiseRightKanExtensionRanCounit N b

/-- Two morphisms into the right Kan extension at `b` agree as soon as they agree on every
leg. -/
lemma ran_hom_ext [L.HasPointwiseRightKanExtension N] {b : B} {Z : H}
    {a₁ a₂ : Z ⟶ (L.ran.obj N).obj b}
    (h : ∀ j, a₁ ≫ ranπ L N b j = a₂ ≫ ranπ L N b j) : a₁ = a₂ :=
  (ranIsLimit L N b).hom_ext (fun j => h j)

/-- The leg at the identity arrow `(a, 𝟙 : L(a) ⟶ L(a))` is the counit at `a`. -/
lemma ranπ_mk_id (a : A) :
    ranπ L N (L.obj a) (StructuredArrow.mk (𝟙 (L.obj a))) = (L.ranCounit.app N).app a := by
  dsimp only [ranπ]
  rw [show (StructuredArrow.mk (𝟙 (L.obj a)) : StructuredArrow (L.obj a) L).hom = 𝟙 _ from rfl,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The unit of the right Kan extension adjunction, followed by the leg at `(a, ψ)` of the
right Kan extension of a restricted functor, is the restriction map along `ψ`. -/
@[reassoc]
lemma ranAdjunction_unit_app_ranπ (G : B ⥤ H) (b : B) (j : StructuredArrow b L) :
    ((L.ranAdjunction H).unit.app G).app b ≫ ranπ L (L ⋙ G) b j = G.map j.hom := by
  have hnat : ((L.ranAdjunction H).unit.app G).app b ≫ (L.ran.obj (L ⋙ G)).map j.hom
      = G.map j.hom ≫ ((L.ranAdjunction H).unit.app G).app (L.obj j.right) :=
    (((L.ranAdjunction H).unit.app G).naturality j.hom).symm
  dsimp only [ranπ]
  rw [← Category.assoc, hnat, Category.assoc,
    L.ranCounit_app_app_ranAdjunction_unit_app_app G j.right]
  exact Category.comp_id _

end Leg

section SMul

variable {Z : Type u₃} [Category.{v₃} Z] {R : Zᵒᵖ ⥤ RingCat.{r}}

/-- Scalar multiplication by a section of the presheaf of rings, as an endomorphism of the
underlying presheaf of abelian groups evaluated at an object. -/
def smulPresheaf (M : PresheafOfModules.{v} R) (U : Zᵒᵖ) (s : R.obj U) :
    M.presheaf.obj U ⟶ M.presheaf.obj U :=
  ((M.obj U).smul s).asHom

/-- The restriction maps of a presheaf of modules are semilinear. -/
@[reassoc]
lemma smulPresheaf_map (M : PresheafOfModules.{v} R) {U U' : Zᵒᵖ} (f : U ⟶ U') (s : R.obj U) :
    smulPresheaf M U s ≫ M.presheaf.map f
      = M.presheaf.map f ≫ smulPresheaf M U' ((R.map f).hom s) :=
  M.smul_map f s

/-- Scalar multiplication by `1` is the identity. -/
lemma smulPresheaf_one (M : PresheafOfModules.{v} R) (U : Zᵒᵖ) : smulPresheaf M U 1 = 𝟙 _ := by
  dsimp only [smulPresheaf]
  rw [map_one]
  rfl

/-- Scalar multiplication by a product is the composite of the two scalar multiplications. -/
lemma smulPresheaf_mul (M : PresheafOfModules.{v} R) (U : Zᵒᵖ) (s s' : R.obj U) :
    smulPresheaf M U (s * s') = smulPresheaf M U s' ≫ smulPresheaf M U s := by
  dsimp only [smulPresheaf]
  rw [map_mul]
  rfl

/-- Scalar multiplication by `0` is the zero morphism. -/
lemma smulPresheaf_zero (M : PresheafOfModules.{v} R) (U : Zᵒᵖ) : smulPresheaf M U 0 = 0 := by
  dsimp only [smulPresheaf]
  rw [map_zero]
  rfl

/-- Scalar multiplication is additive in the scalar. -/
lemma smulPresheaf_add (M : PresheafOfModules.{v} R) (U : Zᵒᵖ) (s s' : R.obj U) :
    smulPresheaf M U (s + s') = smulPresheaf M U s + smulPresheaf M U s' := by
  dsimp only [smulPresheaf]
  rw [map_add]
  rfl

/-- A morphism of presheaves of modules, read on underlying presheaves of abelian groups. -/
def presheafMap {M₁ M₂ : PresheafOfModules.{v} R} (φ : M₁ ⟶ M₂) : M₁.presheaf ⟶ M₂.presheaf :=
  (PresheafOfModules.toPresheaf R).map φ

/-- `presheafMap` takes the identity to the identity. -/
lemma presheafMap_id (M : PresheafOfModules.{v} R) : presheafMap (𝟙 M) = 𝟙 M.presheaf :=
  (PresheafOfModules.toPresheaf R).map_id M

/-- `presheafMap` takes a composite to the composite. -/
lemma presheafMap_comp {M₁ M₂ M₃ : PresheafOfModules.{v} R} (φ₁ : M₁ ⟶ M₂) (φ₂ : M₂ ⟶ M₃) :
    presheafMap (φ₁ ≫ φ₂) = presheafMap φ₁ ≫ presheafMap φ₂ :=
  (PresheafOfModules.toPresheaf R).map_comp φ₁ φ₂

/-- A morphism of presheaves of modules commutes with scalar multiplication. -/
@[reassoc]
lemma smulPresheaf_naturality {M₁ M₂ : PresheafOfModules.{v} R} (φ : M₁ ⟶ M₂) (U : Zᵒᵖ)
    (s : R.obj U) :
    smulPresheaf M₁ U s ≫ (presheafMap φ).app U
      = (presheafMap φ).app U ≫ smulPresheaf M₂ U s :=
  (ModuleCat.smul_naturality (φ.app U) s).symm

end SMul

section Presheaf

variable {S : Xᵒᵖ ⥤ RingCat.{r}} {T : Yᵒᵖ ⥤ RingCat.{r}}
  [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]
  (ψ : T ⟶ w.op.ran.obj S)

/-- The ring map `O_Y(V) ⟶ O_X(U)` attached to `(U, ψ : V ⟶ w.op(U))`: the structure map
`f^♯` followed by the leg of the Kan extension of the presheaf of rings. -/
def scalarπ (V : Yᵒᵖ) (j : StructuredArrow V w.op) : T.obj V ⟶ S.obj j.right :=
  ψ.app V ≫ ranπ w.op S V j

/-- The ring maps `scalarπ` form a cone. -/
lemma scalarπ_naturality {V : Yᵒᵖ} {j₁ j₂ : StructuredArrow V w.op} (φ : j₁ ⟶ j₂)
    (r : T.obj V) :
    (S.map φ.right).hom ((scalarπ w ψ V j₁).hom r) = (scalarπ w ψ V j₂).hom r := by
  have h : scalarπ w ψ V j₁ ≫ S.map φ.right = scalarπ w ψ V j₂ := by
    dsimp only [scalarπ]
    rw [Category.assoc, ranπ_naturality]
  exact congrArg (fun g => RingCat.Hom.hom g r) h

/-- The ring maps `scalarπ` are compatible with the restriction maps of the presheaf of rings,
by naturality of the structure map `f^♯`. -/
lemma scalarπ_map {V V' : Yᵒᵖ} (f : V ⟶ V') (j : StructuredArrow V' w.op) (r : T.obj V) :
    (scalarπ w ψ V ((StructuredArrow.map f).obj j)).hom r
      = (scalarπ w ψ V' j).hom ((T.map f).hom r) := by
  have h : scalarπ w ψ V ((StructuredArrow.map f).obj j) = T.map f ≫ scalarπ w ψ V' j := by
    dsimp only [scalarπ]
    rw [← ranπ_map, ← Category.assoc, ← ψ.naturality f, Category.assoc]
  exact congrArg (fun g => RingCat.Hom.hom g r) h

variable [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F]
  (M : PresheafOfModules.{v} S)

/-- The cone, on the diagram computing the right Kan extension at `V`, whose leg at `(U, ψ)` is
the leg of the limit cone followed by scalar multiplication by the image of `r` in `O_X(U)`. -/
def ranSMulCone (V : Yᵒᵖ) (r : T.obj V) : Cone (StructuredArrow.proj V w.op ⋙ M.presheaf) where
  pt := (w.op.ran.obj M.presheaf).obj V
  π :=
    { app := fun j =>
        ranπ w.op M.presheaf V j ≫ smulPresheaf M j.right ((scalarπ w ψ V j).hom r)
      naturality := fun _ _ φ => by
        dsimp
        rw [Category.id_comp]
        refine Eq.symm ?_
        rw [Category.assoc, smulPresheaf_map, ← Category.assoc,
          ranπ_naturality w.op M.presheaf φ, scalarπ_naturality w ψ φ] }

/-- **Scalar multiplication on the direct image.** Multiplication by `r : O_Y(V)` on the right
Kan extension at `V`, defined by the universal property of the limit cone from scalar
multiplication by the images of `r` in the rings `O_X(U)`. -/
def ranSMul (V : Yᵒᵖ) (r : T.obj V) :
    (w.op.ran.obj M.presheaf).obj V ⟶ (w.op.ran.obj M.presheaf).obj V :=
  (ranIsLimit w.op M.presheaf V).lift (ranSMulCone w ψ M V r)

/-- The defining property of `ranSMul`: on the leg at `(U, ψ)` it acts through the ring map
`O_Y(V) ⟶ O_X(U)`. -/
@[reassoc]
lemma ranSMul_π (V : Yᵒᵖ) (r : T.obj V) (j : StructuredArrow V w.op) :
    ranSMul w ψ M V r ≫ ranπ w.op M.presheaf V j
      = ranπ w.op M.presheaf V j ≫ smulPresheaf M j.right ((scalarπ w ψ V j).hom r) :=
  (ranIsLimit w.op M.presheaf V).fac _ j

/-- Scalar multiplication on the direct image at `V`, as a ring map from `O_Y(V)` to the
endomorphisms of the underlying abelian group. -/
def ranSMulRingHom (V : Yᵒᵖ) : T.obj V →+* End ((w.op.ran.obj M.presheaf).obj V) where
  toFun r := End.of (ranSMul w ψ M V r)
  map_one' := by
    refine End.ext ?_
    show ranSMul w ψ M V 1 = 𝟙 _
    refine ran_hom_ext w.op M.presheaf (fun j => ?_)
    rw [ranSMul_π, Category.id_comp, map_one, smulPresheaf_one, Category.comp_id]
  map_mul' r r' := by
    refine End.ext ?_
    show ranSMul w ψ M V (r * r') = ranSMul w ψ M V r' ≫ ranSMul w ψ M V r
    refine ran_hom_ext w.op M.presheaf (fun j => ?_)
    rw [ranSMul_π, Category.assoc, ranSMul_π, ← Category.assoc, ranSMul_π,
      Category.assoc, map_mul, smulPresheaf_mul]
  map_zero' := by
    refine End.ext ?_
    show ranSMul w ψ M V 0 = 0
    refine ran_hom_ext w.op M.presheaf (fun j => ?_)
    rw [ranSMul_π, map_zero, smulPresheaf_zero, Limits.comp_zero, Limits.zero_comp]
  map_add' r r' := by
    refine End.ext ?_
    show ranSMul w ψ M V (r + r') = ranSMul w ψ M V r + ranSMul w ψ M V r'
    refine ran_hom_ext w.op M.presheaf (fun j => ?_)
    rw [ranSMul_π, Preadditive.add_comp, ranSMul_π, ranSMul_π, map_add, smulPresheaf_add,
      Preadditive.comp_add]

/-- The `O_Y(V)`-module structure on the right Kan extension at `V` cut out by `f^♯`. -/
@[instance_reducible]
def ranModule (V : Yᵒᵖ) : Module (T.obj V) ((w.op.ran.obj M.presheaf).obj V) :=
  inferInstanceAs (Module _ (ModuleCat.mkOfSMul' (ranSMulRingHom w ψ M V)))

/-- The restriction maps of the right Kan extension are semilinear for `ranSMul`. -/
@[reassoc]
lemma ranSMul_ran_map {V V' : Yᵒᵖ} (f : V ⟶ V') (r : T.obj V) :
    ranSMul w ψ M V r ≫ (w.op.ran.obj M.presheaf).map f
      = (w.op.ran.obj M.presheaf).map f ≫ ranSMul w ψ M V' ((T.map f).hom r) := by
  refine ran_hom_ext w.op M.presheaf (fun j => ?_)
  rw [Category.assoc, ranπ_map, ranSMul_π, Category.assoc, ranSMul_π, ← Category.assoc,
    ranπ_map, scalarπ_map]
  rfl

/-- **The direct image of a presheaf of modules** along the morphism of topoi attached to a
cocontinuous functor of sites: the right Kan extension of the underlying presheaf of abelian
groups, with the `O_Y`-module structure cut out of its `{}_sw O_X`-module structure by
`f^♯`. -/
def ranObj : PresheafOfModules.{v} T :=
  @PresheafOfModules.ofPresheaf _ _ T (w.op.ran.obj M.presheaf) (ranModule w ψ M)
    (fun _ _ f r m => ConcreteCategory.congr_hom (ranSMul_ran_map w ψ M f r) m)

/-- The underlying presheaf of abelian groups of the direct image is the right Kan extension. -/
lemma ranObj_presheaf : (ranObj w ψ M).presheaf = w.op.ran.obj M.presheaf := rfl

end Presheaf

section Functor

variable {S : Xᵒᵖ ⥤ RingCat.{r}} {T : Yᵒᵖ ⥤ RingCat.{r}}
  [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F]
  (ψ : T ⟶ w.op.ran.obj S)

/-- The right Kan extension of a morphism of presheaves of abelian groups is linear for the
module structures of `ranObj`. -/
lemma ranSMul_naturality {M₁ M₂ : PresheafOfModules.{v} S} (φ : M₁ ⟶ M₂) (V : Yᵒᵖ)
    (r : T.obj V) :
    ranSMul w ψ M₁ V r ≫ (w.op.ran.map (presheafMap φ)).app V
      = (w.op.ran.map (presheafMap φ)).app V ≫ ranSMul w ψ M₂ V r := by
  refine ran_hom_ext w.op M₂.presheaf (fun j => ?_)
  rw [Category.assoc, Category.assoc, ranπ_map_functor, ranSMul_π_assoc,
    smulPresheaf_naturality, ranSMul_π, ranπ_map_functor_assoc]

/-- The direct image of a morphism of presheaves of modules: the right Kan extension of the
morphism of underlying presheaves of abelian groups. -/
def ranMap {M₁ M₂ : PresheafOfModules.{v} S} (φ : M₁ ⟶ M₂) : ranObj w ψ M₁ ⟶ ranObj w ψ M₂ :=
  PresheafOfModules.homMk (w.op.ran.map (presheafMap φ))
    (fun V r m => ConcreteCategory.congr_hom (ranSMul_naturality w ψ φ V r) m)

/-- `ranMap` takes the identity to the identity. -/
lemma ranMap_id (M : PresheafOfModules.{v} S) : ranMap w ψ (𝟙 M) = 𝟙 _ := by
  refine (PresheafOfModules.toPresheaf T).map_injective ?_
  show w.op.ran.map (presheafMap (𝟙 M)) = 𝟙 (w.op.ran.obj M.presheaf)
  rw [presheafMap_id, CategoryTheory.Functor.map_id]

/-- `ranMap` takes a composite to the composite. -/
lemma ranMap_comp {M₁ M₂ M₃ : PresheafOfModules.{v} S} (φ₁ : M₁ ⟶ M₂) (φ₂ : M₂ ⟶ M₃) :
    ranMap w ψ (φ₁ ≫ φ₂) = ranMap w ψ φ₁ ≫ ranMap w ψ φ₂ := by
  refine (PresheafOfModules.toPresheaf T).map_injective ?_
  show w.op.ran.map (presheafMap (φ₁ ≫ φ₂))
      = w.op.ran.map (presheafMap φ₁) ≫ w.op.ran.map (presheafMap φ₂)
  rw [presheafMap_comp, CategoryTheory.Functor.map_comp]

/-- **The direct image of presheaves of modules** along the morphism of topoi attached to a
cocontinuous functor of sites. -/
def ranPushforward : PresheafOfModules.{v} S ⥤ PresheafOfModules.{v} T where
  obj M := ranObj w ψ M
  map φ := ranMap w ψ φ
  map_id M := ranMap_id w ψ M
  map_comp φ₁ φ₂ := ranMap_comp w ψ φ₁ φ₂

/-- On underlying presheaves of abelian groups, the direct image of presheaves of modules is
right Kan extension along `w.op`. -/
lemma ranPushforward_comp_toPresheaf :
    ranPushforward.{v} w ψ ⋙ PresheafOfModules.toPresheaf T
      = PresheafOfModules.toPresheaf S ⋙ w.op.ran := rfl

end Functor

section PresheafAdjunction

variable [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F]
  (T : Yᵒᵖ ⥤ RingCat.{r})

/-- The **tautological structure map** `T ⟶ {}_sw (w^{-1}T)` for a presheaf of rings `T` on the
target site: the unit of the right Kan extension adjunction, which makes the restriction of `T`
along `w` into the structure presheaf of rings of the source. -/
def ranUnitRing : T ⟶ w.op.ran.obj (w.op ⋙ T) :=
  (w.op.ranAdjunction RingCat.{r}).unit.app T

omit [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F] in
/-- The ring maps that the tautological structure map cuts out at the legs are the restriction
maps of `T`. -/
lemma scalarπ_ranUnitRing (V : Yᵒᵖ) (j : StructuredArrow V w.op) :
    scalarπ w (ranUnitRing w T) V j = T.map j.hom :=
  ranAdjunction_unit_app_ranπ w.op T V j

/-- The leg at `(U, ψ)` of the scalar multiplication of the direct image for the tautological
structure map acts through the restriction map of `T` along `ψ`. -/
private lemma ranSMul_ranUnitRing_π (P : PresheafOfModules.{v} (w.op ⋙ T)) (V : Yᵒᵖ) (t : T.obj V)
    (j : StructuredArrow V w.op) :
    ranSMul w (ranUnitRing w T) P V t ≫ ranπ w.op P.presheaf V j
      = ranπ w.op P.presheaf V j ≫ smulPresheaf P j.right ((T.map j.hom).hom t) := by
  rw [ranSMul_π, scalarπ_ranUnitRing]

/-- The unit of the right Kan extension adjunction on underlying presheaves of abelian groups,
read as a morphism into the underlying presheaf of the direct image of the restriction. -/
def ranUnitPresheaf (N : PresheafOfModules.{v} T) :
    N.presheaf ⟶ w.op.ran.obj ((PresheafOfModules.pushforward₀.{v} w T).obj N).presheaf :=
  (w.op.ranAdjunction AddCommGrpCat.{v}).unit.app N.presheaf

/-- The unit of the right Kan extension adjunction on underlying presheaves of abelian groups is
linear: it carries scalar multiplication by a section of `T` to the scalar multiplication of the
direct image for the tautological structure map. -/
lemma ranSMul_ranUnitPresheaf (N : PresheafOfModules.{v} T) (V : Yᵒᵖ) (r : T.obj V) :
    smulPresheaf N V r ≫ (ranUnitPresheaf w T N).app V
      = (ranUnitPresheaf w T N).app V ≫
        ranSMul w (ranUnitRing w T) ((PresheafOfModules.pushforward₀.{v} w T).obj N) V r := by
  refine ran_hom_ext w.op ((PresheafOfModules.pushforward₀.{v} w T).obj N).presheaf (fun j => ?_)
  have h₁ : (ranUnitPresheaf w T N).app V ≫
      ranπ w.op ((PresheafOfModules.pushforward₀.{v} w T).obj N).presheaf V j
        = N.presheaf.map j.hom :=
    ranAdjunction_unit_app_ranπ w.op N.presheaf V j
  simp only [Category.assoc]
  rw [ranSMul_ranUnitRing_π, h₁, ← Category.assoc, h₁]
  exact smulPresheaf_map N j.hom r

/-- The counit of the right Kan extension adjunction on underlying presheaves of abelian groups
is linear over the restriction of `T` along `w`. -/
lemma ranSMul_ranCounit (P : PresheafOfModules.{v} (w.op ⋙ T)) (U : Xᵒᵖ)
    (t : T.obj (w.op.obj U)) :
    ranSMul w (ranUnitRing w T) P (w.op.obj U) t ≫ (w.op.ranCounit.app P.presheaf).app U
      = (w.op.ranCounit.app P.presheaf).app U ≫ smulPresheaf P U t := by
  have h := ranSMul_ranUnitRing_π w T P (w.op.obj U) t (StructuredArrow.mk (𝟙 (w.op.obj U)))
  rw [ranπ_mk_id] at h
  rw [h, show (StructuredArrow.mk (𝟙 (w.op.obj U)) : StructuredArrow (w.op.obj U) w.op).hom
    = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

/-- The unit of the adjunction between restriction along `w` and the direct image of presheaves
of modules for the tautological structure map. -/
def ranPushforwardUnit :
    𝟭 (PresheafOfModules.{v} T) ⟶
      PresheafOfModules.pushforward₀.{v} w T ⋙ ranPushforward.{v} w (ranUnitRing w T) where
  app N := PresheafOfModules.homMk (ranUnitPresheaf w T N)
    (fun V r m => ConcreteCategory.congr_hom (ranSMul_ranUnitPresheaf w T N V r) m)
  naturality _ _ g := (PresheafOfModules.toPresheaf T).map_injective
    ((w.op.ranAdjunction AddCommGrpCat.{v}).unit.naturality (presheafMap g))

/-- The counit of the adjunction between restriction along `w` and the direct image of
presheaves of modules for the tautological structure map. -/
def ranPushforwardCounit :
    ranPushforward.{v} w (ranUnitRing w T) ⋙ PresheafOfModules.pushforward₀.{v} w T ⟶
      𝟭 (PresheafOfModules.{v} (w.op ⋙ T)) where
  app P := PresheafOfModules.homMk (w.op.ranCounit.app P.presheaf)
    (fun U t m => ConcreteCategory.congr_hom (ranSMul_ranCounit w T P U t) m)
  naturality _ _ g := (PresheafOfModules.toPresheaf (w.op ⋙ T)).map_injective
    (w.op.ranCounit.naturality (presheafMap g))

/-- **Restriction of presheaves of modules along `w` is left adjoint to the direct image** of
presheaves of modules for the tautological structure map `ranUnitRing`: the right Kan extension
adjunction on underlying presheaves of abelian groups is linear. -/
@[sga "4 IV 11.2.2" "special case"]
def pushforward₀RanPushforwardAdjunction :
    PresheafOfModules.pushforward₀.{v} w T ⊣ ranPushforward.{v} w (ranUnitRing w T) where
  unit := ranPushforwardUnit w T
  counit := ranPushforwardCounit w T
  left_triangle_components N :=
    (PresheafOfModules.toPresheaf (w.op ⋙ T)).map_injective
      (w.op.ranCounit_app_whiskerLeft_ranAdjunction_unit_app N.presheaf)
  right_triangle_components P := by
    refine (PresheafOfModules.toPresheaf T).map_injective ?_
    have h := (w.op.ranAdjunction AddCommGrpCat.{v}).right_triangle_components P.presheaf
    rw [Functor.ranAdjunction_counit] at h
    exact h

variable {S : Xᵒᵖ ⥤ RingCat.{r}} (ψ : T ⟶ w.op.ran.obj S)

omit [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F] in
/-- The **structure map read on the source site**: the ring map `w^{-1}O_Y ⟶ O_X` adjoint to
`f^♯ : O_Y ⟶ {}_sw O_X` under the right Kan extension adjunction. -/
def structureMapRestrict : w.op ⋙ T ⟶ S :=
  Functor.whiskerLeft w.op ψ ≫ w.op.ranCounit.app S

/-- Restriction of scalars along `structureMapRestrict`: a presheaf of `O_X`-modules read as a
presheaf of modules over the restriction of `O_Y` along `w`. -/
abbrev restrictScalarsStructureMapRestrict :
    PresheafOfModules.{v} S ⥤ PresheafOfModules.{v} (w.op ⋙ T) :=
  PresheafOfModules.pushforward.{v} (F := 𝟭 X) (structureMapRestrict w T ψ)

omit [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F] in
/-- The ring map `O_Y(V) ⟶ O_X(U)` that `f^♯` cuts out at `(U, ψ : V ⟶ w.op(U))` factors as the
restriction map of `O_Y` along `ψ` followed by `structureMapRestrict`. -/
lemma scalarπ_eq_structureMapRestrict (V : Yᵒᵖ) (j : StructuredArrow V w.op) :
    scalarπ w ψ V j = T.map j.hom ≫ (structureMapRestrict w T ψ).app j.right := by
  have hnat : T.map j.hom ≫ ψ.app (w.op.obj j.right)
      = ψ.app V ≫ (w.op.ran.obj S).map j.hom := ψ.naturality j.hom
  dsimp only [scalarπ, ranπ, structureMapRestrict, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← Category.assoc (ψ.app V), ← hnat, Category.assoc]

/-- The module structure of the direct image for `f^♯` is the module structure of the direct
image for the tautological structure map on the restriction of scalars along
`structureMapRestrict`. -/
lemma ranSMul_restrictScalarsStructureMapRestrict (M : PresheafOfModules.{v} S) (V : Yᵒᵖ)
    (r : T.obj V) :
    ranSMul w (ranUnitRing w T) ((restrictScalarsStructureMapRestrict.{v} w T ψ).obj M) V r
      = ranSMul w ψ M V r := by
  refine ran_hom_ext w.op ((restrictScalarsStructureMapRestrict.{v} w T ψ).obj M).presheaf
    (fun j => ?_)
  rw [ranSMul_ranUnitRing_π]
  have h₁ := ranSMul_π w ψ M V r j
  rw [scalarπ_eq_structureMapRestrict] at h₁
  exact h₁.symm

/-- **The direct image of presheaves of modules for a structure map `f^♯` is the direct image
for the tautological structure map, after restriction of scalars** along the adjoint ring map
`structureMapRestrict`: the two have the same underlying presheaf of abelian groups and, by
`Stacks.SheafOfModules.ranSMul_restrictScalarsStructureMapRestrict`, the same module structure. -/
def restrictScalarsStructureMapRestrictCompRanPushforwardIso :
    restrictScalarsStructureMapRestrict.{v} w T ψ ⋙ ranPushforward.{v} w (ranUnitRing w T)
      ≅ ranPushforward.{v} w ψ :=
  NatIso.ofComponents
    (fun M ↦
      { hom := PresheafOfModules.homMk (𝟙 (w.op.ran.obj M.presheaf))
          (fun V r m ↦ ConcreteCategory.congr_hom
            (ranSMul_restrictScalarsStructureMapRestrict w T ψ M V r) m)
        inv := PresheafOfModules.homMk (𝟙 (w.op.ran.obj M.presheaf))
          (fun V r m ↦ ConcreteCategory.congr_hom
            (ranSMul_restrictScalarsStructureMapRestrict w T ψ M V r).symm m)
        hom_inv_id := rfl
        inv_hom_id := rfl })
    (fun _ ↦ rfl)

variable [UnivLE.{r, v}] [UnivLE.{v₁, v}] [UnivLE.{u₁, v}]

/-- Restriction of scalars along `structureMapRestrict` has a left adjoint, namely base change;
this is `PresheafOfModules.isRightAdjoint_pushforward_of_univLE`, and it needs only that the
source site and the presheaves of rings be small in the universe of the module sections. -/
instance isRightAdjoint_restrictStructureMap :
    (restrictScalarsStructureMapRestrict.{v} w T ψ).IsRightAdjoint :=
  PresheafOfModules.isRightAdjoint_pushforward_of_univLE.{v} (F := 𝟭 X) (R := S)
    (S := w.op ⋙ T) (structureMapRestrict w T ψ)

/-- **The direct image of presheaves of modules along a cocontinuous functor of sites has a left
adjoint**: restriction along `w`, followed by base change along the adjoint ring map
`structureMapRestrict`. This is the presheaf-level form of `f^* = O_X ⊗_{f^{-1}O_Y} f^{-1}`. -/
def ranPushforwardAdjunction :
    PresheafOfModules.pushforward₀.{v} w T ⋙
        PresheafOfModules.pullback.{v} (F := 𝟭 X) (structureMapRestrict w T ψ) ⊣
      ranPushforward.{v} w ψ :=
  ((pushforward₀RanPushforwardAdjunction w T).comp
    (PresheafOfModules.pullbackPushforwardAdjunction.{v} (F := 𝟭 X)
      (structureMapRestrict w T ψ))).ofNatIsoRight
    (restrictScalarsStructureMapRestrictCompRanPushforwardIso w T ψ)

/-- The direct image of presheaves of modules along a cocontinuous functor of sites is a right
adjoint. -/
instance isRightAdjoint_ranPushforward : (ranPushforward.{v} w ψ).IsRightAdjoint :=
  (ranPushforwardAdjunction w T ψ).isRightAdjoint

end PresheafAdjunction

section Sheaf

variable {JX : GrothendieckTopology X} {JY : GrothendieckTopology Y} [w.IsCocontinuous JX JY]
  [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F]
  {OX : Sheaf JX RingCat.{r}} {OY : Sheaf JY RingCat.{r}}
  (fSharp : OY ⟶ (w.sheafPushforwardCocontinuous RingCat.{r} JX JY).obj OX)

/-- The structure map `f^♯ : O_Y ⟶ {}_sw O_X` read on underlying presheaves of rings. -/
def structureMapPresheaf : OY.obj ⟶ w.op.ran.obj OX.obj := fSharp.hom

/-- **The direct image of sheaves of modules** along the morphism of topoi `f` attached to a
cocontinuous functor of sites `w : X ⥤ Y` (Stacks 00XO), for a structure map
`f^♯ : O_Y ⟶ {}_sw O_X` of sheaves of rings: the functor `f_* : Mod(O_X) ⥤ Mod(O_Y)` whose
underlying sheaf of abelian groups is the direct image `{}_sw` of the underlying sheaf of
abelian groups, carrying the `O_Y`-action that `f^♯` cuts out of the `{}_sw O_X`-action. -/
@[sga "4 III 2.4" "special case"]
def pushforwardCocontinuous : _root_.SheafOfModules.{v} OX ⥤ _root_.SheafOfModules.{v} OY where
  obj M :=
    { val := ranObj w (structureMapPresheaf w fSharp) M.val
      isSheaf := CategoryTheory.ran_isSheaf_of_isCocontinuous (G := w) (K := JY)
        (A := AddCommGrpCat.{v}) ((_root_.SheafOfModules.toSheaf.{v} OX).obj M) }
  map φ := { val := ranMap w (structureMapPresheaf w fSharp) φ.val }
  map_id M := _root_.SheafOfModules.hom_ext
    (ranMap_id w (structureMapPresheaf w fSharp) M.val)
  map_comp φ₁ φ₂ := _root_.SheafOfModules.hom_ext
    (ranMap_comp w (structureMapPresheaf w fSharp) φ₁.val φ₂.val)

/-- The underlying sheaf of abelian groups of the direct image of sheaves of modules along a
cocontinuous functor of sites is the direct image `{}_sw` of the underlying sheaf of abelian
groups, as an equality of functors. -/
lemma pushforwardCocontinuous_comp_toSheaf :
    pushforwardCocontinuous.{v} w fSharp ⋙ _root_.SheafOfModules.toSheaf.{v} OY
      = _root_.SheafOfModules.toSheaf.{v} OX ⋙
        w.sheafPushforwardCocontinuous AddCommGrpCat.{v} JX JY := rfl

variable [UnivLE.{r, v}] [UnivLE.{v₁, v}] [UnivLE.{u₁, v}]
  [HasWeakSheafify JX AddCommGrpCat.{v}] [JX.WEqualsLocallyBijective AddCommGrpCat.{v}]

end Sheaf

end Stacks.SheafOfModules

end
