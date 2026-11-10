module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceAdjunctions
import StacksCore.Tactic.StacksAttribute

/-!
# The objectwise formula for extension from a slice

Let `O` be a presheaf of rings on a category `C` and let `U` be an object of `C`. Extension
of presheaves of modules from the slice `C/U`, the functor `j_{U!}` of Stacks 03EJ, is
computed objectwise by a direct sum: the sections of `j_{U!} G` over `V` are
`⨁_{φ : V ⟶ U} G(V →^φ U)`, and the restriction along `f : V ⟶ W` sends the summand indexed
by `φ : W ⟶ U` into the one indexed by `f ≫ φ`.

## Main definitions

* `Stacks.Sites.OverModules.extensionFormula`: the direct sum occurring in the formula.
* `Stacks.Sites.OverModules.extensionFormulaMap`: its restriction map.

## Main results

* `Stacks.Sites.OverModules.extensionObjLinearEquivDirectSum`: a family of linear
  equivalences identifying the sections of `j_{U!} G` with those direct sums, together with
  the equation saying that the family commutes with every restriction map.

## Implementation notes

The formula is stated for an arbitrary realization `A` of the adjunctions of Stacks 03EJ,
`Stacks.Sites.OverModules.PresheafModuleAdjunctionsOver`, so it is an existential over the
family of equivalences, and the accompanying naturality equation pins the family down.

The summands are indexed by `φ : V ⟶ U` through `Over.mk φ`, so a restriction along `f` lands in
the summand indexed by `f ≫ φ` only up to that composition; `extensionFormulaMap_of_hom` takes
the target index and the equation `f ≫ ψ = φ` as separate arguments. The index family of the
direct sum is named, as `extensionFormulaSummands`, so that the family `β` of
`DirectSum.toAddMonoid_of` and `DirectSum.lof_eq_of` is determined at an index of the form
`f ≫ φ`. The `DecidableEq` instance on the index type is fixed as `Classical.decEq`. The summand
modules are spelled with the scalars `O.obj (op V)` through the semilinear restriction maps
`PresheafOfModules.restrictₛₗ`, since the module and ring universes of `G` are independent of the
site universes.

## Universes

The declarations up to `extensionFormulaInclusion` take the modules of `G` in `Type (max v m)`
for a free `m`: the sum is indexed by `V ⟶ U`, a type in the morphism universe `v` of the site,
so the universe `u` of its objects does not enter. This covers sites whose objects lie above
their modules, such as `AlgebraicGeometry.RingedSite.{u + 1, u, u}`.

From `extensionFormulaCoprodEquiv` on, the sums are compared with `extensionPresheaf`, whose
colimit is indexed by a comma category built from the objects of `C`; its modules lie in
`Type (max u v m)`, and these declarations use the ones above with `max u m` in place of `m`.

## References

* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w m

namespace Stacks.Sites.OverModules

variable {C : Type u} [Category.{v} C]

section ExtensionFormula

attribute [local instance] Classical.decEq

/-- The family of modules indexed by the arrows `φ : V ⟶ U`, given by `G (V →^φ U)`, whose direct
sum is the value of the extension formula at `V`. -/
abbrev extensionFormulaSummands (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)
    (G : PresheafOfModules.{max v m} (overRingPresheaf O U)) (V : C) :
    (V ⟶ U) → Type (max v m) :=
  fun φ ↦ G.obj (op (Over.mk φ))

/-- The objectwise direct sum in the formula for extension from `C/U`. -/
abbrev extensionFormula (O : Cᵒᵖ ⥤ RingCat.{w}) (U V : C)
    (G : PresheafOfModules.{max v m} (overRingPresheaf O U)) :=
  DirectSum (V ⟶ U) (extensionFormulaSummands.{v, u, w, m} O U G V)

/-- The restriction of a single summand: the summand indexed by `ψ : W ⟶ U` restricts along
`f : V ⟶ W` into the summand indexed by `f ≫ ψ`. -/
noncomputable def extensionFormulaSummandRestriction (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)
    (G : PresheafOfModules.{max v m} (overRingPresheaf O U))
    {V W : C} (f : V ⟶ W) (ψ : W ⟶ U) :
    G.obj (op (Over.mk ψ)) →+ extensionFormula.{v, u, w, m} O U V G :=
  (DirectSum.of (extensionFormulaSummands.{v, u, w, m} O U G V) (f ≫ ψ)).comp
    (G.map (Over.homMk f : Over.mk (f ≫ ψ) ⟶ Over.mk ψ).op).hom.toAddMonoidHom

/-- The restriction map on the direct sums in the extension formula. A summand indexed by
`ψ : W ⟶ U` is sent to the summand indexed by `f ≫ ψ : V ⟶ U`. -/
noncomputable def extensionFormulaMap (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)
    (G : PresheafOfModules.{max v m} (overRingPresheaf O U))
    {V W : C} (f : V ⟶ W) :
    extensionFormula.{v, u, w, m} O U W G →+
      extensionFormula.{v, u, w, m} O U V G :=
  DirectSum.toAddMonoid (extensionFormulaSummandRestriction.{v, u, w, m} O U G f)

/-- The restriction map on a single summand. -/
theorem extensionFormulaMap_of (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)
    (G : PresheafOfModules.{max v m} (overRingPresheaf O U))
    {V W : C} (f : V ⟶ W) (ψ : W ⟶ U) (y : G.obj (op (Over.mk ψ))) :
    extensionFormulaMap.{v, u, w, m} O U G f
        (DirectSum.of (extensionFormulaSummands.{v, u, w, m} O U G W) ψ y) =
      extensionFormulaSummandRestriction.{v, u, w, m} O U G f ψ y :=
  DirectSum.toAddMonoid_of
    (β := extensionFormulaSummands.{v, u, w, m} O U G W)
    (extensionFormulaSummandRestriction.{v, u, w, m} O U G f) ψ y

/-- The restriction map on a single summand, with the target index `φ` and the equation
`f ≫ ψ = φ` identifying it given as separate arguments. -/
theorem extensionFormulaMap_of_hom (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)
    (G : PresheafOfModules.{max v m} (overRingPresheaf O U))
    {V W : C} (f : V ⟶ W) (φ : V ⟶ U) (ψ : W ⟶ U) (h : f ≫ ψ = φ)
    (y : G.obj (op (Over.mk ψ))) :
    extensionFormulaMap.{v, u, w, m} O U G f
        (DirectSum.of (extensionFormulaSummands.{v, u, w, m} O U G W) ψ y) =
      DirectSum.of (extensionFormulaSummands.{v, u, w, m} O U G V) φ
        (G.restrictₛₗ (Over.homMk f h : Over.mk φ ⟶ Over.mk ψ).op y) := by
  subst h
  exact extensionFormulaMap_of.{v, u, w, m} O U G f ψ y

/-- The extension-formula transition map at the identity is the identity. -/
public lemma extensionFormulaMap_id (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)
    (G : PresheafOfModules.{max v m} (overRingPresheaf O U)) (V : C)
    (x : extensionFormula.{v, u, w, m} O U V G) :
    extensionFormulaMap.{v, u, w, m} O U G (𝟙 V) x = x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of φ y =>
      rw [extensionFormulaMap_of_hom O U G (𝟙 V) φ φ (Category.id_comp φ)]
      have h : (Over.homMk (𝟙 V) (Category.id_comp φ) : Over.mk φ ⟶ Over.mk φ) = 𝟙 _ := by
        ext; rfl
      rw [h, op_id]
      congr 1
      simp

/-- The extension-formula transition maps compose. -/
public lemma extensionFormulaMap_comp (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)
    (G : PresheafOfModules.{max v m} (overRingPresheaf O U))
    {V W X : C} (f : V ⟶ W) (g : W ⟶ X)
    (x : extensionFormula.{v, u, w, m} O U X G) :
    extensionFormulaMap.{v, u, w, m} O U G f
      (extensionFormulaMap.{v, u, w, m} O U G g x) =
      extensionFormulaMap.{v, u, w, m} O U G (f ≫ g) x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of φ y =>
      rw [extensionFormulaMap_of_hom O U G g (g ≫ φ) φ rfl,
        extensionFormulaMap_of_hom O U G f (f ≫ g ≫ φ) (g ≫ φ) rfl,
        extensionFormulaMap_of_hom O U G (f ≫ g) (f ≫ g ≫ φ) φ (Category.assoc f g φ)]
      congr 1
      exact (G.map_comp_apply
        (Over.homMk g : Over.mk (g ≫ φ) ⟶ Over.mk φ).op
        (Over.homMk f : Over.mk (f ≫ g ≫ φ) ⟶ Over.mk (g ≫ φ)).op y).symm

/-- The direct sums of the extension formula, assembled into a presheaf of `O`-modules. -/
public noncomputable def extensionFormulaObject (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)
    (G : PresheafOfModules.{max v m} (overRingPresheaf O U)) :
    PresheafOfModules.{max v m} O := by
  refine PresheafOfModules.ofPresheaf
    { obj := fun X => AddCommGrpCat.of (extensionFormula.{v, u, w, m} O U X.unop G)
      map := fun {X Y} f => AddCommGrpCat.ofHom
        (extensionFormulaMap.{v, u, w, m} O U G f.unop)
      map_id := ?_
      map_comp := ?_ }
    ?_
  · exact fun X ↦ AddCommGrpCat.hom_ext <| AddMonoidHom.ext <|
      extensionFormulaMap_id.{v, u, w, m} O U G X.unop
  · refine fun f g ↦ AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun x ↦ ?_
    simpa [ConcreteCategory.comp_apply, unop_comp] using
      (extensionFormulaMap_comp.{v, u, w, m} O U G g.unop f.unop x).symm
  · intro X Y f r x
    change extensionFormulaMap.{v, u, w, m} O U G f.unop (r • x) =
      O.map f r • extensionFormulaMap.{v, u, w, m} O U G f.unop x
    induction x using DirectSum.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | of φ y =>
        rw [← DirectSum.of_smul, extensionFormulaMap_of_hom O U G f.unop (f.unop ≫ φ) φ rfl,
          extensionFormulaMap_of_hom O U G f.unop (f.unop ≫ φ) φ rfl, ← DirectSum.of_smul]
        congr 1
        exact (G.restrictₛₗ
          (Over.homMk f.unop rfl : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ).op).map_smulₛₗ r y

/-- The inclusion of `G` into the restriction of the formula object, given over `φ : V ⟶ U`
by the inclusion of the summand indexed by `φ`. -/
public noncomputable def extensionFormulaInclusion (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)
    (G : PresheafOfModules.{max v m} (overRingPresheaf O U)) :
    G ⟶ (PresheafOfModules.pushforward₀ (Over.forget U) O).obj
      (extensionFormulaObject.{v, u, w, m} O U G) where
  app X := ModuleCat.ofHom
    (DirectSum.lof _ _ (fun φ ↦ G.obj (op (Over.mk φ))) X.unop.hom)
  naturality {X Y} f := by
    ext x
    exact (extensionFormulaMap_of_hom.{v, u, w, m} O U G f.unop.left
      Y.unop.hom X.unop.hom (Over.w f.unop) x).symm

/-- The sections of the coproduct presheaf `j_{U!} G` over `V`, identified with the direct
sum of the same summands. -/
noncomputable def extensionFormulaCoprodEquiv (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)
    (G : PresheafOfModules.{max u v m} (overRingPresheaf O U)) (V : C) :
    (extensionPresheaf.{v, u, w, max u v m} O U G).obj (op V) ≃ₗ[O.obj (op V)]
      extensionFormula.{v, u, w, max u m} O U V G :=
  (ModuleCat.coprodIsoDirectSum (extensionSummands O U G (op V))).toLinearEquiv

/-- The identification sends the inclusion of the summand indexed by `φ` to the inclusion of
the summand indexed by `φ`. -/
lemma extensionFormulaCoprodEquiv_ι (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)
    (G : PresheafOfModules.{max u v m} (overRingPresheaf O U))
    (V : C) (φ : V ⟶ U) (y : G.obj (op (Over.mk φ))) :
    extensionFormulaCoprodEquiv.{v, u, w, m} O U G V
        (Limits.Sigma.ι (extensionSummands O U G (op V)) φ y) =
      DirectSum.of (extensionFormulaSummands.{v, u, w, max u m} O U G V) φ y := by
  rw [← DirectSum.lof_eq_of (O.obj (op V))
    (M := extensionFormulaSummands.{v, u, w, max u m} O U G V)]
  exact ModuleCat.ι_coprodIsoDirectSum_hom_apply (extensionSummands O U G (op V)) φ y

/-- The restriction map of the coproduct presheaf along `f`, read through the identification
with the direct sums. -/
noncomputable def extensionFormulaCoprodRestriction (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)
    (G : PresheafOfModules.{max u v m} (overRingPresheaf O U)) {V W : C} (f : V ⟶ W) :
    extensionFormula.{v, u, w, max u m} O U W G →+ extensionFormula.{v, u, w, max u m} O U V G :=
  ((extensionFormulaCoprodEquiv.{v, u, w, m} O U G V).toLinearMap.toAddMonoidHom.comp
    (((extensionPresheaf.{v, u, w, max u v m} O U G).map f.op).hom.toAddMonoidHom.comp
      (extensionFormulaCoprodEquiv.{v, u, w, m} O U G W).symm.toLinearMap.toAddMonoidHom))

/-- The identification carries the restriction maps of the coproduct presheaf to the
restriction maps of the extension formula. -/
lemma extensionFormulaCoprodRestriction_eq (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)
    (G : PresheafOfModules.{max u v m} (overRingPresheaf O U)) {V W : C} (f : V ⟶ W) :
    extensionFormulaCoprodRestriction.{v, u, w, m} O U G f =
      extensionFormulaMap.{v, u, w, max u m} O U G f := by
  refine DirectSum.addHom_ext fun φ y ↦ ?_
  change extensionFormulaCoprodEquiv.{v, u, w, m} O U G V
      ((extensionPresheaf.{v, u, w, max u v m} O U G).map f.op
        ((extensionFormulaCoprodEquiv.{v, u, w, m} O U G W).symm
          (DirectSum.of (extensionFormulaSummands.{v, u, w, max u m} O U G W) φ y))) = _
  rw [(extensionFormulaCoprodEquiv.{v, u, w, m} O U G W).symm_apply_eq.2
    (extensionFormulaCoprodEquiv_ι.{v, u, w, m} O U G W φ y).symm]
  change extensionFormulaCoprodEquiv.{v, u, w, m} O U G V
      (extensionRestriction O U G f.op
        (Limits.Sigma.ι (extensionSummands O U G (op W)) φ y)) = _
  rw [extensionRestriction_ι_apply O U G f.op φ (f ≫ φ) rfl,
    extensionFormulaCoprodEquiv_ι, extensionFormulaMap_of_hom O U G f (f ≫ φ) φ rfl]
  rfl

/-- The identification carries the restriction maps of the coproduct presheaf to the
restriction maps of the extension formula, on elements. -/
lemma extensionFormulaCoprodEquiv_map (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)
    (G : PresheafOfModules.{max u v m} (overRingPresheaf O U))
    {V W : C} (f : V ⟶ W)
    (x : (extensionPresheaf.{v, u, w, max u v m} O U G).obj (op W)) :
    extensionFormulaCoprodEquiv.{v, u, w, m} O U G V
        ((extensionPresheaf.{v, u, w, max u v m} O U G).map f.op x) =
      extensionFormulaMap.{v, u, w, max u m} O U G f
        (extensionFormulaCoprodEquiv.{v, u, w, m} O U G W x) := by
  have h : extensionFormulaCoprodEquiv.{v, u, w, m} O U G V
        ((extensionPresheaf.{v, u, w, max u v m} O U G).map f.op
          ((extensionFormulaCoprodEquiv.{v, u, w, m} O U G W).symm
            (extensionFormulaCoprodEquiv.{v, u, w, m} O U G W x))) =
      extensionFormulaMap.{v, u, w, max u m} O U G f
        (extensionFormulaCoprodEquiv.{v, u, w, m} O U G W x) :=
    congrArg (fun k : extensionFormula.{v, u, w, max u m} O U W G →+
        extensionFormula.{v, u, w, max u m} O U V G ↦
      k (extensionFormulaCoprodEquiv.{v, u, w, m} O U G W x))
      (extensionFormulaCoprodRestriction_eq.{v, u, w, m} O U G f)
  rwa [LinearEquiv.symm_apply_apply] at h

/-- The coproduct model of the extension and its direct-sum model are isomorphic as presheaves
of modules: objectwise the identification of a coproduct of modules with their direct sum, which
commutes with every restriction map. -/
public noncomputable def extensionPresheafIsoFormulaObject (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)
    (G : PresheafOfModules.{max u v m} (overRingPresheaf O U)) :
    extensionPresheaf.{v, u, w, max u v m} O U G ≅
      extensionFormulaObject.{v, u, w, max u m} O U G :=
  PresheafOfModules.isoMk
    (fun X ↦ (extensionFormulaCoprodEquiv.{v, u, w, m} O U G X.unop).toModuleIso)
    (fun _ _ f ↦ ModuleCat.hom_ext <| LinearMap.ext <|
      extensionFormulaCoprodEquiv_map.{v, u, w, m} O U G f.unop)

/-- Extension of a presheaf of modules from `C/U` has, at `V`, the direct sum of its values
on all arrows `V ⟶ U`. These identifications commute with every restriction map. -/
@[stacks 03EJ "`j_{U!}G : V ↦ ⨁_{φ ∈ Mor(V, U)} G(V →^φ U)`"]
theorem extensionObjLinearEquivDirectSum (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)
    (A : PresheafModuleAdjunctionsOver.{v, u, w, m} O U)
    (G : PresheafOfModules.{max u v m} (overRingPresheaf O U)) :
    ∃ e : ∀ V : C,
        (A.extension.obj G).obj (op V) ≃ₗ[O.obj (op V)]
          extensionFormula.{v, u, w, max u m} O U V G,
      ∀ {V W : C} (f : V ⟶ W) (x : (A.extension.obj G).obj (op W)),
        e V ((A.extension.obj G).map f.op x) =
          extensionFormulaMap.{v, u, w, max u m} O U G f (e W x) := by
  let ψ : A.extension.obj G ≅ extensionPresheaf.{v, u, w, max u v m} O U G :=
    (Adjunction.leftAdjointUniq A.extensionRestriction
      (extensionFunctorAdjunction.{v, u, w, max u v m} O U)).app G
  let ε : ∀ V : C, (A.extension.obj G).obj (op V) ≃ₗ[O.obj (op V)]
      (extensionPresheaf.{v, u, w, max u v m} O U G).obj (op V) := fun V ↦
    { (ψ.hom.app (op V)).hom with
      invFun := (ψ.inv.app (op V)).hom
      left_inv := fun x ↦ congrArg (fun k ↦ k.app (op V) x) ψ.hom_inv_id
      right_inv := fun x ↦ congrArg (fun k ↦ k.app (op V) x) ψ.inv_hom_id }
  refine ⟨fun V ↦ (ε V).trans (extensionFormulaCoprodEquiv.{v, u, w, m} O U G V), ?_⟩
  intro V W f x
  change extensionFormulaCoprodEquiv.{v, u, w, m} O U G V
      (ψ.hom.app (op V) ((A.extension.obj G).map f.op x)) =
    extensionFormulaMap.{v, u, w, max u m} O U G f
      (extensionFormulaCoprodEquiv.{v, u, w, m} O U G W (ψ.hom.app (op W) x))
  rw [PresheafOfModules.naturality_apply ψ.hom f.op x]
  exact extensionFormulaCoprodEquiv_map.{v, u, w, m} O U G f (ψ.hom.app (op W) x)

end ExtensionFormula

end Stacks.Sites.OverModules

end
