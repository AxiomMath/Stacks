module

public import StacksFrontier.AlgebraicGeometry.InvertibleLocallyFree.Basic

/-!
# The inverse of a locally trivial sheaf of modules

Let `O` be a sheaf of commutative rings on a site `(C, J)`. A sheaf of `O`-modules which is
finite locally free of rank one is invertible, that is, tensoring by it is an auto-equivalence
of the category of `O`-modules. The inverse is the sheafification of the dual presheaf of
modules: the evaluation morphism is a *local* isomorphism, hence becomes an isomorphism after
sheafification, since sheafification of presheaves of modules is the localization at the local
isomorphisms.

## Main definitions

* `Stacks.SheafDescent.DualSection`: a section over `U` of the dual of a presheaf of modules
  `P`, namely a family of `O(W)`-linear forms on the sections of `P` over the objects `W`
  lying over `U`, compatible with restriction.
* `Stacks.SheafDescent.dual`: the dual presheaf of modules.
* `Stacks.SheafDescent.ev`: the evaluation morphism `P ⊗ dual P ⟶ O`.
* `Stacks.SheafDescent.Trivialization`: a *sectionwise* trivialization of `P` over `U`, that
  is, a compatible family of `O(W)`-linear isomorphisms `P(W) ≅ O(W)` for `W` lying over `U`.
* `Stacks.SheafDescent.tensorFun`: the sheafified tensor functor, written with the monoidal
  structure of presheaves of modules over
  `Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O`; it is equal to the
  sheaf tensor bifunctor (`Stacks.SheafDescent.tensorFun_eq`).

## Main results

* `Stacks.SheafDescent.Trivialization.dualSection_spec`: over an object carrying a sectionwise
  trivialization, every dual section is the canonical one scaled by its value on the local
  basis element.
* `Stacks.SheafDescent.Trivialization.evAppEquiv`: over an object carrying a sectionwise
  trivialization, evaluation is an isomorphism of modules of sections.
* `Stacks.SheafDescent.isIso_sheafify_map_ev`: if `P` is sectionwise trivial on a family of
  objects covering the terminal object, then `ev` becomes an isomorphism after sheafification.
* `Stacks.SheafDescent.tensorFunComp`: the composite of two sheafified tensor functors is the
  sheafified tensor functor of the sheafified tensor product.
* `Stacks.SheafDescent.isInvertible_of_trivialization`: a sheaf of modules which is
  sectionwise trivial on a family of objects covering the terminal object is invertible, in
  the sense of the library class `AlgebraicGeometry.SheafOfModules.IsInvertible`.
* `Stacks.SheafDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one`: a sheaf of modules
  which is finite locally free of rank one is invertible.
* `Stacks.SheafDescent.isInvertible_of_isLocallyTrivial`: a locally trivial sheaf of modules
  is invertible.

## Implementation notes

The sectionwise dual `U ↦ Hom_{O(U)}(P(U), O(U))` is not a presheaf, since restriction would
need a map `P(V) → P(U)` for `V` over `U`. A `DualSection` over `U` therefore records a linear
form over every object lying over `U`, and restriction is reindexing. The dual then lives in
`Type (max u v w)`, so the module universe throughout is `max u v w`.

The construction uses no descent of objects: the only passage from local to global is that a
morphism of presheaves of modules which is sectionwise bijective on a covering family becomes
an isomorphism after sheafification. That local isomorphisms are stable under tensoring
(`Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerLeft` and
`Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight`) gives the
composition of sheafified tensor functors `tensorFunComp`.

Everything is indexed by `structureRingPresheaf O` rather than by
`(Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj`, and a sheaf of modules
`L` enters through `L.val`.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits Opposite Stacks.SheafOfModules.TensorSheafification

universe v u w

namespace Stacks.SheafDescent

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{max u v w})
  (P : PresheafOfModules.{max u v w} (structureRingPresheaf O))

/-- The restriction maps of `O` compose. -/
theorem ringMap_comp_apply {W W' U : C} (h : W ⟶ U) (h' : W' ⟶ W)
    (r : (structureRingPresheaf O).obj (op U)) :
    (structureRingPresheaf O).map (h' ≫ h).op r =
      (structureRingPresheaf O).map h'.op ((structureRingPresheaf O).map h.op r) := by
  rw [op_comp, CategoryTheory.Functor.map_comp]
  rfl

/-- The restriction map of `O` along an identity is the identity. -/
theorem ringMap_id_apply {U : C} (r : (structureRingPresheaf O).obj (op U)) :
    (structureRingPresheaf O).map (𝟙 U).op r = r := by
  rw [op_id, CategoryTheory.Functor.map_id]
  rfl

/-- A section over `U` of the dual of a presheaf of modules `P`: a family of `O(W)`-linear
forms on the sections of `P` over the objects `W` lying over `U`, compatible with restriction. -/
@[ext]
structure DualSection (U : Cᵒᵖ) where
  /-- The linear form attached to an object `W` lying over `U` by a map `h`. -/
  app (W : C) (h : W ⟶ U.unop) :
    (P.obj (op W) : Type max u v w) →ₗ[((structureRingPresheaf O).obj (op W) : Type max u v w)]
      ((structureRingPresheaf O).obj (op W) : Type max u v w)
  /-- The forms are compatible with the restriction maps of `P` and of `O`. -/
  naturality {W W' : C} (h : W ⟶ U.unop) (h' : W' ⟶ W) (m : P.obj (op W)) :
    app W' (h' ≫ h) (P.map h'.op m) = (structureRingPresheaf O).map h'.op (app W h m)

namespace DualSection

variable {O P} {U : Cᵒᵖ}

/-- Two dual sections are equal if their linear forms agree on every section. -/
theorem ext_app {φ ψ : DualSection O P U}
    (h : ∀ (W : C) (g : W ⟶ U.unop) (m : P.obj (op W)), φ.app W g m = ψ.app W g m) : φ = ψ :=
  DualSection.ext (funext fun W ↦ funext fun g ↦ LinearMap.ext (h W g))

/-- The zero dual section, all of whose linear forms vanish. -/
instance : Zero (DualSection O P U) where
  zero :=
    { app := fun _ _ ↦ 0
      naturality := fun {_ _} _ h' _ ↦ by
        change (0 : ((structureRingPresheaf O).obj (op _) : Type max u v w)) =
          (structureRingPresheaf O).map h'.op 0
        rw [map_zero] }

/-- The linear forms of the zero dual section vanish. -/
@[simp] theorem zero_app (W : C) (g : W ⟶ U.unop) (m : P.obj (op W)) :
    (0 : DualSection O P U).app W g m = 0 := rfl

/-- The sum of two dual sections, formed linear form by linear form. -/
instance : Add (DualSection O P U) where
  add φ ψ :=
    { app := fun W h ↦ φ.app W h + ψ.app W h
      naturality := fun {_ _} h h' m ↦ by
        change φ.app _ (h' ≫ h) (P.map h'.op m) + ψ.app _ (h' ≫ h) (P.map h'.op m) =
          (structureRingPresheaf O).map h'.op (φ.app _ h m + ψ.app _ h m)
        rw [map_add, φ.naturality, ψ.naturality] }

/-- The linear forms of a sum of dual sections are the sums of the linear forms. -/
@[simp] theorem add_app (φ ψ : DualSection O P U) (W : C) (g : W ⟶ U.unop) (m : P.obj (op W)) :
    (φ + ψ).app W g m = φ.app W g m + ψ.app W g m := rfl

/-- The negative of a dual section, formed linear form by linear form. -/
instance : Neg (DualSection O P U) where
  neg φ :=
    { app := fun W h ↦ -φ.app W h
      naturality := fun {_ _} h h' m ↦ by
        change -φ.app _ (h' ≫ h) (P.map h'.op m) =
          (structureRingPresheaf O).map h'.op (-φ.app _ h m)
        rw [map_neg, φ.naturality] }

/-- The linear forms of the negative of a dual section are the negated linear forms. -/
@[simp] theorem neg_app (φ : DualSection O P U) (W : C) (g : W ⟶ U.unop) (m : P.obj (op W)) :
    (-φ).app W g m = -φ.app W g m := rfl

/-- The dual sections over `U` form an additive commutative group. -/
instance : AddCommGroup (DualSection O P U) where
  add_assoc a b c := by ext W g m; exact add_assoc (a.app W g m) (b.app W g m) (c.app W g m)
  zero_add a := by ext W g m; exact zero_add (a.app W g m)
  add_zero a := by ext W g m; exact add_zero (a.app W g m)
  neg_add_cancel a := by ext W g m; exact neg_add_cancel (a.app W g m)
  add_comm a b := by ext W g m; exact add_comm (a.app W g m) (b.app W g m)
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- A section `r` of `O` over `U` scales a dual section: the form over `h : W ⟶ U` is multiplied
by the restriction of `r` along `h`. -/
instance : SMul ((structureRingPresheaf O).obj U : Type max u v w) (DualSection O P U) where
  smul r φ :=
    { app := fun W h ↦ (structureRingPresheaf O).map h.op r • φ.app W h
      naturality := fun {_ _} h h' m ↦ by
        change (structureRingPresheaf O).map (h' ≫ h).op r • φ.app _ (h' ≫ h) (P.map h'.op m) =
          (structureRingPresheaf O).map h'.op
            ((structureRingPresheaf O).map h.op r • φ.app _ h m)
        rw [smul_eq_mul, smul_eq_mul, map_mul, ringMap_comp_apply, φ.naturality] }

/-- The linear forms of `r • φ` are those of `φ` multiplied by the restrictions of `r`. -/
@[simp] theorem smul_app (r : (structureRingPresheaf O).obj U) (φ : DualSection O P U)
    (W : C) (g : W ⟶ U.unop) (m : P.obj (op W)) :
    (r • φ).app W g m = (structureRingPresheaf O).map g.op r • φ.app W g m := rfl

/-- The dual sections over `U` form a module over the sections of `O` over `U`. -/
instance : Module ((structureRingPresheaf O).obj U : Type max u v w) (DualSection O P U) where
  one_smul a := by
    ext W g m
    change (structureRingPresheaf O).map g.op 1 • a.app W g m = a.app W g m
    rw [map_one, one_smul]
  mul_smul r s a := by
    ext W g m
    change (structureRingPresheaf O).map g.op (r * s) • a.app W g m =
      (structureRingPresheaf O).map g.op r • (structureRingPresheaf O).map g.op s • a.app W g m
    rw [map_mul, mul_smul]
  smul_zero r := by
    ext W g m
    exact smul_zero ((structureRingPresheaf O).map g.op r)
  smul_add r a b := by
    ext W g m
    exact smul_add ((structureRingPresheaf O).map g.op r) (a.app W g m) (b.app W g m)
  add_smul r s a := by
    ext W g m
    change (structureRingPresheaf O).map g.op (r + s) • a.app W g m =
      (structureRingPresheaf O).map g.op r • a.app W g m +
        (structureRingPresheaf O).map g.op s • a.app W g m
    rw [map_add, add_smul]
  zero_smul a := by
    ext W g m
    change (structureRingPresheaf O).map g.op 0 • a.app W g m = 0
    rw [map_zero, zero_smul]

/-- Restriction of a dual section along a morphism of the site. -/
def restrict (φ : DualSection O P U) {U' : Cᵒᵖ} (f : U ⟶ U') : DualSection O P U' where
  app W h := φ.app W (h ≫ f.unop)
  naturality {_ _} h h' m := by
    rw [Category.assoc]
    exact φ.naturality (h ≫ f.unop) h' m

/-- The restriction of `φ` along `f` evaluates over `g` as `φ` evaluates over `g ≫ f.unop`. -/
@[simp] theorem restrict_app (φ : DualSection O P U) {U' : Cᵒᵖ} (f : U ⟶ U')
    (W : C) (g : W ⟶ U'.unop) (m : P.obj (op W)) :
    (φ.restrict f).app W g m = φ.app W (g ≫ f.unop) m := rfl

end DualSection

/-- The dual of a presheaf of modules: over `U` its sections are the `O`-linear forms on the
sections of `P` over the objects lying over `U`. -/
noncomputable def dual : PresheafOfModules.{max u v w} (structureRingPresheaf O) where
  obj U := ModuleCat.of _ (DualSection O P U)
  map {_ U'} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars ((structureRingPresheaf O).map f).hom).obj
        (ModuleCat.of _ (DualSection O P U')))
    { toFun := fun φ ↦ φ.restrict f
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r φ ↦ DualSection.ext_app fun W h m ↦
        congrArg (fun s ↦ s • φ.app W (h ≫ f.unop) m) (ringMap_comp_apply O f.unop h r) }
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun φ ↦ DualSection.ext_app fun W h m ↦
    congrArg (fun g ↦ φ.app W g m) (Category.comp_id h))
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext fun φ ↦ DualSection.ext_app fun W h m ↦
    congrArg (fun k ↦ φ.app W k m) (Category.assoc h g.unop f.unop).symm)

/-- The evaluation morphism from `P` tensored with its dual to the monoidal unit: a section is
evaluated at the identity of the object over which it lives. -/
noncomputable def ev :
    P ⊗ dual O P ⟶ 𝟙_ (PresheafOfModules.{max u v w} (structureRingPresheaf O)) where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun (m : P.obj U) (φ : DualSection O P U) ↦ φ.app U.unop (𝟙 U.unop) m)
    (fun m m' _ ↦ map_add _ m m') (fun a m _ ↦ map_smul _ a m) (fun _ _ _ ↦ rfl)
    (fun a m φ ↦ by
      change (structureRingPresheaf O).map (𝟙 U.unop).op a • φ.app U.unop (𝟙 U.unop) m =
        a • φ.app U.unop (𝟙 U.unop) m
      rw [ringMap_id_apply])
  naturality {U V} f := ModuleCat.MonoidalCategory.tensor_ext fun m φ ↦ by
    have h := φ.naturality (𝟙 U.unop) f.unop m
    rw [Category.comp_id] at h
    change φ.app _ (𝟙 V.unop ≫ f.unop) (P.map f.unop.op m) =
      (structureRingPresheaf O).map f.unop.op (φ.app _ (𝟙 U.unop) m)
    rw [Category.id_comp]
    exact h

/-- A sectionwise trivialization of `P` over `U`: `O(W)`-linear isomorphisms from the sections
of `P` to those of `O`, for every object `W` lying over `U`, compatible with restriction. -/
structure Trivialization (U : C) where
  /-- The isomorphism on sections over an object `W` lying over `U` by a map `h`. -/
  θ (W : C) (h : W ⟶ U) :
    (P.obj (op W) : Type max u v w) ≃ₗ[((structureRingPresheaf O).obj (op W) : Type max u v w)]
      ((structureRingPresheaf O).obj (op W) : Type max u v w)
  /-- The isomorphisms are compatible with the restriction maps of `P` and of `O`. -/
  θ_naturality {W W' : C} (h : W ⟶ U) (h' : W' ⟶ W) (m : P.obj (op W)) :
    θ W' (h' ≫ h) (P.map h'.op m) = (structureRingPresheaf O).map h'.op (θ W h m)

namespace Trivialization

variable {O P} {U : C} (t : Trivialization O P U)

/-- A trivialization over `U` induces one over any object lying over `U`. -/
def comp {V : C} (g : V ⟶ U) : Trivialization O P V where
  θ W h := t.θ W (h ≫ g)
  θ_naturality {_ _} h h' m := by
    rw [Category.assoc]
    exact t.θ_naturality (h ≫ g) h' m

/-- The dual section of `P` over `U` determined by a trivialization. -/
def dualSection : DualSection O P (op U) where
  app W h := (t.θ W h).toLinearMap
  naturality := t.θ_naturality

/-- The linear forms of the dual section of a trivialization are its isomorphisms. -/
@[simp] theorem dualSection_app (W : C) (h : W ⟶ U) (m : P.obj (op W)) :
    t.dualSection.app W h m = t.θ W h m := rfl

/-- The local basis element: the section of `P` over `U` sent to `1` by the trivialization. -/
noncomputable def basis : P.obj (op U) := (t.θ U (𝟙 U)).symm 1

/-- The trivialization over `U` sends the local basis element to `1`. -/
theorem θ_basis : t.θ U (𝟙 U) t.basis = 1 := (t.θ U (𝟙 U)).apply_symm_apply 1

/-- The local basis element, restricted to an object lying over `U`. -/
noncomputable def basisAt {W : C} (h : W ⟶ U) : (P.obj (op W) : Type max u v w) :=
  P.map h.op t.basis

/-- The trivialization over `W` sends the restricted local basis element to `1`. -/
theorem θ_basisAt {W : C} (h : W ⟶ U) : t.θ W h (t.basisAt h) = 1 := by
  simpa [t.θ_basis, basisAt] using t.θ_naturality (𝟙 U) h t.basis

/-- The value of a dual section on the restricted local basis element is the restriction of
its value on the local basis element. -/
theorem naturality_basisAt (φ : DualSection O P (op U)) {W : C} (h : W ⟶ U) :
    φ.app W h (t.basisAt h) =
      (structureRingPresheaf O).map h.op (φ.app U (𝟙 U) t.basis) := by
  simpa [basisAt] using φ.naturality (𝟙 U) h t.basis

/-- Every section of `P` over `W` is its image under the trivialization times the restricted
local basis element. -/
theorem eq_smul_basisAt {W : C} (h : W ⟶ U) (m : P.obj (op W)) :
    m = t.θ W h m • t.basisAt h := by
  apply (t.θ W h).injective
  rw [map_smul, t.θ_basisAt, smul_eq_mul, mul_one]

/-- Every dual section over `U` is the dual section of the trivialization scaled by its value on
the local basis element. -/
theorem dualSection_spec (φ : DualSection O P (op U)) :
    φ = φ.app U (𝟙 U) t.basis • t.dualSection := by
  refine DualSection.ext_app fun W h m ↦ ?_
  rw [DualSection.smul_app, dualSection_app, ← t.naturality_basisAt φ h]
  conv_lhs => rw [t.eq_smul_basisAt h m]
  rw [map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

/-- On a pure tensor `m ⊗ₜ φ`, the section `(θ U (𝟙 U)).symm (φ.app U (𝟙 U) m) ⊗ₜ dualSection`
equals `m ⊗ₜ φ`. -/
theorem evInv_ev_tmul (m : P.obj (op U)) (φ : DualSection O P (op U)) :
    (t.θ U (𝟙 U)).symm (φ.app U (𝟙 U) m)
        ⊗ₜ[((structureRingPresheaf O).obj (op U) : Type max u v w)] t.dualSection =
      m ⊗ₜ[((structureRingPresheaf O).obj (op U) : Type max u v w)] φ := by
  have hφ := t.dualSection_spec φ
  have hev : φ.app U (𝟙 U) m = φ.app U (𝟙 U) t.basis * t.θ U (𝟙 U) m := by
    conv_lhs => rw [hφ]
    rw [DualSection.smul_app, dualSection_app, ringMap_id_apply, smul_eq_mul]
  have hsym : (t.θ U (𝟙 U)).symm (φ.app U (𝟙 U) m) = φ.app U (𝟙 U) t.basis • m := by
    rw [hev, ← smul_eq_mul, map_smul, LinearEquiv.symm_apply_apply]
  have hmk : m ⊗ₜ[((structureRingPresheaf O).obj (op U) : Type max u v w)]
        (φ.app U (𝟙 U) t.basis • t.dualSection) =
      φ.app U (𝟙 U) t.basis •
        m ⊗ₜ[((structureRingPresheaf O).obj (op U) : Type max u v w)] t.dualSection :=
    map_smul (TensorProduct.mk _ _ _ m) _ t.dualSection
  rw [hsym, ← TensorProduct.smul_tmul', ← hmk, ← hφ]

/-- Evaluation on sections over `U` is an isomorphism, as soon as `P` is trivialized over `U`. -/
noncomputable def evAppEquiv :
    ((P ⊗ dual O P).obj (op U) : Type max u v w)
      ≃ₗ[((structureRingPresheaf O).obj (op U) : Type max u v w)]
      ((structureRingPresheaf O).obj (op U) : Type max u v w) :=
  LinearEquiv.ofLinearMap ((ev O P).app (op U)).hom
    { toFun := fun r ↦ (t.θ U (𝟙 U)).symm r ⊗ₜ t.dualSection
      map_add' := fun r s ↦ by rw [map_add]; exact TensorProduct.add_tmul _ _ _
      map_smul' := fun a r ↦ by rw [map_smul]; exact (TensorProduct.smul_tmul' _ _ _).symm }
    (LinearMap.ext fun r ↦ (t.θ U (𝟙 U)).apply_symm_apply r)
    (TensorProduct.ext' fun m φ ↦ t.evInv_ev_tmul m φ)

include t in
/-- Evaluation on sections over `U` is bijective when `P` is trivialized over `U`. -/
theorem bijective_ev_app : Function.Bijective ((ev O P).app (op U)).hom :=
  LinearEquiv.bijective t.evAppEquiv

end Trivialization

section Local

variable {J : GrothendieckTopology C} {I : Type*} {Y : I → C}

/-- Evaluation is locally surjective as soon as `P` is trivialized on a family of objects
covering the terminal object. -/
theorem isLocallySurjective_ev (hY : J.CoversTop Y) (t : ∀ i, Trivialization O P (Y i)) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf (structureRingPresheaf O)).map (ev O P)) where
  imageSieve_mem {U} s := by
    refine J.superset_covering ?_ (hY U)
    rintro W g ⟨i, ⟨k⟩⟩
    exact ((t i).comp k).bijective_ev_app.surjective _

/-- Evaluation is locally injective as soon as `P` is trivialized on a family of objects
covering the terminal object. -/
theorem isLocallyInjective_ev (hY : J.CoversTop Y) (t : ∀ i, Trivialization O P (Y i)) :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf (structureRingPresheaf O)).map (ev O P)) where
  equalizerSieve_mem {V} x y h := by
    refine J.superset_covering ?_ (hY V.unop)
    rintro W g ⟨i, ⟨k⟩⟩
    refine ((t i).comp k).bijective_ev_app.injective ?_
    have key (z : (P ⊗ dual O P).obj V) : (ev O P).app (op W) ((P ⊗ dual O P).map g.op z) =
        (PresheafOfModules.unit (structureRingPresheaf O)).map g.op ((ev O P).app V z) :=
      PresheafOfModules.naturality_apply (ev O P) g.op z
    exact (key x).trans (Eq.trans (congrArg _ h) (key y).symm)

variable (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]

/-- Evaluation becomes an isomorphism after sheafification, as soon as `P` is trivialized on a
family of objects covering the terminal object. -/
theorem isIso_sheafify_map_ev (hY : J.CoversTop Y) (t : ∀ i, Trivialization O P (Y i)) :
    IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (ev O P)) := by
  have hW : J.W ((PresheafOfModules.toPresheaf (structureRingPresheaf O)).map (ev O P)) :=
    (J.W_iff_isLocallyBijective _).2
      ⟨isLocallyInjective_ev O P hY t, isLocallySurjective_ev O P hY t⟩
  exact Localization.inverts
    (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      O hO).obj))
    (J.W.inverseImage (PresheafOfModules.toPresheaf
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj)) _
    ((MorphismProperty.inverseImage_iff _ _ _).2 hW)

end Local

section Assembly

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry.SheafOfModules Stacks.InvertibleLocallyFree

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

variable {J : GrothendieckTopology C}
  (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]

/-- A trivialization, read sectionwise, of the restriction of a sheaf of modules to the slice
category over an object, from an isomorphism with the restricted structure sheaf. -/
noncomputable def Trivialization.ofIso {X : C}
    {L : SheafOfModules.{max u v w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)}
    (e : L.over X ≅ SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf
      O hO).over X)) :
    Trivialization O L.val X where
  θ W h := ((PresheafOfModules.evaluation _ (op (Over.mk h))).mapIso
    ((SheafOfModules.forget _).mapIso e)).toLinearEquiv
  θ_naturality {W W'} h h' m :=
    PresheafOfModules.naturality_apply (M₁ := (L.over X).val) e.hom.val
      (Over.homMk h' (by simp) : Over.mk (h' ≫ h) ⟶ Over.mk h).op m

/-- The sheafified tensor functor, written with the monoidal structure of presheaves of modules
over `structureRingPresheaf O`, with a presheaf as the fixed tensor factor. -/
noncomputable abbrev tensorFun (A : PresheafOfModules.{max u v w} (structureRingPresheaf O)) :
    SheafOfModules.{max u v w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⥤
      SheafOfModules.{max u v w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
  SheafOfModules.forget _ ⋙ tensorLeft A ⋙ Stacks.SheafOfModules.TensorSheafification.sheafify O hO

/-- The sheaf tensor bifunctor applied to a sheaf of modules `A` is the sheafified tensor
functor `tensorFun` of the underlying presheaf of `A`. -/
theorem tensorFun_eq (A : SheafOfModules.{max u v w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v w, max u v w, max u v w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).obj A =
        tensorFun O hO A.val := rfl

/-- Sheafifying the second factor does not change the sheafification of a tensor product. -/
noncomputable def sheafifyTensorLeftIso
    (A B : PresheafOfModules.{max u v w} (structureRingPresheaf O)) :
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (A ⊗ B) ≅
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (A ⊗
        ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj B).val) :=
  @asIso _ _ _ _ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (A ◁
    Stacks.SheafOfModules.TensorSheafification.toSheafify O hO B))
    (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerLeft O hO A
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO B)
      (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify O hO B))

/-- Sheafifying the first factor does not change the sheafification of a tensor product. -/
noncomputable def sheafifyTensorRightIso
    (A B : PresheafOfModules.{max u v w} (structureRingPresheaf O)) :
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (A ⊗ B) ≅
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj
        (((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A).val ⊗ B) :=
  @asIso _ _ _ _ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map
    (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO A ▷ B))
    (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight O hO
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO A) B
      (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify O hO A))

/-- The sheafification unit, tensored on the left by `B` and sheafified. -/
noncomputable def tensorLeftSheafifyUnit
    (B : PresheafOfModules.{max u v w} (structureRingPresheaf O)) :
    tensorLeft B ⋙ Stacks.SheafOfModules.TensorSheafification.sheafify O hO ⟶
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO ⋙ SheafOfModules.forget _) ⋙
        tensorLeft B ⋙ Stacks.SheafOfModules.TensorSheafification.sheafify O hO :=
  Functor.whiskerRight (Functor.whiskerRight
    (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction O hO).unit
    (tensorLeft B)) (Stacks.SheafOfModules.TensorSheafification.sheafify O hO)

/-- Each component of `tensorLeftSheafifyUnit` is an isomorphism. -/
theorem isIso_tensorLeftSheafifyUnit_app
    (B Q : PresheafOfModules.{max u v w} (structureRingPresheaf O)) :
    IsIso ((tensorLeftSheafifyUnit O hO B).app Q) :=
  Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerLeft O hO B
    (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO Q)
    (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify O hO Q)

/-- Tensoring on the left by `B` commutes with sheafification, after sheafification. -/
noncomputable def tensorLeftSheafifyUnitIso
    (B : PresheafOfModules.{max u v w} (structureRingPresheaf O)) :
    tensorLeft B ⋙ Stacks.SheafOfModules.TensorSheafification.sheafify O hO ≅
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO ⋙ SheafOfModules.forget _) ⋙
        tensorLeft B ⋙ Stacks.SheafOfModules.TensorSheafification.sheafify O hO :=
  haveI : ∀ Q, IsIso ((tensorLeftSheafifyUnit O hO B).app Q) :=
    isIso_tensorLeftSheafifyUnit_app O hO B
  @asIso _ _ _ _ (tensorLeftSheafifyUnit O hO B)
    (NatIso.isIso_of_isIso_app (tensorLeftSheafifyUnit O hO B))

/-- The sheafification unit, tensored on the right and sheafified. -/
noncomputable def tensorRightSheafifyUnit
    (A : PresheafOfModules.{max u v w} (structureRingPresheaf O)) :
    tensorLeft A ⋙ Stacks.SheafOfModules.TensorSheafification.sheafify O hO ⟶
      tensorLeft (((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A).val) ⋙
        Stacks.SheafOfModules.TensorSheafification.sheafify O hO :=
  Functor.whiskerRight
    ((curriedTensor (PresheafOfModules.{max u v w} (structureRingPresheaf O))).map
      (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO A))
        (Stacks.SheafOfModules.TensorSheafification.sheafify O hO)

/-- Each component of `tensorRightSheafifyUnit` is an isomorphism. -/
theorem isIso_tensorRightSheafifyUnit_app
    (A Q : PresheafOfModules.{max u v w} (structureRingPresheaf O)) :
    IsIso ((tensorRightSheafifyUnit O hO A).app Q) :=
  Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_whiskerRight O hO
    (Stacks.SheafOfModules.TensorSheafification.toSheafify O hO A) Q
    (Stacks.SheafOfModules.TensorSheafification.isIso_sheafify_map_toSheafify O hO A)

/-- Replacing the tensoring object by its sheafification does not change the sheafified tensor
functor. -/
noncomputable def tensorRightSheafifyUnitIso
    (A : PresheafOfModules.{max u v w} (structureRingPresheaf O)) :
    tensorLeft A ⋙ Stacks.SheafOfModules.TensorSheafification.sheafify O hO ≅
      tensorLeft (((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj A).val) ⋙
        Stacks.SheafOfModules.TensorSheafification.sheafify O hO :=
  haveI : ∀ Q, IsIso ((tensorRightSheafifyUnit O hO A).app Q) :=
    isIso_tensorRightSheafifyUnit_app O hO A
  @asIso _ _ _ _ (tensorRightSheafifyUnit O hO A)
    (NatIso.isIso_of_isIso_app (tensorRightSheafifyUnit O hO A))

/-- The composite of two sheafified tensor functors is the sheafified tensor functor of the
sheafified tensor product. -/
noncomputable def tensorFunComp
    (A B : PresheafOfModules.{max u v w} (structureRingPresheaf O)) :
    tensorFun O hO A ⋙ tensorFun O hO B ≅
      tensorFun O hO (((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (B ⊗ A)).val)
        :=
  by
  have h1 : tensorFun O hO A ⋙ tensorFun O hO B ≅
      SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
        tensorLeft A ⋙ tensorLeft B ⋙ Stacks.SheafOfModules.TensorSheafification.sheafify O hO :=
    (Functor.isoWhiskerLeft
      (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
        tensorLeft A)
      (tensorLeftSheafifyUnitIso O hO B)).symm
  have h2 : SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
        tensorLeft A ⋙ tensorLeft B ⋙ Stacks.SheafOfModules.TensorSheafification.sheafify O hO ≅
      SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
        tensorLeft (B ⊗ A) ⋙ Stacks.SheafOfModules.TensorSheafification.sheafify O hO :=
    (Functor.isoWhiskerLeft (SheafOfModules.forget
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      (Functor.isoWhiskerRight (tensorLeftTensor B A)
        (Stacks.SheafOfModules.TensorSheafification.sheafify O hO))).symm
  have h3 : SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⋙
        tensorLeft (B ⊗ A) ⋙ Stacks.SheafOfModules.TensorSheafification.sheafify O hO ≅
      tensorFun O hO (((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (B ⊗ A)).val)
        :=
    Functor.isoWhiskerLeft (SheafOfModules.forget
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      (tensorRightSheafifyUnitIso O hO (B ⊗ A))
  exact h1 ≪≫ h2 ≪≫ h3

/-- Two tensor functors compose to the identity as soon as the sheafified tensor product of the
two objects is the structure sheaf. -/
noncomputable def tensorFunCompUnitIso
    (A B : PresheafOfModules.{max u v w} (structureRingPresheaf O))
    (e : (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (B ⊗ A) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    tensorFun O hO A ⋙ tensorFun O hO B ≅ 𝟭 _ := by
  have composition := tensorFunComp O hO A B
  rw [← tensorFun_eq O hO
    ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (B ⊗ A))] at composition
  exact composition ≪≫
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v w, max u v w, max u v w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).mapIso
        (X := (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (B ⊗ A))
        (Y := SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) e ≪≫
    tensorLeftFunctorUnitIso O hO

variable {I : Type*} {Y : I → C}

/-- The sheafified tensor product of `P` with its dual is the structure sheaf, as soon as `P` is
sectionwise trivial on a family covering the terminal object. -/
noncomputable def tensorDualUnitIso (hY : J.CoversTop Y)
    (t : ∀ i, Trivialization O P (Y i)) :
    (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (P ⊗ dual O P) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
  @asIso _ _ _ _ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).map (ev O P))
      (isIso_sheafify_map_ev O P hO hY t) ≪≫
    (sheafifyForgetIso O hO).app (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))

/-- A sheaf of modules that is sectionwise trivial on a family of objects covering the terminal
object is invertible. -/
theorem isInvertible_of_trivialization
    (L : SheafOfModules.{max u v w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)) (hY : J.CoversTop Y)
    (t : ∀ i, Trivialization O L.val (Y i)) :
    IsInvertible O hO L := by
  refine (isInvertible_iff_tensorLeftFunctor_isEquivalence O hO L).mpr ?_
  have u2 : (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj
      (L.val ⊗ ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (dual O L.val)).val)
        ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
    (sheafifyTensorLeftIso O hO L.val (dual O L.val)).symm ≪≫
      tensorDualUnitIso O L.val hO hY t
  have hbr : dual O L.val ⊗ L.val ≅ L.val ⊗ dual O L.val := β_ (dual O L.val) L.val
  have u1 : (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj
      (((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (dual O L.val)).val ⊗ L.val)
        ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) :=
    (sheafifyTensorRightIso O hO (dual O L.val) L.val).symm ≪≫
      (Stacks.SheafOfModules.TensorSheafification.sheafify O hO).mapIso hbr ≪≫ tensorDualUnitIso O
        L.val hO hY t
  exact (CategoryTheory.Equivalence.mk (tensorFun O hO L.val)
    (tensorFun O hO ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (dual O
      L.val)).val)
    (tensorFunCompUnitIso O hO L.val
      ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (dual O L.val)).val u1).symm
    (tensorFunCompUnitIso O hO ((Stacks.SheafOfModules.TensorSheafification.sheafify O hO).obj (dual
      O L.val)).val
      L.val u2)).isEquivalence_functor

/-- A sheaf of modules that is trivial on a family of objects covering the terminal object is
invertible. -/
private theorem isInvertible_of_exists_coversTop_nonempty_iso_unit
    (L : SheafOfModules.{max u v w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO))
    (h : ∃ (I' : Type u) (X : I' → C) (_ : J.CoversTop X),
      ∀ i, Nonempty (L.over (X i) ≅ SheafOfModules.unit
        ((Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).over (X i)))) :
    IsInvertible O hO L := by
  obtain ⟨I', X, hX, e⟩ := h
  exact isInvertible_of_trivialization O hO L hX fun i ↦ Trivialization.ofIso O hO (e i).some

/-- A sheaf of modules that is finite locally free of rank one is invertible. -/
theorem isInvertible_of_isFiniteLocallyFreeOfRank_one
    [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{max u v w}]
    [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (L : SheafOfModules.{max u v w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO))
    [IsFiniteLocallyFreeOfRank L 1] :
    IsInvertible O hO L := by
  exact isInvertible_of_exists_coversTop_nonempty_iso_unit O hO L
    (exists_coversTop_nonempty_iso_unit_of_isFiniteLocallyFreeOfRank_one O hO L)

/-- A locally trivial sheaf of modules, in the sense of
`Stacks.SheafOfModules.Invertible.IsLocallyTrivial`, is invertible. -/
theorem isInvertible_of_isLocallyTrivial
    [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{max u v w}]
    [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    (L : SheafOfModules.{max u v w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO))
    (h : Stacks.SheafOfModules.Invertible.IsLocallyTrivial L) :
    IsInvertible O hO L := by
  exact isInvertible_of_exists_coversTop_nonempty_iso_unit O hO L h.exists_trivializing_cover

end Assembly

end Stacks.SheafDescent

end
