module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.StalkCriterionPartOneAcyclic
public import StacksFrontier.CategoryTheory.Sites.Point.FlatModuleStalk
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The stalk of a free sheaf of modules at a point of a site

Let `(C, O)` be a ringed site, `Φ` a point of `C`, `U` an object of `C` and `x₀` an element of
the fibre of `Φ` at `U`.  This file constructs, for the free presheaf of `O`-modules
`freePres O U n` on `n` copies of the representable presheaf at `U`, a **retract**

* `Stacks.Sheaves.FreeModuleStalk.incl`: `O_Φ^n ⟶ (freePres O U n)_Φ`, the `i`-th basis vector
  going to the germ at `(U, x₀)` of the `i`-th tautological generator;
* `Stacks.Sheaves.FreeModuleStalk.proj`: `(freePres O U n)_Φ ⟶ O_Φ^n`, the coefficient map at
  `(U, x₀)`;
* `Stacks.Sheaves.FreeModuleStalk.incl_proj`: `incl ≫ proj = 𝟙`.

This is the `(U, x₀)`-component of the module-level form of Stacks 04H4: the stalk of an
extension by zero decomposes as a direct sum over the fibre, one summand for each element of
`Φ.fiber.obj U`.

The retract is compatible with the action of sections of `O` over `U`, which is the content of
the two intertwining squares `incl_comp_stalkMap` and `stalkMap_comp_proj`: for a matrix `A` of
sections of `O` over `U`, the morphism `matrixHom` of free presheaves of modules it induces is
carried by the stalk functor to the matrix `germMatrix` of germs at `(U, x₀)`, in both
directions.  Together with `retract_cokernel` this says that a finitely presented `O_Φ`-module
presented by the germ matrix is a retract of the cokernel of `matrixHom` at the stalk.

## Main results

* `Stacks.Sheaves.FreeModuleStalk.incl_proj`: the retract at the stalk of the free presheaf.
* `Stacks.Sheaves.FreeModuleStalk.incl_comp_stalkMap`,
  `Stacks.Sheaves.FreeModuleStalk.stalkMap_comp_proj`: the two intertwining squares.
* `Stacks.Sheaves.FreeModuleStalk.retract_cokernel`: a presentation which is an arrow-category
  retract of a map of modules exhibits the presented module as a retract of the cokernel.

## Implementation notes

The germ map `germHom` is the composite of the `RingCat`-valued germ with
`Stacks.commRingSheafFiberIso`, so every statement here is about modules over
`structureStalk O Φ`.

The restriction maps of `freePres`, a scaled generator and the coefficient map are named
(`restr`, `gens`, `coeff`) because the underlying terms carry two definitionally equal but
syntactically different spellings of the same module (`ModuleCat.restrictScalars` of a module
versus the module). For the same reason `freePres_induction` states induction on sections with
the zero and addition of `freePres` rather than those of `Finsupp`.

Everything is at a single universe `u` with `Category.{u} C`, as
`Stacks.SheafOfModules.Tensor.ringSheaf` requires.

## References

* [Stacks Project, Tag 04H4](https://stacks.math.columbia.edu/tag/04H4)
* [Stacks Project, Tag 0DEN](https://stacks.math.columbia.edu/tag/0DEN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace Stacks.Sheaves.FreeModuleStalk

open _root_.Stacks.Sheaves.KFlatStalkCriterion (structureStalk)

/-- **A retract transported along a presentation.**  If a presentation `R^k --G--> R^l --f-->
N --> 0` of `N` is a retract, in the arrow category, of a map `u : X ⟶ Y` of `R`-modules, then
`N` is a retract of `coker u`. -/
lemma retract_cokernel {R : Type u} [Ring R] {k l : ℕ} {X Y N : ModuleCat.{u} R} (u : X ⟶ Y)
    (σ : ModuleCat.of R (Fin l → R) ⟶ Y) (π : Y ⟶ ModuleCat.of R (Fin l → R))
    (σ' : ModuleCat.of R (Fin k → R) ⟶ X) (π' : X ⟶ ModuleCat.of R (Fin k → R))
    (G : ModuleCat.of R (Fin k → R) ⟶ ModuleCat.of R (Fin l → R))
    (hσπ : σ ≫ π = 𝟙 _) (h1 : σ' ≫ u = G ≫ σ) (h2 : u ≫ π = π' ≫ G)
    (f : (Fin l → R) →ₗ[R] N) (hf : Function.Surjective f)
    (hfg : Function.Exact G.hom f) :
    ∃ (i : N ⟶ cokernel u) (p : cokernel u ⟶ N), i ≫ p = 𝟙 N := by
  have hGf : G ≫ ModuleCat.ofHom f = 0 :=
    ConcreteCategory.hom_ext _ _ fun v => hfg.apply_apply_eq_zero v
  have hzero : u ≫ (π ≫ ModuleCat.ofHom f) = 0 := by
    rw [← Category.assoc, h2, Category.assoc, hGf, comp_zero]
  have hker : LinearMap.ker f ≤ LinearMap.ker (σ ≫ cokernel.π u).hom := by
    intro v hv
    obtain ⟨w, hw⟩ := (hfg v).1 (LinearMap.mem_ker.mp hv)
    simp only [LinearMap.mem_ker]
    show cokernel.π u (σ v) = 0
    rw [← hw]
    have h3 : σ (G.hom w) = u (σ' w) := (ConcreteCategory.congr_hom h1 w).symm
    rw [h3]
    show (u ≫ cokernel.π u) (σ' w) = 0
    rw [cokernel.condition]
    rfl
  refine ⟨ConcreteCategory.ofHom ((Submodule.liftQ (LinearMap.ker f)
      (σ ≫ cokernel.π u).hom hker).comp
      (LinearMap.quotKerEquivOfSurjective f hf).symm.toLinearMap),
    cokernel.desc u (π ≫ ModuleCat.ofHom f) hzero, ?_⟩
  refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
  obtain ⟨v, rfl⟩ := hf x
  show cokernel.desc u (π ≫ ModuleCat.ofHom f) hzero
    ((Submodule.liftQ (LinearMap.ker f) (σ ≫ cokernel.π u).hom hker)
      ((LinearMap.quotKerEquivOfSurjective f hf).symm (f v))) = f v
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  show (cokernel.π u ≫ cokernel.desc u (π ≫ ModuleCat.ofHom f) hzero) (σ v) = f v
  rw [cokernel.π_desc]
  show f (π (σ v)) = f v
  rw [show π (σ v) = v from ConcreteCategory.congr_hom hσπ v]

/-- A retract of `X` is a retract of anything isomorphic to `X`. -/
lemma retract_of_iso {R : Type u} [Ring R] {N X Y : ModuleCat.{u} R} (e : X ≅ Y)
    (h : ∃ (i : N ⟶ X) (p : X ⟶ N), i ≫ p = 𝟙 N) :
    ∃ (i : N ⟶ Y) (p : Y ⟶ N), i ≫ p = 𝟙 N := by
  obtain ⟨i, p, hip⟩ := h
  refine ⟨i ≫ e.hom, e.inv ≫ p, ?_⟩
  rw [Category.assoc, Iso.hom_inv_id_assoc, hip]

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (O : Sheaf J CommRingCat.{u})
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The underlying presheaf of rings of the structure sheaf `O`. -/
abbrev ringPresheaf : Cᵒᵖ ⥤ RingCat.{u} := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj

variable (Φ : J.Point.{u})

/-- The stalk at `Φ` of a presheaf of `O`-modules, as a module over the stalk `O_Φ`. -/
abbrev stalkPres : PresheafOfModules.{u} (ringPresheaf O) ⥤
    ModuleCat.{u} (structureStalk O Φ) :=
  Stacks.presheafModuleFiber Φ (ringPresheaf O) ⋙
    ModuleCat.restrictScalars.{u} (Stacks.commRingSheafFiberIso Φ O).inv.hom

/-- The germ map `O(V) →+* O_Φ` at the point `y` of the fibre of `Φ` over `V`. -/
abbrev germHom (V : C) (y : Φ.fiber.obj V) :
    ((ringPresheaf O).obj (op V) : Type u) →+* (structureStalk O Φ : Type u) :=
  (Stacks.commRingSheafFiberIso Φ O).hom.hom.comp
    (Φ.toPresheafFiber V y (ringPresheaf O)).hom

/-- The germ at `(V, y)` of a section `s` of a presheaf of modules `M`, as an element of the
stalk `(stalkPres O Φ).obj M`. -/
abbrev germMod (M : PresheafOfModules.{u} (ringPresheaf O)) (V : C) (y : Φ.fiber.obj V)
    (s : M.obj (op V)) : (stalkPres O Φ).obj M :=
  Stacks.toPresheafModuleFiber Φ M V y s

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The germ of `r • s` is the germ of `r` acting on the germ of `s`. -/
lemma germMod_smul (M : PresheafOfModules.{u} (ringPresheaf O)) (V : C) (y : Φ.fiber.obj V)
    (r : (ringPresheaf O).obj (op V)) (s : M.obj (op V)) :
    germMod O Φ M V y (r • s) = germHom O Φ V y r • germMod O Φ M V y s :=
  (Stacks.toPresheafModuleFiber_smul Φ M V y r s).trans
    (congrArg (fun scalar => scalar • Stacks.toPresheafModuleFiber Φ M V y s)
      (ConcreteCategory.congr_hom (Stacks.commRingSheafFiberIso Φ O).hom_inv_id
        ((Φ.toPresheafFiber V y (ringPresheaf O)).hom r)).symm)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The germ of the zero section is zero. -/
lemma germMod_zero (M : PresheafOfModules.{u} (ringPresheaf O)) (V : C) (y : Φ.fiber.obj V) :
    germMod O Φ M V y 0 = 0 := map_zero _

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The germ of a sum of sections is the sum of their germs. -/
lemma germMod_add (M : PresheafOfModules.{u} (ringPresheaf O)) (V : C) (y : Φ.fiber.obj V)
    (s t : M.obj (op V)) :
    germMod O Φ M V y (s + t) = germMod O Φ M V y s + germMod O Φ M V y t := map_add _ _ _

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The germ of a finite sum of sections is the sum of their germs. -/
lemma germMod_sum {ι : Type*} (M : PresheafOfModules.{u} (ringPresheaf O)) (V : C)
    (y : Φ.fiber.obj V) (s : Finset ι) (g : ι → M.obj (op V)) :
    germMod O Φ M V y (∑ i ∈ s, g i) = ∑ i ∈ s, germMod O Φ M V y (g i) := map_sum _ _ _

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The germ at `(V, y)` of the restriction of `s` along `f : V ⟶ W` is the germ of `s` at
`(W, Φ.fiber.map f y)`. -/
lemma germMod_restrict (M : PresheafOfModules.{u} (ringPresheaf O)) {V W : C} (f : V ⟶ W)
    (y : Φ.fiber.obj V) (s : M.obj (op W)) :
    germMod O Φ M V y (M.map f.op s) = germMod O Φ M W (Φ.fiber.map f y) s :=
  (Stacks.toPresheafModuleFiber_w Φ M f y s).symm

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The germ at `(V, y)` of the restriction of a section `s` of `O` along `f : V ⟶ W` is the
germ of `s` at `(W, Φ.fiber.map f y)`. -/
lemma germHom_restrict {V W : C} (f : V ⟶ W) (y : Φ.fiber.obj V)
    (s : (ringPresheaf O).obj (op W)) :
    germHom O Φ V y ((ringPresheaf O).map f.op s) = germHom O Φ W (Φ.fiber.map f y) s :=
  congrArg (Stacks.commRingSheafFiberIso Φ O).hom.hom
    (Φ.toPresheafFiber_w_apply f y (ringPresheaf O) s)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Every element of the stalk `O_Φ` is the germ of a section of `O` over some neighbourhood. -/
lemma exists_germHom (a : structureStalk O Φ) :
    ∃ (V : C) (y : Φ.fiber.obj V) (s : (ringPresheaf O).obj (op V)), germHom O Φ V y s = a := by
  obtain ⟨V, y, s, hs⟩ := Φ.toPresheafFiber_jointly_surjective
    (P := ringPresheaf O) ((Stacks.commRingSheafFiberIso Φ O).inv.hom a)
  exact ⟨V, y, s, (congrArg (Stacks.commRingSheafFiberIso Φ O).hom.hom hs).trans
    (ConcreteCategory.congr_hom (Stacks.commRingSheafFiberIso Φ O).inv_hom_id a)⟩

/-! ### The free presheaf of modules on `n` copies of the representable at `U` -/

/-- The presheaf of sets `V ↦ Fin n × (V ⟶ U)`. -/
def freeIndex (U : C) (n : ℕ) : Cᵒᵖ ⥤ Type u where
  obj V := Fin n × (V.unop ⟶ U)
  map {V W} f := ↾fun (p : Fin n × (V.unop ⟶ U)) =>
    ((p.1, f.unop ≫ p.2) : Fin n × (W.unop ⟶ U))

/-- The presheaf `freeIndex U n` acts on `(i, ψ)` by precomposing `ψ`. -/
@[simp]
lemma freeIndex_map_apply (U : C) (n : ℕ) {V W : Cᵒᵖ} (f : V ⟶ W)
    (p : Fin n × (V.unop ⟶ U)) :
    (freeIndex U n).map f p = (p.1, f.unop ≫ p.2) := rfl

/-- The free presheaf of `O`-modules on `n` copies of the representable at `U`. -/
abbrev freePres (U : C) (n : ℕ) : PresheafOfModules.{u} (ringPresheaf O) :=
  PresheafOfModules.freeObj (freeIndex U n)

/-- The tautological generator of `freePres O U n` over `V` indexed by `(i, ψ)`. -/
abbrev gen (U : C) (n : ℕ) (V : C) (q : Fin n × (V ⟶ U)) : (freePres O U n).obj (op V) :=
  ModuleCat.freeMk q

/-- The generator indexed by `(i, ψ)` scaled by a section `c` of the structure sheaf. -/
def gens (U : C) (n : ℕ) (V : C) (q : Fin n × (V ⟶ U)) (c : (ringPresheaf O).obj (op V)) :
    (freePres O U n).obj (op V) :=
  c • gen O U n V q

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The scaled generator `gens O U n V q c` is the finitely supported function `single q c`. -/
lemma gens_eq_single (U : C) (n : ℕ) (V : C) (q : Fin n × (V ⟶ U))
    (c : (ringPresheaf O).obj (op V)) :
    gens O U n V q c = (Finsupp.single q c : (freePres O U n).obj (op V)) :=
  Finsupp.smul_single_one q c

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Induction on a section of `freePres O U n`, stated at the type that section has, so that
the zero and the sums carry the module structure of `freePres`. -/
lemma freePres_induction (U : C) (n : ℕ) {V : C}
    {P : ((freePres O U n).obj (op V) : Type u) → Prop}
    (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hs : ∀ (q : Fin n × (V ⟶ U)) (c : (ringPresheaf O).obj (op V)),
      P (Finsupp.single q c : (freePres O U n).obj (op V)))
    (x : (freePres O U n).obj (op V)) : P x := by
  induction x using Finsupp.induction_linear with
  | zero => exact h0
  | add a b ha hb => exact hadd a b ha hb
  | single q c => exact hs q c

/-- The restriction map of `freePres O U n` along `f`, with its target spelled as a module
over the smaller object rather than as a restriction of scalars. -/
def restr (U : C) (n : ℕ) {V W : C} (f : V ⟶ W) (c : (freePres O U n).obj (op W)) :
    (freePres O U n).obj (op V) :=
  (freePres O U n).map f.op c

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Restriction sends zero to zero. -/
lemma restr_zero (U : C) (n : ℕ) {V W : C} (f : V ⟶ W) :
    restr O U n f (0 : (freePres O U n).obj (op W)) = 0 := map_zero _

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Restriction is additive. -/
lemma restr_add (U : C) (n : ℕ) {V W : C} (f : V ⟶ W) (a b : (freePres O U n).obj (op W)) :
    restr O U n f (a + b) = restr O U n f a + restr O U n f b := map_add _ _ _

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Restricting the generator indexed by `(i, ψ)` along `f` gives the generator indexed by
`(i, f ≫ ψ)`. -/
lemma restr_gen (U : C) (n : ℕ) {V W : C} (f : V ⟶ W) (q : Fin n × (W ⟶ U)) :
    restr O U n f (gen O U n W q) = gen O U n V (q.1, f ≫ q.2) := by
  show (freePres O U n).map f.op (gen O U n W q) = _
  rw [PresheafOfModules.freeObj_map]
  exact ModuleCat.freeDesc_apply _ _

/-- Restricting the generator indexed by `(i, ψ)` scaled by `c` along `f` gives the generator
indexed by `(i, f ≫ ψ)` scaled by the restriction of `c`. -/
lemma restr_gens (U : C) (n : ℕ) {V W : C} (f : V ⟶ W) (q : Fin n × (W ⟶ U))
    (c : (ringPresheaf O).obj (op W)) :
    restr O U n f (gens O U n W q c)
      = gens O U n V (q.1, f ≫ q.2) ((ringPresheaf O).map f.op c) := by
  have h : restr O U n f (gens O U n W q c)
      = (ringPresheaf O).map f.op c • restr O U n f (gen O U n W q) :=
    PresheafOfModules.map_smul _ _ _ _
  rw [h, restr_gen]
  rfl

/-! ### The coefficient map at a distinguished point of the fibre -/

variable (U : C) (n : ℕ) (x₀ : Φ.fiber.obj U) [DecidableEq (Φ.fiber.obj U)]

/-- The `(U, x₀)`-coefficient map over a neighbourhood `(V, y)`: it sends the generator
indexed by `(i, ψ)` to the `i`-th standard basis vector if `u(ψ)(y) = x₀`, and to zero
otherwise. It is a map of `O(V)`-modules into `Fin n → O_Φ` with scalars restricted along
the germ map. -/
def coeffAt (V : C) (y : Φ.fiber.obj V) :
    (freePres O U n).obj (op V) ⟶ (ModuleCat.restrictScalars (germHom O Φ V y)).obj
      (ModuleCat.of (structureStalk O Φ)
        (Fin n → structureStalk O Φ)) :=
  ModuleCat.freeDesc (↾fun q =>
    (if Φ.fiber.map q.2 y = x₀ then Pi.single q.1 1 else 0 :
      Fin n → structureStalk O Φ))

/-- `coeffAt` as a plain function to `Fin n → O_Φ`. -/
abbrev coeff (V : C) (y : Φ.fiber.obj V) (c : (freePres O U n).obj (op V)) :
    Fin n → structureStalk O Φ :=
  coeffAt O Φ U n x₀ V y c

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The coefficient of the generator indexed by `(i, ψ)` is the `i`-th basis vector if
`u(ψ)(y) = x₀`, and zero otherwise. -/
lemma coeff_gen (V : C) (y : Φ.fiber.obj V) (q : Fin n × (V ⟶ U)) :
    coeff O Φ U n x₀ V y (gen O U n V q)
      = if Φ.fiber.map q.2 y = x₀ then Pi.single q.1 1 else 0 :=
  ModuleCat.freeDesc_apply _ _

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The coefficient map is additive. -/
lemma coeff_add (V : C) (y : Φ.fiber.obj V) (c c' : (freePres O U n).obj (op V)) :
    coeff O Φ U n x₀ V y (c + c') = coeff O Φ U n x₀ V y c + coeff O Φ U n x₀ V y c' :=
  map_add _ _ _

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The coefficient map sends zero to zero. -/
lemma coeff_zero (V : C) (y : Φ.fiber.obj V) :
    coeff O Φ U n x₀ V y (0 : (freePres O U n).obj (op V)) = 0 := map_zero _

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The coefficient map is semilinear along the germ map: the coefficient of `r • c` is the
germ of `r` times the coefficient of `c`. -/
lemma coeff_smul (V : C) (y : Φ.fiber.obj V) (r : (ringPresheaf O).obj (op V))
    (c : (freePres O U n).obj (op V)) :
    coeff O Φ U n x₀ V y (r • c) = germHom O Φ V y r • coeff O Φ U n x₀ V y c := by
  have h0 : coeffAt O Φ U n x₀ V y (r • c) = r • coeffAt O Φ U n x₀ V y c := map_smul _ _ _
  have h1 := ModuleCat.restrictScalars.smul_def (f := germHom O Φ V y)
      (M := ModuleCat.of (structureStalk O Φ : Type u)
        (Fin n → (structureStalk O Φ : Type u))) r (coeffAt O Φ U n x₀ V y c)
  show coeffAt O Φ U n x₀ V y (r • c) = _
  rw [h0, h1]

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The coefficient of the generator indexed by `(i, ψ)` scaled by `c` is the germ of `c` in
the `i`-th coordinate if `u(ψ)(y) = x₀`, and zero otherwise. -/
lemma coeff_gens (V : C) (y : Φ.fiber.obj V) (q : Fin n × (V ⟶ U))
    (c : (ringPresheaf O).obj (op V)) :
    coeff O Φ U n x₀ V y (gens O U n V q c)
      = if Φ.fiber.map q.2 y = x₀ then Pi.single q.1 (germHom O Φ V y c) else 0 := by
  have h0 : coeff O Φ U n x₀ V y (gens O U n V q c)
      = germHom O Φ V y c • coeff O Φ U n x₀ V y (gen O U n V q) :=
    coeff_smul O Φ U n x₀ V y c (gen O U n V q)
  rw [h0, coeff_gen]
  by_cases h : Φ.fiber.map q.2 y = x₀
  · rw [ite_eq_left h, ite_eq_left h, ← Pi.single_smul', smul_eq_mul, mul_one]
  · rw [ite_eq_right h, ite_eq_right h, smul_zero]

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The coefficient at `(V, y)` of the restriction of `c` along `f : V ⟶ W` is the coefficient
of `c` at `(W, Φ.fiber.map f y)`. -/
lemma coeff_restrict {V W : C} (f : V ⟶ W) (y : Φ.fiber.obj V)
    (c : (freePres O U n).obj (op W)) :
    coeff O Φ U n x₀ V y (restr O U n f c) = coeff O Φ U n x₀ W (Φ.fiber.map f y) c := by
  induction c using freePres_induction with
  | h0 => rw [restr_zero, coeff_zero, coeff_zero]
  | hadd a b ha hb => rw [restr_add, coeff_add, coeff_add, ha, hb]
  | hs q c₀ =>
      rw [← gens_eq_single, restr_gens, coeff_gens, coeff_gens, germHom_restrict,
        CategoryTheory.Functor.map_comp_apply]

/-! ### The projection and the inclusion at the stalk -/

/-- The coefficient map as a morphism of abelian groups out of the sections over `(V, y)`. -/
def coeffAdd (V : C) (y : Φ.fiber.obj V) :
    (freePres O U n).presheaf.obj (op V) ⟶
      AddCommGrpCat.of (Fin n → structureStalk O Φ) :=
  AddCommGrpCat.ofHom (coeffAt O Φ U n x₀ V y).hom.toAddMonoidHom

/-- The maps `coeffAdd` are compatible with the restriction maps of `freePres O U n`. -/
lemma coeffAdd_naturality : ∀ ⦃V W : C⦄ (f : V ⟶ W) (y : Φ.fiber.obj V),
    (freePres O U n).presheaf.map f.op ≫ coeffAdd O Φ U n x₀ V y
      = coeffAdd O Φ U n x₀ W (Φ.fiber.map f y) :=
  fun _ _ f y => ConcreteCategory.hom_ext _ _ fun c => coeff_restrict O Φ U n x₀ f y c

/-- The `(U, x₀)`-coefficient map on the stalk, as a morphism of abelian groups. -/
def projAdd : (Φ.presheafFiber (A := AddCommGrpCat.{u})).obj (freePres O U n).presheaf ⟶
    AddCommGrpCat.of (Fin n → structureStalk O Φ) :=
  Φ.presheafFiberDesc (coeffAdd O Φ U n x₀) (coeffAdd_naturality O Φ U n x₀)

/-- `projAdd` sends the germ of `c` at `(V, y)` to the coefficient of `c` at `(V, y)`. -/
lemma projAdd_germ (V : C) (y : Φ.fiber.obj V) (c : (freePres O U n).obj (op V)) :
    projAdd O Φ U n x₀ (germMod O Φ (freePres O U n) V y c) = coeff O Φ U n x₀ V y c :=
  ConcreteCategory.congr_hom
    (Φ.toPresheafFiber_presheafFiberDesc (P := (freePres O U n).presheaf)
      (coeffAdd O Φ U n x₀) (coeffAdd_naturality O Φ U n x₀) V y) c

/-- **The `(U, x₀)`-coefficient map on the stalk**, as a morphism of `O_Φ`-modules
`(freePres O U n)_Φ ⟶ O_Φ^n`. -/
def proj : (stalkPres O Φ).obj (freePres O U n) ⟶
    ModuleCat.of (structureStalk O Φ)
      (Fin n → structureStalk O Φ) :=
  ConcreteCategory.ofHom
    { toFun := fun l => projAdd O Φ U n x₀ l
      map_add' := fun a b => map_add _ _ _
      map_smul' := by
        intro a l
        obtain ⟨V, y, s, hs⟩ := exists_germHom O Φ a
        obtain ⟨W, w, c, hc⟩ :=
          Stacks.toPresheafModuleFiber_jointly_surjective Φ (freePres O U n) l
        obtain ⟨Z, z, f₁, f₂, hf₁, hf₂⟩ := Stacks.exists_common_neighbourhood Φ y w
        have ha : germHom O Φ Z z ((ringPresheaf O).map f₁.op s) = a := by
          rw [germHom_restrict, hf₁, hs]
        have hl : germMod O Φ (freePres O U n) Z z (restr O U n f₂ c) = l := by
          rw [show restr O U n f₂ c = (freePres O U n).map f₂.op c from rfl,
            germMod_restrict, hf₂]
          exact hc
        have hsmul : germMod O Φ (freePres O U n) Z z
              (((ringPresheaf O).map f₁.op s) • restr O U n f₂ c)
            = a • germMod O Φ (freePres O U n) Z z (restr O U n f₂ c) := by
          rw [germMod_smul, ha]
        simp only [RingHom.id_apply]
        rw [← hl, ← hsmul]
        change projAdd O Φ U n x₀ _ = a • projAdd O Φ U n x₀ _
        rw [projAdd_germ, projAdd_germ, coeff_smul, ha] }

/-- **The inclusion of `O_Φ^n` into the stalk of `freePres O U n`**: the `i`-th basis vector
goes to the germ at `(U, x₀)` of the `i`-th tautological generator. -/
def incl : ModuleCat.of (structureStalk O Φ)
      (Fin n → structureStalk O Φ) ⟶ (stalkPres O Φ).obj (freePres O U n) :=
  ConcreteCategory.ofHom
    { toFun := fun v => ∑ i, v i • germMod O Φ (freePres O U n) U x₀ (gen O U n U (i, 𝟙 U))
      map_add' := by
        intro v w
        simp only [Pi.add_apply, add_smul]
        exact Finset.sum_add_distrib
      map_smul' := by
        intro a v
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul] }

/-- `proj` sends the germ at `(U, x₀)` of the `i`-th tautological generator to the `i`-th
basis vector. -/
lemma proj_gen (i : Fin n) :
    proj O Φ U n x₀ (germMod O Φ (freePres O U n) U x₀ (gen O U n U (i, 𝟙 U)))
      = (Pi.single i 1 : Fin n → structureStalk O Φ) := by
  show projAdd O Φ U n x₀ _ = _
  rw [projAdd_germ, coeff_gen]
  have h : Φ.fiber.map ((i, 𝟙 U) : Fin n × (U ⟶ U)).2 x₀ = x₀ := by simp
  rw [ite_eq_left h]

/-- **`incl` is a section of `proj`**: `incl ≫ proj` is the identity of `O_Φ^n`. -/
lemma incl_proj : incl O Φ U n x₀ ≫ proj O Φ U n x₀ = 𝟙 _ := by
  refine ConcreteCategory.hom_ext _ _ (fun v => ?_)
  show proj O Φ U n x₀
    (∑ i, v i • germMod O Φ (freePres O U n) U x₀ (gen O U n U (i, 𝟙 U))) = v
  rw [map_sum]
  have key : ∀ i : Fin n, proj O Φ U n x₀ (v i •
      germMod O Φ (freePres O U n) U x₀ (gen O U n U (i, 𝟙 U))) = Pi.single i (v i) := by
    intro i
    rw [map_smul, proj_gen, ← Pi.single_smul', smul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  exact Finset.univ_sum_single v

/-- The germ at `(U, x₀)` of the `i`-th tautological generator. -/
abbrev basisGerm : Fin n → ((stalkPres O Φ).obj (freePres O U n) : Type u) :=
  fun i => germMod O Φ (freePres O U n) U x₀ (gen O U n U (i, 𝟙 U))

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [DecidableEq (Φ.fiber.obj U)] in
/-- `incl` sends `v` to `∑ i, v i • basisGerm i`. -/
lemma incl_apply (v : Fin n → structureStalk O Φ) :
    incl O Φ U n x₀ v = ∑ i, v i • basisGerm O Φ U n x₀ i := rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The map on stalks induced by `ψ : M ⟶ M'` sends the germ of `c` to the germ of
`ψ.app (op V) c`. -/
lemma stalkPres_map_germ {M M' : PresheafOfModules.{u} (ringPresheaf O)} (ψ : M ⟶ M')
    (V : C) (y : Φ.fiber.obj V) (c : M.obj (op V)) :
    (stalkPres O Φ).map ψ (germMod O Φ M V y c) = germMod O Φ M' V y (ψ.app (op V) c) :=
  Stacks.toPresheafModuleFiber_naturality Φ ψ V y c

/-! ### The morphism attached to a matrix of sections over `U` -/

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Scaling `gens O U n V q c'` by `c` gives `gens O U n V q (c * c')`. -/
lemma gens_smul (V : C) (q : Fin n × (V ⟶ U)) (c c' : (ringPresheaf O).obj (op V)) :
    c • gens O U n V q c' = gens O U n V q (c * c') :=
  smul_smul c c' _

/-- The natural transformation `freeIndex U m ⟶ freePres O U n` attached to a matrix of
sections of `O` over `U`: the generator indexed by `(j, ψ)` goes to the `j`-th column of the
matrix, restricted along `ψ`. -/
def matrixNat (m : ℕ) (A : Fin m → Fin n → (ringPresheaf O).obj (op U)) :
    freeIndex U m ⟶ (freePres O U n).presheaf ⋙ forget _ where
  app V := ↾fun (q : Fin m × (V.unop ⟶ U)) =>
    (∑ i, gens O U n V.unop (i, q.2) ((ringPresheaf O).map q.2.op (A q.1 i)) :
      (freePres O U n).obj (op V.unop))
  naturality X Y f := by
    ext q
    have hmap : ((freePres O U n).map f (∑ i, gens O U n X.unop (i, q.2)
          ((ringPresheaf O).map q.2.op (A q.1 i))) : (freePres O U n).obj Y)
        = ∑ i, gens O U n Y.unop (i, f.unop ≫ q.2)
            ((ringPresheaf O).map (f.unop ≫ q.2).op (A q.1 i)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      change restr O U n f.unop (gens O U n X.unop (i, q.2) _) = _
      rw [restr_gens]
      exact congrArg _
        (ConcreteCategory.congr_hom ((ringPresheaf O).map_comp q.2.op f) (A q.1 i)).symm
    exact hmap.symm

/-- The morphism `freePres O U m ⟶ freePres O U n` attached to a matrix of sections of `O`
over `U`. -/
def matrixHom (m : ℕ) (A : Fin m → Fin n → (ringPresheaf O).obj (op U)) :
    freePres O U m ⟶ freePres O U n :=
  PresheafOfModules.freeObjDesc (R := ringPresheaf O) (G := freePres O U n)
    (matrixNat O U n m A)

/-- `matrixHom` sends the generator indexed by `(j, ψ)` to the `j`-th column of the matrix,
restricted along `ψ`. -/
lemma matrixHom_gen (m : ℕ) (A : Fin m → Fin n → (ringPresheaf O).obj (op U))
    (V : C) (q : Fin m × (V ⟶ U)) :
    (matrixHom O U n m A).app (op V) (gen O U m V q)
      = ∑ i, gens O U n V (i, q.2) ((ringPresheaf O).map q.2.op (A q.1 i)) := by
  rw [matrixHom, PresheafOfModules.freeObjDesc_app]
  exact ModuleCat.freeDesc_apply _ _

/-- `matrixHom` sends the generator indexed by `(j, ψ)` scaled by `c` to the `j`-th column of
the matrix, restricted along `ψ` and scaled by `c`. -/
lemma matrixHom_gens (m : ℕ) (A : Fin m → Fin n → (ringPresheaf O).obj (op U))
    (V : C) (q : Fin m × (V ⟶ U)) (c : (ringPresheaf O).obj (op V)) :
    (matrixHom O U n m A).app (op V) (gens O U m V q c)
      = ∑ i, gens O U n V (i, q.2) (c * (ringPresheaf O).map q.2.op (A q.1 i)) := by
  have h : (matrixHom O U n m A).app (op V) (gens O U m V q c)
      = c • (matrixHom O U n m A).app (op V) (gen O U m V q) := map_smul _ _ _
  rw [h, matrixHom_gen, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => gens_smul O U n V _ _ _)

/-- The `O_Φ`-linear map `O_Φ^m ⟶ O_Φ^n` given by the germs at `(U, x₀)` of the matrix. -/
def germMatrix (m : ℕ) (A : Fin m → Fin n → (ringPresheaf O).obj (op U)) :
    ModuleCat.of (structureStalk O Φ)
      (Fin m → structureStalk O Φ) ⟶
    ModuleCat.of (structureStalk O Φ)
      (Fin n → structureStalk O Φ) :=
  ModuleCat.ofHom
    { toFun := fun w i => ∑ j, w j * germHom O Φ U x₀ (A j i)
      map_add' := by
        intro v w
        funext i
        simp only [Pi.add_apply, add_mul]
        exact Finset.sum_add_distrib
      map_smul' := by
        intro a v
        funext i
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc] }

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [DecidableEq (Φ.fiber.obj U)] in
/-- The `i`-th coordinate of `germMatrix A w` is `∑ j, w j * germ (A j i)`. -/
lemma germMatrix_apply (m : ℕ) (A : Fin m → Fin n → (ringPresheaf O).obj (op U))
    (w : Fin m → structureStalk O Φ) (i : Fin n) :
    germMatrix O Φ U n x₀ m A w i = ∑ j, w j * germHom O Φ U x₀ (A j i) := rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [DecidableEq (Φ.fiber.obj U)] in
/-- The `i`-th coordinate of `germMatrix A (Pi.single j a)` is `a * germ (A j i)`. -/
lemma germMatrix_single (m : ℕ) (A : Fin m → Fin n → (ringPresheaf O).obj (op U))
    (j : Fin m) (a : structureStalk O Φ) (i : Fin n) :
    germMatrix O Φ U n x₀ m A (Pi.single j a) i = a * germHom O Φ U x₀ (A j i) := by
  rw [germMatrix_apply, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
    (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_mul]), Pi.single_eq_same]

/-! ### The two intertwining squares -/

/-- `proj` sends the germ of `c` at `(V, y)` to the coefficient of `c` at `(V, y)`. -/
lemma proj_germ (V : C) (y : Φ.fiber.obj V) (c : (freePres O U n).obj (op V)) :
    proj O Φ U n x₀ (germMod O Φ (freePres O U n) V y c) = coeff O Φ U n x₀ V y c :=
  projAdd_germ O Φ U n x₀ V y c

/-- `proj` commutes with finite sums. -/
lemma proj_sum {ι : Type*} (s : Finset ι)
    (g : ι → ((stalkPres O Φ).obj (freePres O U n) : Type u)) :
    proj O Φ U n x₀ (∑ i ∈ s, g i) = ∑ i ∈ s, proj O Φ U n x₀ (g i) := map_sum _ _ _

omit [DecidableEq (Φ.fiber.obj U)] in
/-- The map on stalks induced by `matrixHom A` sends the `j`-th basis germ to
`∑ i, germ (A j i) • basisGerm i`. -/
lemma stalkMap_basisGerm (m : ℕ) (A : Fin m → Fin n → (ringPresheaf O).obj (op U)) (j : Fin m) :
    (stalkPres O Φ).map (matrixHom O U n m A) (basisGerm O Φ U m x₀ j)
      = ∑ i, germHom O Φ U x₀ (A j i) • basisGerm O Φ U n x₀ i := by
  rw [stalkPres_map_germ, matrixHom_gen, germMod_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hid : (ringPresheaf O).map ((𝟙 U).op) (A j i) = A j i := by simp
  rw [hid]
  exact germMod_smul O Φ (freePres O U n) U x₀ (A j i) (gen O U n U (i, 𝟙 U))

omit [DecidableEq (Φ.fiber.obj U)] in
/-- **The inclusion intertwines the matrix of germs with the matrix morphism.** -/
lemma incl_comp_stalkMap (m : ℕ) (A : Fin m → Fin n → (ringPresheaf O).obj (op U)) :
    incl O Φ U m x₀ ≫ (stalkPres O Φ).map (matrixHom O U n m A)
      = germMatrix O Φ U n x₀ m A ≫ incl O Φ U n x₀ := by
  refine ConcreteCategory.hom_ext _ _ (fun v => ?_)
  show (stalkPres O Φ).map (matrixHom O U n m A) (∑ j, v j • basisGerm O Φ U m x₀ j)
    = ∑ i, germMatrix O Φ U n x₀ m A v i • basisGerm O Φ U n x₀ i
  rw [map_sum]
  have h1 : ∀ j : Fin m, (stalkPres O Φ).map (matrixHom O U n m A)
      (v j • basisGerm O Φ U m x₀ j)
      = ∑ i, (v j * germHom O Φ U x₀ (A j i)) • basisGerm O Φ U n x₀ i := by
    intro j
    rw [map_smul, stalkMap_basisGerm, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i _ => (smul_smul _ _ _))
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_smul]
  rfl

/-- **The projection intertwines the matrix morphism with the matrix of germs.** -/
lemma stalkMap_comp_proj (m : ℕ) (A : Fin m → Fin n → (ringPresheaf O).obj (op U)) :
    (stalkPres O Φ).map (matrixHom O U n m A) ≫ proj O Φ U n x₀
      = proj O Φ U m x₀ ≫ germMatrix O Φ U n x₀ m A := by
  refine ConcreteCategory.hom_ext _ _ (fun l => ?_)
  obtain ⟨V, y, c, rfl⟩ :=
    Stacks.toPresheafModuleFiber_jointly_surjective Φ (freePres O U m) l
  show proj O Φ U n x₀ ((stalkPres O Φ).map (matrixHom O U n m A)
      (germMod O Φ (freePres O U m) V y c))
    = germMatrix O Φ U n x₀ m A (proj O Φ U m x₀ (germMod O Φ (freePres O U m) V y c))
  induction c using freePres_induction with
  | h0 =>
      rw [germMod_zero]
      simp only [map_zero]
  | hadd a b ha hb =>
      rw [germMod_add]
      simp only [map_add]
      rw [ha, hb]
  | hs q c₀ =>
      rw [← gens_eq_single, stalkPres_map_germ, matrixHom_gens, germMod_sum, proj_sum]
      by_cases h : Φ.fiber.map q.2 y = x₀
      · have hL : ∀ i : Fin n, proj O Φ U n x₀ (germMod O Φ (freePres O U n) V y
              (gens O U n V (i, q.2) (c₀ * (ringPresheaf O).map q.2.op (A q.1 i))))
            = Pi.single i (germHom O Φ V y c₀ * germHom O Φ U x₀ (A q.1 i)) := by
          intro i
          rw [proj_germ, coeff_gens, ite_eq_left h, map_mul, germHom_restrict, h]
        rw [Finset.sum_congr rfl (fun i _ => hL i), Finset.univ_sum_single, proj_germ,
          coeff_gens, ite_eq_left h]
        funext i
        rw [germMatrix_single]
      · have hL : ∀ i : Fin n, proj O Φ U n x₀ (germMod O Φ (freePres O U n) V y
              (gens O U n V (i, q.2) (c₀ * (ringPresheaf O).map q.2.op (A q.1 i)))) = 0 := by
          intro i
          rw [proj_germ, coeff_gens, ite_eq_right h]
        rw [Finset.sum_congr rfl (fun i _ => hL i), Finset.sum_const_zero, proj_germ,
          coeff_gens, ite_eq_right h, map_zero]

end Stacks.Sheaves.FreeModuleStalk

end

end
