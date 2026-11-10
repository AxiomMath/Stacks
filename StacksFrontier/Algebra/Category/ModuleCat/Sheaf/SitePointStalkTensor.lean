module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleStalkFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk of a tensor product of presheaves of modules at a point of a site

Let `(C, J)` be a site, `Φ` a point of it, and `O` a presheaf of commutative rings on `C`. For
two presheaves of `O`-modules `M` and `N`, the stalk at `Φ` of the presheaf tensor product
`U ↦ M(U) ⊗_{O(U)} N(U)` is the tensor product of the stalks over the stalk ring `O_Φ`:

`(M ⊗_O N)_Φ ≅ M_Φ ⊗_{O_Φ} N_Φ`,

naturally in `M` and in `N`. This is the case of Stacks 03EL for the morphism of ringed topoi
given by a point of the site, at the level of presheaves of modules.

## Main definitions

* `Stacks.presheafModuleFiberOfCommRing Φ O` is the stalk functor on presheaves of modules
  over the underlying presheaf of rings of `O`, valued in modules over the `CommRingCat`-valued
  stalk `O_Φ`; it is the presheaf-level counterpart of `Stacks.sheafModuleFiberOfCommRing`.
* `Stacks.germ Φ O M U x` is the germ map `M(U) →+ M_Φ` at a neighbourhood `(U, x)` of `Φ`.
* `Stacks.meet`, `Stacks.meetPt`, `Stacks.meetFst`, `Stacks.meetSnd` are a canonical common
  refinement of two neighbourhoods of `Φ`, taken from the cofilteredness of
  `Φ.fiber.Elements`.
* `Stacks.fwdHom` and `Stacks.bwdHom` are the two comparison maps.

## Main results

* `Stacks.presheafModuleFiberTensorEquiv`: **tensor product commutes with the filtered colimit
  defining the stalk, over the varying base ring.** The comparison is characterised on germs of
  pure tensors by `Stacks.presheafModuleFiberTensorEquiv_germ_tmul`, and its inverse by
  `Stacks.presheafModuleFiberTensorEquiv_symm_germ_tmul`.
* `Stacks.moduleFiberTensorIso`, the same comparison read as an isomorphism in
  `ModuleCat O_Φ` with the target written through `MonoidalCategory.curriedTensor`, together
  with `Stacks.moduleFiberTensorIso_naturality_left` and
  `Stacks.moduleFiberTensorIso_naturality_right`.

## Implementation notes

Mathlib has this for a *fixed* base ring: `GrothendieckTopology.Point.presheafFiber` is
monoidal whenever the target category is monoidal with tensor commuting with filtered colimits
(`Mathlib/CategoryTheory/Sites/Point/Monoidal.lean`), and for modules a monoidal target means a
fixed ring. Here the ring varies with the neighbourhood, so the colimit is over a diagram of
*triples* (ring, module, module) and none of that machinery applies. The proof is therefore the
element-level one: `fwdHom` is built from the universal property of the colimit
(`GrothendieckTopology.Point.presheafFiberDesc`) applied to the `O(U)`-balanced legs
`m ⊗ n ↦ (germ m) ⊗ (germ n)`, and `bwdHom` from two nested applications of the same universal
property followed by `TensorProduct.liftAddHom`. The one place where the varying ring is dealt
with is `Stacks.bwdBiAdd_balance`.

Three spelling decisions are load-bearing, each forced by a failure:

* Restriction of sections is written `PresheafOfModules.restrictₛₗ f.op m`, never
  `M.map f.op m`. The latter has type `(ModuleCat.restrictScalars _).obj (M.obj _)` rather
  than `M.obj _`, and a `rw` whose instantiation produces such a term is rejected when the
  result is re-checked at `instances` transparency. A type ascription does not help: the term
  keeps its own type.
* Sections of the tensor product are handled through `Stacks.tensorSections`,
  `Stacks.tensorRestrict`, `Stacks.tensorGerm` and `Stacks.resTmul`, whose types are written
  in the `TensorProduct` spelling rather than as `(M ⊗ N).obj (op U)`. The additive structures
  of the two spellings are definitionally equal but not syntactically equal, so `map_add` and
  `map_zero` do not fire on the terms `TensorProduct.induction_on` produces unless the
  additive maps are stated at the tensor-product spelling.
* Germ equalities between different common refinements all go through
  `Stacks.germ_resTmul_eq` and `Stacks.germ_resTmul_eq_self`. On a general site two morphisms
  of neighbourhoods with the same source and target need not be equal — the ringed-space proof
  of Stacks 01CB closes those steps with the partial order on `Opens` — so they are made equal
  by passing to a smaller neighbourhood, which is `Stacks.exists_eq_nbhd` and
  `Stacks.exists_eq_nbhd₂`.

Mathlib's `PresheafOfModules.Monoidal` is used only through its results; nothing is proved in
its style.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C} (Φ : J.Point.{w}) (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-- The `CommRingCat`-valued stalk of `O` at `Φ`. -/
noncomputable abbrev ringFiber : CommRingCat.{w} :=
  (Φ.presheafFiber (A := CommRingCat.{w})).obj O

/-- The ring homomorphism from the `CommRingCat`-valued stalk of `O` to the `RingCat`-valued
stalk of the underlying presheaf of rings. -/
noncomputable abbrev toRingFiber :
    ringFiber Φ O →+*
      (Φ.presheafFiber (A := RingCat.{w})).obj (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}) :=
  (commRingPresheafFiberIso Φ O).inv.hom

/-- The stalk functor on presheaves of modules over the underlying presheaf of rings of a
presheaf of commutative rings, valued in modules over the `CommRingCat`-valued stalk. -/
noncomputable def presheafModuleFiberOfCommRing :
    PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ⥤
      ModuleCat.{w} (ringFiber Φ O) :=
  presheafModuleFiber Φ (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ⋙
    ModuleCat.restrictScalars.{w} (toRingFiber Φ O)

/-- The stalk of a presheaf of modules at `Φ`, as a module over the `CommRingCat`-valued
stalk of `O`. -/
noncomputable abbrev moduleFiber
    (M : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})) :
    ModuleCat.{w} (ringFiber Φ O) :=
  (presheafModuleFiberOfCommRing Φ O).obj M

/-- The germ of a section of `O` over a neighbourhood of `Φ`. -/
noncomputable abbrev ringGerm (U : C) (x : Φ.fiber.obj U) (r : O.obj (op U)) : ringFiber Φ O :=
  Φ.toPresheafFiber U x O r

/-- The germ of a section of a presheaf of modules over a neighbourhood of `Φ`, landing in the
stalk read as a module over the `CommRingCat`-valued stalk of `O`. -/
noncomputable def germ (M : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}))
    (U : C) (x : Φ.fiber.obj U) : M.obj (op U) →+ moduleFiber Φ O M :=
  toPresheafModuleFiber Φ M U x

variable {Φ O}

/-- The germ of a section of `O` in the `CommRingCat`-valued stalk is carried to the germ in
the `RingCat`-valued stalk. -/
lemma toRingFiber_germ (U : C) (x : Φ.fiber.obj U) (r : O.obj (op U)) :
    toRingFiber Φ O (ringGerm Φ O U x r) =
      Φ.toPresheafFiber U x (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}) r := by
  have h := ConcreteCategory.congr_hom (Φ.toPresheafFiber_presheafFiberCompIso_hom_app
    (F := forget₂ CommRingCat.{w} RingCat.{w}) U x O) r
  rw [CategoryTheory.comp_apply] at h
  refine (congrArg (toRingFiber Φ O) h.symm).trans ?_
  exact ConcreteCategory.congr_hom (commRingPresheafFiberIso Φ O).hom_inv_id _

/-! ### Restriction of sections, in a spelling whose codomain is the module itself -/

section Restrict

variable {R : Cᵒᵖ ⥤ RingCat.{w}} {M : PresheafOfModules.{w} R}

omit [LocallySmall.{w} C] in
lemma restrictₛₗ_comp {X Y Z : Cᵒᵖ} (i : X ⟶ Y) (j : Y ⟶ Z) (m : M.obj X) :
    M.restrictₛₗ (i ≫ j) m = M.restrictₛₗ j (M.restrictₛₗ i m) :=
  M.map_comp_apply i j m

omit [LocallySmall.{w} C] in
lemma restrictₛₗ_id {X : Cᵒᵖ} (m : M.obj X) : M.restrictₛₗ (𝟙 X) m = m := by
  simp [PresheafOfModules.restrictₛₗ]

end Restrict

/-! ### The germ API over the `CommRingCat`-valued stalk -/

section GermAPI

variable {M : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})}

/-- The germ map is compatible with the action of scalars. -/
lemma germ_smul (U : C) (x : Φ.fiber.obj U)
    (r : (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op U)) (m : M.obj (op U)) :
    germ Φ O M U x (r • m) = ringGerm Φ O U x r • germ Φ O M U x m := by
  refine (toPresheafModuleFiber_smul Φ M U x r m).trans ?_
  rw [← toRingFiber_germ]
  rfl

/-- The germ maps are compatible with restriction along a morphism of neighbourhoods. -/
lemma germ_w {U V : C} (f : U ⟶ V) (x : Φ.fiber.obj U) (m : M.obj (op V)) :
    germ Φ O M V (Φ.fiber.map f x) m = germ Φ O M U x (M.restrictₛₗ f.op m) :=
  toPresheafModuleFiber_w Φ M f x m

/-- Every element of the stalk is the germ of a section over some neighbourhood. -/
lemma germ_jointly_surjective (m : moduleFiber Φ O M) :
    ∃ (U : C) (x : Φ.fiber.obj U) (s : M.obj (op U)), germ Φ O M U x s = m :=
  toPresheafModuleFiber_jointly_surjective Φ M m

omit [LocallySmall.{w} C] in
/-- The germs of sections of `O` are compatible with restriction. -/
lemma ringGerm_w {U V : C} (f : U ⟶ V) (x : Φ.fiber.obj U) (r : O.obj (op V)) :
    ringGerm Φ O V (Φ.fiber.map f x) r = ringGerm Φ O U x (O.map f.op r) :=
  (Φ.toPresheafFiber_w_apply f x O r).symm

/-- Every element of the stalk of `O` is the germ of a section over some neighbourhood. -/
lemma ringGerm_jointly_surjective (r : ringFiber Φ O) :
    ∃ (U : C) (x : Φ.fiber.obj U) (s : O.obj (op U)), ringGerm Φ O U x s = r :=
  Φ.toPresheafFiber_jointly_surjective (P := O) r

/-- Two germs that agree after restriction to a common neighbourhood are equal. -/
lemma germ_eq_of_restrict {U V W : C} {x : Φ.fiber.obj U} {y : Φ.fiber.obj V}
    (z : Φ.fiber.obj W) (a : W ⟶ U) (b : W ⟶ V)
    (ha : Φ.fiber.map a z = x) (hb : Φ.fiber.map b z = y)
    (s : M.obj (op U)) (t : M.obj (op V))
    (h : M.restrictₛₗ a.op s = M.restrictₛₗ b.op t) :
    germ Φ O M U x s = germ Φ O M V y t := by
  subst ha hb
  rw [germ_w, germ_w, h]

end GermAPI

/-! ### Common refinements of neighbourhoods -/

omit [LocallySmall.{w} C] in
/-- Two neighbourhoods of a point of a site admit a common refinement. -/
lemma exists_common_nbhd {U V : C} (x : Φ.fiber.obj U) (y : Φ.fiber.obj V) :
    ∃ (W : C) (z : Φ.fiber.obj W) (a : W ⟶ U) (b : W ⟶ V),
      Φ.fiber.map a z = x ∧ Φ.fiber.map b z = y :=
  ⟨_, _, (IsCofiltered.minToLeft (Φ.fiber.elementsMk U x) (Φ.fiber.elementsMk V y)).1,
    (IsCofiltered.minToRight (Φ.fiber.elementsMk U x) (Φ.fiber.elementsMk V y)).1,
    (IsCofiltered.minToLeft (Φ.fiber.elementsMk U x) (Φ.fiber.elementsMk V y)).2,
    (IsCofiltered.minToRight (Φ.fiber.elementsMk U x) (Φ.fiber.elementsMk V y)).2⟩

/-- Composing morphisms carries a point of a set-valued functor along. -/
private lemma map_comp_eq_of_map_eq {D : Type*} [Category D] {F : D ⥤ Type*} {U V W : D}
    {z : F.obj W} {y : F.obj V} {x : F.obj U} {d : W ⟶ V} {a : V ⟶ U} (hd : F.map d z = y)
    (ha : F.map a y = x) : F.map (d ≫ a) z = x := by
  rw [Functor.map_comp_apply, hd, ha]

omit [LocallySmall.{w} C] in
/-- Two morphisms of neighbourhoods with the same source and target become equal after passing
to a smaller neighbourhood. -/
lemma exists_eq_nbhd {W U : C} {z : Φ.fiber.obj W} {x : Φ.fiber.obj U}
    (a b : W ⟶ U) (ha : Φ.fiber.map a z = x) (hb : Φ.fiber.map b z = x) :
    ∃ (W' : C) (z' : Φ.fiber.obj W') (c : W' ⟶ W),
      Φ.fiber.map c z' = z ∧ c ≫ a = c ≫ b :=
  ⟨_, _, (IsCofiltered.eqHom (show Φ.fiber.elementsMk W z ⟶ Φ.fiber.elementsMk U x from ⟨a, ha⟩)
      ⟨b, hb⟩).1,
    (IsCofiltered.eqHom (show Φ.fiber.elementsMk W z ⟶ Φ.fiber.elementsMk U x from ⟨a, ha⟩)
      ⟨b, hb⟩).2,
    congrArg CategoryTheory.Functor.Elements.Hom.hom (IsCofiltered.eq_condition
      (show Φ.fiber.elementsMk W z ⟶ Φ.fiber.elementsMk U x from ⟨a, ha⟩) ⟨b, hb⟩)⟩

omit [LocallySmall.{w} C] in
/-- Two parallel pairs of morphisms out of a neighbourhood, each pair compatible with the fibre
element, become simultaneously equal after passing to a smaller neighbourhood. -/
lemma exists_eq_nbhd₂ {W U V : C} {z : Φ.fiber.obj W} {x : Φ.fiber.obj U} {y : Φ.fiber.obj V}
    (a a' : W ⟶ U) (b b' : W ⟶ V)
    (ha : Φ.fiber.map a z = x) (ha' : Φ.fiber.map a' z = x)
    (hb : Φ.fiber.map b z = y) (hb' : Φ.fiber.map b' z = y) :
    ∃ (W' : C) (z' : Φ.fiber.obj W') (c : W' ⟶ W), Φ.fiber.map c z' = z ∧
      c ≫ a = c ≫ a' ∧ c ≫ b = c ≫ b' := by
  obtain ⟨W₁, z₁, c₁, hc₁, h₁⟩ := exists_eq_nbhd a a' ha ha'
  obtain ⟨W₂, z₂, c₂, hc₂, h₂⟩ := exists_eq_nbhd (c₁ ≫ b) (c₁ ≫ b')
    (map_comp_eq_of_map_eq hc₁ hb) (map_comp_eq_of_map_eq hc₁ hb')
  refine ⟨W₂, z₂, c₂ ≫ c₁, map_comp_eq_of_map_eq hc₂ hc₁, ?_, ?_⟩
  · simp only [Category.assoc, h₁]
  · simp only [Category.assoc]; exact h₂

/-- A canonical common refinement of two neighbourhoods of `Φ`. -/
noncomputable def meet {U V : C} (x : Φ.fiber.obj U) (y : Φ.fiber.obj V) : C :=
  (IsCofiltered.min (Φ.fiber.elementsMk U x) (Φ.fiber.elementsMk V y)).1

/-- The point of the fibre over `Stacks.meet`. -/
noncomputable def meetPt {U V : C} (x : Φ.fiber.obj U) (y : Φ.fiber.obj V) :
    Φ.fiber.obj (meet x y) :=
  (IsCofiltered.min (Φ.fiber.elementsMk U x) (Φ.fiber.elementsMk V y)).2

/-- The projection of `Stacks.meet` to the first neighbourhood. -/
noncomputable def meetFst {U V : C} (x : Φ.fiber.obj U) (y : Φ.fiber.obj V) : meet x y ⟶ U :=
  (IsCofiltered.minToLeft (Φ.fiber.elementsMk U x) (Φ.fiber.elementsMk V y)).1

/-- The projection of `Stacks.meet` to the second neighbourhood. -/
noncomputable def meetSnd {U V : C} (x : Φ.fiber.obj U) (y : Φ.fiber.obj V) : meet x y ⟶ V :=
  (IsCofiltered.minToRight (Φ.fiber.elementsMk U x) (Φ.fiber.elementsMk V y)).1

omit [LocallySmall.{w} C] in
@[simp]
lemma fiber_map_meetFst {U V : C} (x : Φ.fiber.obj U) (y : Φ.fiber.obj V) :
    Φ.fiber.map (meetFst x y) (meetPt x y) = x :=
  (IsCofiltered.minToLeft (Φ.fiber.elementsMk U x) (Φ.fiber.elementsMk V y)).2

omit [LocallySmall.{w} C] in
@[simp]
lemma fiber_map_meetSnd {U V : C} (x : Φ.fiber.obj U) (y : Φ.fiber.obj V) :
    Φ.fiber.map (meetSnd x y) (meetPt x y) = y :=
  (IsCofiltered.minToRight (Φ.fiber.elementsMk U x) (Φ.fiber.elementsMk V y)).2

/-! ### Sections of the presheaf tensor product -/

section Tensor

open MonoidalCategory

variable (Φ O) (M N : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}))

/-- The tensor product of the stalks over the stalk ring: the target of the comparison. -/
noncomputable abbrev fiberTensor : Type w :=
  TensorProduct (ringFiber Φ O) (moduleFiber Φ O M) (moduleFiber Φ O N)

/-- The sections of the presheaf tensor product over an object of the site, as a type. -/
noncomputable abbrev tensorSections (U : C) : Type w :=
  TensorProduct ((O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op U))
    (M.obj (op U)) (N.obj (op U))

/-- The restriction map of the presheaf tensor product, as an additive map between the
tensor-product types. Stating it this way puts the additive structures of both sides in the
tensor-product spelling, which is what makes `map_add` and `map_zero` usable below. -/
noncomputable def tensorRestrict {U V : C} (f : U ⟶ V) :
    tensorSections O M N V →+ tensorSections O M N U :=
  ((M ⊗ N).map f.op).hom.toAddMonoidHom

/-- A pure tensor of two sections restricted to a common refinement. -/
noncomputable def resTmul {U V W : C} (a : W ⟶ U) (b : W ⟶ V)
    (m : M.obj (op U)) (n : N.obj (op V)) : tensorSections O M N W :=
  M.restrictₛₗ a.op m ⊗ₜ[(O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op W)]
    N.restrictₛₗ b.op n

/-- The germ map on sections of the presheaf tensor product, with its domain written in the
tensor-product spelling.  This is the same map as `Stacks.germ` at `M ⊗ N`; the point of the
separate spelling is that `map_add` and `map_zero` then fire on the terms produced by
`TensorProduct.induction_on`. -/
noncomputable def tensorGerm (U : C) (x : Φ.fiber.obj U) :
    tensorSections O M N U →+ moduleFiber Φ O (M ⊗ N) :=
  germ Φ O (M ⊗ N) U x

lemma tensorGerm_apply (U : C) (x : Φ.fiber.obj U) (t : tensorSections O M N U) :
    tensorGerm Φ O M N U x t = germ Φ O (M ⊗ N) U x t := rfl

lemma tensorGerm_jointly_surjective (t : moduleFiber Φ O (M ⊗ N)) :
    ∃ (U : C) (x : Φ.fiber.obj U) (s : tensorSections O M N U), tensorGerm Φ O M N U x s = t :=
  germ_jointly_surjective (M := M ⊗ N) t

lemma tensorGerm_smul (U : C) (x : Φ.fiber.obj U)
    (r : (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op U)) (u : tensorSections O M N U) :
    tensorGerm Φ O M N U x (r • u) = ringGerm Φ O U x r • tensorGerm Φ O M N U x u :=
  germ_smul (M := M ⊗ N) U x r u

lemma tensorGerm_w {U V : C} (f : U ⟶ V) (x : Φ.fiber.obj U) (u : tensorSections O M N V) :
    tensorGerm Φ O M N V (Φ.fiber.map f x) u =
      tensorGerm Φ O M N U x (tensorRestrict O M N f u) :=
  germ_w (M := M ⊗ N) f x u

omit [LocallySmall.{w} C] in
@[simp]
lemma tensorRestrict_tmul {U V : C} (f : U ⟶ V) (m : M.obj (op V)) (n : N.obj (op V)) :
    tensorRestrict O M N f (m ⊗ₜ[(O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op V)] n) =
      M.restrictₛₗ f.op m ⊗ₜ[(O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op U)]
        N.restrictₛₗ f.op n :=
  rfl

omit [LocallySmall.{w} C] in
lemma tensorRestrict_resTmul {U V W W' : C} (f : W' ⟶ W) (a : W ⟶ U) (b : W ⟶ V)
    (m : M.obj (op U)) (n : N.obj (op V)) :
    tensorRestrict O M N f (resTmul O M N a b m n) = resTmul O M N (f ≫ a) (f ≫ b) m n := by
  rw [resTmul, tensorRestrict_tmul, resTmul, ← restrictₛₗ_comp, ← restrictₛₗ_comp,
    ← op_comp, ← op_comp]

omit [LocallySmall.{w} C] in
lemma resTmul_restrictₛₗ_right {U V V' W : C} (a : W ⟶ U) (b : W ⟶ V) (f : V ⟶ V')
    (m : M.obj (op U)) (n : N.obj (op V')) :
    resTmul O M N a b m (N.restrictₛₗ f.op n) = resTmul O M N a (b ≫ f) m n := by
  rw [resTmul, resTmul, ← restrictₛₗ_comp, ← op_comp]

omit [LocallySmall.{w} C] in
lemma resTmul_restrictₛₗ_left {U U' V W : C} (a : W ⟶ U) (b : W ⟶ V) (g : U ⟶ U')
    (m : M.obj (op U')) (n : N.obj (op V)) :
    resTmul O M N a b (M.restrictₛₗ g.op m) n = resTmul O M N (a ≫ g) b m n := by
  rw [resTmul, resTmul, ← restrictₛₗ_comp, ← op_comp]

/-! ### The forward comparison map -/

/-- The additive, `O(U)`-balanced map `m ⊗ n ↦ (germ m) ⊗ (germ n)` on the sections of the
presheaf tensor product over a neighbourhood of `Φ`. -/
noncomputable def fwdLeg (U : C) (x : Φ.fiber.obj U) :
    tensorSections O M N U →+ fiberTensor Φ O M N :=
  TensorProduct.liftAddHom
    (R := (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op U))
    { toFun := fun m =>
        { toFun := fun n => germ Φ O M U x m ⊗ₜ[ringFiber Φ O] germ Φ O N U x n
          map_zero' := by simp
          map_add' := fun n₁ n₂ => by simp [TensorProduct.tmul_add] }
      map_zero' := by ext n; simp
      map_add' := fun m₁ m₂ => by ext n; simp [TensorProduct.add_tmul] }
    (fun r m n => by
      dsimp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [germ_smul, germ_smul, TensorProduct.smul_tmul])

@[simp]
lemma fwdLeg_tmul (U : C) (x : Φ.fiber.obj U) (m : M.obj (op U)) (n : N.obj (op U)) :
    fwdLeg Φ O M N U x (m ⊗ₜ[(O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op U)] n) =
      germ Φ O M U x m ⊗ₜ[ringFiber Φ O] germ Φ O N U x n :=
  rfl

lemma fwdLeg_resTmul {U V W : C} (z : Φ.fiber.obj W) (a : W ⟶ U) (b : W ⟶ V)
    (m : M.obj (op U)) (n : N.obj (op V)) :
    fwdLeg Φ O M N W z (resTmul O M N a b m n) =
      germ Φ O M U (Φ.fiber.map a z) m ⊗ₜ[ringFiber Φ O] germ Φ O N V (Φ.fiber.map b z) n := by
  rw [resTmul, fwdLeg_tmul, germ_w, germ_w]

/-- `fwdLeg` is compatible with restriction along a morphism of neighbourhoods. -/
lemma fwdLeg_naturality {U V : C} (f : U ⟶ V) (x : Φ.fiber.obj U)
    (t : tensorSections O M N V) :
    fwdLeg Φ O M N U x (tensorRestrict O M N f t) = fwdLeg Φ O M N V (Φ.fiber.map f x) t := by
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul m n =>
      rw [tensorRestrict_tmul, fwdLeg_tmul, fwdLeg_tmul, germ_w, germ_w]

/-- The family of legs of the forward comparison map. -/
noncomputable def fwdLegApp (U : C) (x : Φ.fiber.obj U) :
    (M ⊗ N).presheaf.obj (op U) ⟶ AddCommGrpCat.of (fiberTensor Φ O M N) :=
  AddCommGrpCat.ofHom (fwdLeg Φ O M N U x)

lemma fwdLegApp_w ⦃U V : C⦄ (f : U ⟶ V) (x : Φ.fiber.obj U) :
    (M ⊗ N).presheaf.map f.op ≫ fwdLegApp Φ O M N U x =
      fwdLegApp Φ O M N V (Φ.fiber.map f x) :=
  AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun t => fwdLeg_naturality Φ O M N f x t

/-- The forward comparison map: the stalk of the presheaf tensor product maps to the tensor
product of the stalks, by `germ (m ⊗ n) ↦ (germ m) ⊗ (germ n)`. -/
noncomputable def fwdHom : moduleFiber Φ O (M ⊗ N) →+ fiberTensor Φ O M N :=
  (Φ.presheafFiberDesc (fwdLegApp Φ O M N) (fwdLegApp_w Φ O M N)).hom

lemma fwdHom_germ (U : C) (x : Φ.fiber.obj U) (t : tensorSections O M N U) :
    fwdHom Φ O M N (tensorGerm Φ O M N U x t) = fwdLeg Φ O M N U x t :=
  ConcreteCategory.congr_hom
    (Φ.toPresheafFiber_presheafFiberDesc (fwdLegApp Φ O M N) (fwdLegApp_w Φ O M N) U x) t

/-! ### Germ equalities for pure tensors -/

/-- The germ of a pure tensor of restricted sections does not depend on the chosen common
refinement, nor on the chosen morphisms to the two neighbourhoods. -/
lemma germ_resTmul_eq {U V W₁ W₂ : C} {x : Φ.fiber.obj U} {y : Φ.fiber.obj V}
    (z₁ : Φ.fiber.obj W₁) (z₂ : Φ.fiber.obj W₂)
    (a₁ : W₁ ⟶ U) (b₁ : W₁ ⟶ V) (a₂ : W₂ ⟶ U) (b₂ : W₂ ⟶ V)
    (ha₁ : Φ.fiber.map a₁ z₁ = x) (hb₁ : Φ.fiber.map b₁ z₁ = y)
    (ha₂ : Φ.fiber.map a₂ z₂ = x) (hb₂ : Φ.fiber.map b₂ z₂ = y)
    (m : M.obj (op U)) (n : N.obj (op V)) :
    tensorGerm Φ O M N W₁ z₁ (resTmul O M N a₁ b₁ m n) =
      tensorGerm Φ O M N W₂ z₂ (resTmul O M N a₂ b₂ m n) := by
  obtain ⟨W, z, d₁, d₂, hd₁, hd₂⟩ := exists_common_nbhd z₁ z₂
  obtain ⟨W', z', c, hc, hA, hB⟩ := exists_eq_nbhd₂ (d₁ ≫ a₁) (d₂ ≫ a₂) (d₁ ≫ b₁) (d₂ ≫ b₂)
    (map_comp_eq_of_map_eq hd₁ ha₁) (map_comp_eq_of_map_eq hd₂ ha₂)
    (map_comp_eq_of_map_eq hd₁ hb₁) (map_comp_eq_of_map_eq hd₂ hb₂)
  rw [tensorGerm_apply, tensorGerm_apply]
  refine germ_eq_of_restrict z' (c ≫ d₁) (c ≫ d₂) (map_comp_eq_of_map_eq hc hd₁)
    (map_comp_eq_of_map_eq hc hd₂) _ _ ?_
  · change tensorRestrict O M N (c ≫ d₁) _ = tensorRestrict O M N (c ≫ d₂) _
    rw [tensorRestrict_resTmul, tensorRestrict_resTmul, Category.assoc, Category.assoc,
      Category.assoc, Category.assoc, hA, hB]

/-- The germ of a pure tensor of sections restricted from one and the same neighbourhood is the
germ of the pure tensor there. -/
lemma germ_resTmul_eq_self {U W : C} {x : Φ.fiber.obj U} (z : Φ.fiber.obj W) (a b : W ⟶ U)
    (ha : Φ.fiber.map a z = x) (hb : Φ.fiber.map b z = x)
    (m : M.obj (op U)) (n : N.obj (op U)) :
    tensorGerm Φ O M N W z (resTmul O M N a b m n) =
      tensorGerm Φ O M N U x
        (m ⊗ₜ[(O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op U)] n) := by
  obtain ⟨W', z', c, hc, h⟩ := exists_eq_nbhd a b ha hb
  rw [tensorGerm_apply, tensorGerm_apply]
  refine germ_eq_of_restrict z' c (c ≫ a) hc (map_comp_eq_of_map_eq hc ha) _ _ ?_
  · change tensorRestrict O M N c _ = tensorRestrict O M N (c ≫ a) _
    rw [tensorRestrict_resTmul, tensorRestrict_tmul, h, resTmul]

/-! ### The backward comparison map -/

/-- For a section `m` of `M` over a neighbourhood `(U, x)`, the additive map on the sections of
`N` over a neighbourhood `(V, y)` given by the germ of the pure tensor over the canonical common
refinement of the two neighbourhoods. -/
noncomputable def bwdInnerLeg {U : C} (x : Φ.fiber.obj U) (m : M.obj (op U))
    (V : C) (y : Φ.fiber.obj V) : N.obj (op V) →+ moduleFiber Φ O (M ⊗ N) where
  toFun n :=
    tensorGerm Φ O M N (meet x y) (meetPt x y) (resTmul O M N (meetFst x y) (meetSnd x y) m n)
  map_zero' := by simp [resTmul]
  map_add' n₁ n₂ := by simp [resTmul, TensorProduct.tmul_add]

@[simp]
lemma bwdInnerLeg_apply {U : C} (x : Φ.fiber.obj U) (m : M.obj (op U))
    (V : C) (y : Φ.fiber.obj V) (n : N.obj (op V)) :
    bwdInnerLeg Φ O M N x m V y n =
      tensorGerm Φ O M N (meet x y) (meetPt x y)
        (resTmul O M N (meetFst x y) (meetSnd x y) m n) :=
  rfl

/-- The legs `Stacks.bwdInnerLeg`, as morphisms of abelian groups. -/
noncomputable def bwdInnerLegApp {U : C} (x : Φ.fiber.obj U) (m : M.obj (op U))
    (V : C) (y : Φ.fiber.obj V) :
    N.presheaf.obj (op V) ⟶ AddCommGrpCat.of (moduleFiber Φ O (M ⊗ N)) :=
  AddCommGrpCat.ofHom (bwdInnerLeg Φ O M N x m V y)

lemma bwdInnerLeg_w {U : C} (x : Φ.fiber.obj U) (m : M.obj (op U))
    {V V' : C} (f : V ⟶ V') (y : Φ.fiber.obj V) (n : N.obj (op V')) :
    bwdInnerLeg Φ O M N x m V y (N.restrictₛₗ f.op n) =
      bwdInnerLeg Φ O M N x m V' (Φ.fiber.map f y) n := by
  rw [bwdInnerLeg_apply, bwdInnerLeg_apply, resTmul_restrictₛₗ_right]
  exact germ_resTmul_eq Φ O M N _ _ _ _ _ _ (fiber_map_meetFst x y)
    (map_comp_eq_of_map_eq (fiber_map_meetSnd x y) rfl)
    (fiber_map_meetFst x (Φ.fiber.map f y)) (fiber_map_meetSnd x (Φ.fiber.map f y)) m n

lemma bwdInnerLegApp_w {U : C} (x : Φ.fiber.obj U) (m : M.obj (op U))
    ⦃V V' : C⦄ (f : V ⟶ V') (y : Φ.fiber.obj V) :
    N.presheaf.map f.op ≫ bwdInnerLegApp Φ O M N x m V y =
      bwdInnerLegApp Φ O M N x m V' (Φ.fiber.map f y) :=
  AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun n => bwdInnerLeg_w Φ O M N x m f y n

/-- For a section `m` of `M` over a neighbourhood of `Φ`, the induced additive map from the
stalk of `N` to the stalk of the presheaf tensor product. -/
noncomputable def bwdInnerHom {U : C} (x : Φ.fiber.obj U) (m : M.obj (op U)) :
    moduleFiber Φ O N →+ moduleFiber Φ O (M ⊗ N) :=
  (Φ.presheafFiberDesc (bwdInnerLegApp Φ O M N x m) (bwdInnerLegApp_w Φ O M N x m)).hom

lemma bwdInnerHom_germ {U : C} (x : Φ.fiber.obj U) (m : M.obj (op U))
    (V : C) (y : Φ.fiber.obj V) (n : N.obj (op V)) :
    bwdInnerHom Φ O M N x m (germ Φ O N V y n) =
      tensorGerm Φ O M N (meet x y) (meetPt x y)
        (resTmul O M N (meetFst x y) (meetSnd x y) m n) :=
  ConcreteCategory.congr_hom (Φ.toPresheafFiber_presheafFiberDesc
    (bwdInnerLegApp Φ O M N x m) (bwdInnerLegApp_w Φ O M N x m) V y) n

/-- The outer legs of the backward comparison map: `m ↦ Stacks.bwdInnerHom m`. -/
noncomputable def bwdOuterLeg (U : C) (x : Φ.fiber.obj U) :
    M.obj (op U) →+ (moduleFiber Φ O N →+ moduleFiber Φ O (M ⊗ N)) where
  toFun m := bwdInnerHom Φ O M N x m
  map_zero' := by
    refine AddMonoidHom.ext fun q => ?_
    obtain ⟨V, y, n, rfl⟩ := germ_jointly_surjective (M := N) q
    rw [AddMonoidHom.zero_apply, bwdInnerHom_germ]
    simp [resTmul]
  map_add' m₁ m₂ := by
    refine AddMonoidHom.ext fun q => ?_
    obtain ⟨V, y, n, rfl⟩ := germ_jointly_surjective (M := N) q
    rw [AddMonoidHom.add_apply, bwdInnerHom_germ, bwdInnerHom_germ, bwdInnerHom_germ]
    simp [resTmul, TensorProduct.add_tmul]

/-- The outer legs, as morphisms of abelian groups. -/
noncomputable def bwdOuterLegApp (U : C) (x : Φ.fiber.obj U) :
    M.presheaf.obj (op U) ⟶
      AddCommGrpCat.of (moduleFiber Φ O N →+ moduleFiber Φ O (M ⊗ N)) :=
  AddCommGrpCat.ofHom (bwdOuterLeg Φ O M N U x)

lemma bwdOuterLeg_w {U U' : C} (g : U ⟶ U') (x : Φ.fiber.obj U) (m : M.obj (op U')) :
    bwdOuterLeg Φ O M N U x (M.restrictₛₗ g.op m) =
      bwdOuterLeg Φ O M N U' (Φ.fiber.map g x) m := by
  refine AddMonoidHom.ext fun q => ?_
  obtain ⟨V, y, n, rfl⟩ := germ_jointly_surjective (M := N) q
  change bwdInnerHom Φ O M N x (M.restrictₛₗ g.op m) _ =
    bwdInnerHom Φ O M N (Φ.fiber.map g x) m _
  rw [bwdInnerHom_germ, bwdInnerHom_germ, resTmul_restrictₛₗ_left]
  refine germ_resTmul_eq Φ O M N _ _ _ _ _ _ ?_ (fiber_map_meetSnd x y)
    (fiber_map_meetFst (Φ.fiber.map g x) y) (fiber_map_meetSnd (Φ.fiber.map g x) y) m n
  rw [Functor.map_comp_apply, fiber_map_meetFst]

lemma bwdOuterLegApp_w ⦃U U' : C⦄ (g : U ⟶ U') (x : Φ.fiber.obj U) :
    M.presheaf.map g.op ≫ bwdOuterLegApp Φ O M N U x =
      bwdOuterLegApp Φ O M N U' (Φ.fiber.map g x) :=
  AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun m => bwdOuterLeg_w Φ O M N g x m

/-- The biadditive map underlying the backward comparison. -/
noncomputable def bwdBiAdd :
    moduleFiber Φ O M →+ (moduleFiber Φ O N →+ moduleFiber Φ O (M ⊗ N)) :=
  (Φ.presheafFiberDesc (bwdOuterLegApp Φ O M N) (bwdOuterLegApp_w Φ O M N)).hom

lemma bwdBiAdd_germ (U : C) (x : Φ.fiber.obj U) (m : M.obj (op U)) :
    bwdBiAdd Φ O M N (germ Φ O M U x m) = bwdInnerHom Φ O M N x m :=
  ConcreteCategory.congr_hom (Φ.toPresheafFiber_presheafFiberDesc
    (bwdOuterLegApp Φ O M N) (bwdOuterLegApp_w Φ O M N) U x) m

lemma bwdBiAdd_germ_germ {U V : C} (x : Φ.fiber.obj U) (y : Φ.fiber.obj V)
    (m : M.obj (op U)) (n : N.obj (op V)) :
    bwdBiAdd Φ O M N (germ Φ O M U x m) (germ Φ O N V y n) =
      tensorGerm Φ O M N (meet x y) (meetPt x y)
        (resTmul O M N (meetFst x y) (meetSnd x y) m n) := by
  rw [bwdBiAdd_germ, bwdInnerHom_germ]

/-- On germs over one neighbourhood, `bwdBiAdd` is the germ of the pure tensor there. -/
private lemma bwdBiAdd_germ_germ_self (U : C) (x : Φ.fiber.obj U) (m : M.obj (op U))
    (n : N.obj (op U)) :
    bwdBiAdd Φ O M N (germ Φ O M U x m) (germ Φ O N U x n) =
      tensorGerm Φ O M N U x
        (m ⊗ₜ[(O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op U)] n) := by
  rw [bwdBiAdd_germ_germ,
    germ_resTmul_eq_self Φ O M N _ _ _ (fiber_map_meetFst x x) (fiber_map_meetSnd x x)]

/-- A germ of `O` and germs of `M` and of `N` can be represented over one and the same
neighbourhood of `Φ`. -/
lemma exists_common_germ₃ (r : ringFiber Φ O) (p : moduleFiber Φ O M)
    (q : moduleFiber Φ O N) :
    ∃ (W : C) (z : Φ.fiber.obj W)
      (s : (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op W))
      (m : M.obj (op W)) (n : N.obj (op W)),
      ringGerm Φ O W z s = r ∧ germ Φ O M W z m = p ∧ germ Φ O N W z n = q := by
  obtain ⟨U₁, x₁, s, hs⟩ := ringGerm_jointly_surjective r
  obtain ⟨U₂, x₂, m, hm⟩ := germ_jointly_surjective (M := M) p
  obtain ⟨U₃, x₃, n, hn⟩ := germ_jointly_surjective (M := N) q
  obtain ⟨V, y, a, b, ha, hb⟩ := exists_common_nbhd x₁ x₂
  obtain ⟨W, z, c, d, hc, hd⟩ := exists_common_nbhd y x₃
  refine ⟨W, z, O.map (c ≫ a).op s, M.restrictₛₗ (c ≫ b).op m, N.restrictₛₗ d.op n, ?_, ?_, ?_⟩
  · rw [← ringGerm_w, Functor.map_comp_apply, hc, ha, hs]
  · rw [← germ_w, Functor.map_comp_apply, hc, hb, hm]
  · rw [← germ_w, hd, hn]

/-- The balance condition over the stalk ring: this is what makes the backward comparison map
well defined, and it is the only place where the varying base ring is dealt with. -/
lemma bwdBiAdd_balance (r : ringFiber Φ O) (p : moduleFiber Φ O M) (q : moduleFiber Φ O N) :
    bwdBiAdd Φ O M N (r • p) q = bwdBiAdd Φ O M N p (r • q) := by
  obtain ⟨W, z, s, m, n, rfl, rfl, rfl⟩ := exists_common_germ₃ Φ O M N r p q
  rw [← germ_smul, ← germ_smul, bwdBiAdd_germ_germ_self, bwdBiAdd_germ_germ_self]
  exact congrArg _ (TensorProduct.smul_tmul s m n)

/-- The backward comparison map, `(germ m) ⊗ (germ n) ↦ germ (m ⊗ n)`. -/
noncomputable def bwdHom : fiberTensor Φ O M N →+ moduleFiber Φ O (M ⊗ N) :=
  TensorProduct.liftAddHom (bwdBiAdd Φ O M N) (bwdBiAdd_balance Φ O M N)

lemma bwdHom_tmul (p : moduleFiber Φ O M) (q : moduleFiber Φ O N) :
    bwdHom Φ O M N (p ⊗ₜ[ringFiber Φ O] q) = bwdBiAdd Φ O M N p q := rfl

lemma bwdHom_germ_tmul (U : C) (x : Φ.fiber.obj U) (m : M.obj (op U)) (n : N.obj (op U)) :
    bwdHom Φ O M N (germ Φ O M U x m ⊗ₜ[ringFiber Φ O] germ Φ O N U x n) =
      tensorGerm Φ O M N U x
        (m ⊗ₜ[(O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op U)] n) := by
  rw [bwdHom_tmul, bwdBiAdd_germ_germ_self]

/-! ### The two maps are mutually inverse, and the forward map is linear -/

lemma bwdHom_fwdHom (t : moduleFiber Φ O (M ⊗ N)) :
    bwdHom Φ O M N (fwdHom Φ O M N t) = t := by
  obtain ⟨U, x, u, rfl⟩ := tensorGerm_jointly_surjective Φ O M N t
  rw [fwdHom_germ]
  induction u using TensorProduct.inductionOn with
  | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | tmul m n => rw [fwdLeg_tmul, bwdHom_germ_tmul]

lemma fwdHom_bwdHom (t : fiberTensor Φ O M N) :
    fwdHom Φ O M N (bwdHom Φ O M N t) = t := by
  induction t using TensorProduct.inductionOn with
  | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | tmul p q =>
      obtain ⟨U₁, x₁, m, rfl⟩ := germ_jointly_surjective (M := M) p
      obtain ⟨U₂, x₂, n, rfl⟩ := germ_jointly_surjective (M := N) q
      obtain ⟨W, z, a, b, ha, hb⟩ := exists_common_nbhd x₁ x₂
      subst ha
      subst hb
      rw [germ_w, germ_w, bwdHom_germ_tmul, fwdHom_germ, fwdLeg_tmul]

/-- A germ of `O` and a germ of the presheaf tensor product can be represented over one and
the same neighbourhood of `Φ`. -/
lemma exists_common_germ_tensor (r : ringFiber Φ O) (t : moduleFiber Φ O (M ⊗ N)) :
    ∃ (W : C) (z : Φ.fiber.obj W) (s : O.obj (op W)) (u : tensorSections O M N W),
      ringGerm Φ O W z s = r ∧ tensorGerm Φ O M N W z u = t := by
  obtain ⟨U₁, x₁, s, hs⟩ := ringGerm_jointly_surjective r
  obtain ⟨U₂, x₂, u, hu⟩ := tensorGerm_jointly_surjective Φ O M N t
  obtain ⟨W, z, a, b, ha, hb⟩ := exists_common_nbhd x₁ x₂
  refine ⟨W, z, O.map a.op s, tensorRestrict O M N b u, ?_, ?_⟩
  · rw [← ringGerm_w, ha, hs]
  · rw [← tensorGerm_w, hb, hu]

/-- The forward comparison map is linear over the stalk of `O`. -/
lemma fwdHom_smul (r : ringFiber Φ O) (t : moduleFiber Φ O (M ⊗ N)) :
    fwdHom Φ O M N (r • t) = r • fwdHom Φ O M N t := by
  obtain ⟨W, z, s, u, rfl, rfl⟩ := exists_common_germ_tensor Φ O M N r t
  rw [← tensorGerm_smul, fwdHom_germ, fwdHom_germ]
  induction u using TensorProduct.inductionOn with
  | add t₁ t₂ h₁ h₂ => rw [smul_add, map_add, map_add, h₁, h₂, smul_add]
  | tmul m n =>
      rw [TensorProduct.smul_tmul', fwdLeg_tmul, fwdLeg_tmul, germ_smul,
        TensorProduct.smul_tmul']

/-! ### The comparison isomorphism -/

/-- **The stalk of a tensor product of presheaves of modules at a point of a site is the tensor
product of the stalks over the stalk of the ring of the site.** The comparison map is the
canonical one: the germ of a pure tensor of sections goes to the tensor of the germs, see
`Stacks.presheafModuleFiberTensorEquiv_germ_tmul`. -/
@[sga "4 IV 13.5" "Presheaf-level case"]
noncomputable def presheafModuleFiberTensorEquiv :
    moduleFiber Φ O (M ⊗ N) ≃ₗ[ringFiber Φ O] fiberTensor Φ O M N where
  toFun := fwdHom Φ O M N
  map_add' := (fwdHom Φ O M N).map_add
  map_smul' := fwdHom_smul Φ O M N
  invFun := bwdHom Φ O M N
  left_inv := bwdHom_fwdHom Φ O M N
  right_inv := fwdHom_bwdHom Φ O M N

@[simp]
lemma presheafModuleFiberTensorEquiv_germ_tmul (U : C) (x : Φ.fiber.obj U)
    (m : M.obj (op U)) (n : N.obj (op U)) :
    presheafModuleFiberTensorEquiv Φ O M N
        (tensorGerm Φ O M N U x
          (m ⊗ₜ[(O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op U)] n)) =
      germ Φ O M U x m ⊗ₜ[ringFiber Φ O] germ Φ O N U x n := by
  change fwdHom Φ O M N _ = _
  rw [fwdHom_germ, fwdLeg_tmul]

@[simp]
lemma presheafModuleFiberTensorEquiv_symm_germ_tmul (U : C) (x : Φ.fiber.obj U)
    (m : M.obj (op U)) (n : N.obj (op U)) :
    (presheafModuleFiberTensorEquiv Φ O M N).symm
        (germ Φ O M U x m ⊗ₜ[ringFiber Φ O] germ Φ O N U x n) =
      tensorGerm Φ O M N U x
        (m ⊗ₜ[(O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op U)] n) := by
  rw [LinearEquiv.symm_apply_eq, presheafModuleFiberTensorEquiv_germ_tmul]

/-! ### Naturality -/

lemma germ_naturality {M' : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})}
    (h : M ⟶ M') (U : C) (x : Φ.fiber.obj U) (m : M.obj (op U)) :
    (presheafModuleFiberOfCommRing Φ O).map h (germ Φ O M U x m) =
      germ Φ O M' U x (h.app (op U) m) :=
  toPresheafModuleFiber_naturality Φ h U x m

variable {M N}

/-- The map induced on sections of the presheaf tensor product by a pair of morphisms, in the
tensor-product spelling. -/
noncomputable def tensorSectionsMap
    {M' N' : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})}
    (φ : M ⟶ M') (ψ : N ⟶ N') (U : C) :
    tensorSections O M N U →+ tensorSections O M' N' U :=
  ((φ ⊗ₘ ψ).app (op U)).hom.toAddMonoidHom

omit [LocallySmall.{w} C] in
@[simp]
lemma tensorSectionsMap_tmul
    {M' N' : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})}
    (φ : M ⟶ M') (ψ : N ⟶ N') (U : C) (m : M.obj (op U)) (n : N.obj (op U)) :
    tensorSectionsMap O φ ψ U (m ⊗ₜ[(O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op U)] n) =
      φ.app (op U) m ⊗ₜ[(O ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj (op U)]
        ψ.app (op U) n :=
  rfl

lemma tensorGerm_naturality
    {M' N' : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})}
    (φ : M ⟶ M') (ψ : N ⟶ N') (U : C) (x : Φ.fiber.obj U) (u : tensorSections O M N U) :
    (presheafModuleFiberOfCommRing Φ O).map (φ ⊗ₘ ψ) (tensorGerm Φ O M N U x u) =
      tensorGerm Φ O M' N' U x (tensorSectionsMap O φ ψ U u) :=
  germ_naturality Φ O (M ⊗ N) (φ ⊗ₘ ψ) U x u

variable (M N)

/-- **The comparison is natural in both variables.** -/
lemma fwdHom_naturality
    {M' N' : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})}
    (φ : M ⟶ M') (ψ : N ⟶ N') (t : moduleFiber Φ O (M ⊗ N)) :
    fwdHom Φ O M' N' ((presheafModuleFiberOfCommRing Φ O).map (φ ⊗ₘ ψ) t) =
      ((presheafModuleFiberOfCommRing Φ O).map φ ⊗ₘ
          (presheafModuleFiberOfCommRing Φ O).map ψ) (fwdHom Φ O M N t) := by
  obtain ⟨U, x, u, rfl⟩ := tensorGerm_jointly_surjective Φ O M N t
  rw [tensorGerm_naturality]
  induction u using TensorProduct.inductionOn with
  | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul m n =>
      rw [tensorSectionsMap_tmul, fwdHom_germ, fwdHom_germ, fwdLeg_tmul, fwdLeg_tmul,
        ModuleCat.MonoidalCategory.tensorHom_tmul, germ_naturality, germ_naturality]

/-- The comparison isomorphism, as an isomorphism of modules over the stalk of `O`, in the
shape in which `CategoryTheory.MonoidalCategory.curriedTensor` presents the tensor product. -/
noncomputable def moduleFiberTensorIso :
    moduleFiber Φ O (M ⊗ N) ≅
      ((curriedTensor (ModuleCat.{w} (ringFiber Φ O))).obj (moduleFiber Φ O M)).obj
        (moduleFiber Φ O N) :=
  (presheafModuleFiberTensorEquiv Φ O M N).toModuleIso

lemma moduleFiberTensorIso_hom_apply (t : moduleFiber Φ O (M ⊗ N)) :
    (moduleFiberTensorIso Φ O M N).hom t = fwdHom Φ O M N t := rfl

/-- Naturality of the comparison in the left-hand variable, in the shape
`CategoryTheory.Functor.mapBifunctorTotalIso` consumes. -/
lemma moduleFiberTensorIso_naturality_left
    {M' : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})} (φ : M ⟶ M') :
    (presheafModuleFiberOfCommRing Φ O).map (((curriedTensor
          (PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}))).map φ).app N) ≫
        (moduleFiberTensorIso Φ O M' N).hom =
      (moduleFiberTensorIso Φ O M N).hom ≫
        ((curriedTensor (ModuleCat.{w} (ringFiber Φ O))).map
          ((presheafModuleFiberOfCommRing Φ O).map φ)).app (moduleFiber Φ O N) := by
  ext t
  have h := fwdHom_naturality Φ O M N φ (𝟙 N) t
  rw [CategoryTheory.Functor.map_id, MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_id] at h
  exact h

/-- Naturality of the comparison in the right-hand variable, in the shape
`CategoryTheory.Functor.mapBifunctorTotalIso` consumes. -/
lemma moduleFiberTensorIso_naturality_right
    {N' : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})} (ψ : N ⟶ N') :
    (presheafModuleFiberOfCommRing Φ O).map (((curriedTensor
          (PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}))).obj M).map ψ) ≫
        (moduleFiberTensorIso Φ O M N').hom =
      (moduleFiberTensorIso Φ O M N).hom ≫
        ((curriedTensor (ModuleCat.{w} (ringFiber Φ O))).obj
          (moduleFiber Φ O M)).map ((presheafModuleFiberOfCommRing Φ O).map ψ) := by
  ext t
  have h := fwdHom_naturality Φ O M N (𝟙 M) ψ t
  rw [CategoryTheory.Functor.map_id, MonoidalCategory.id_tensorHom,
    MonoidalCategory.id_tensorHom] at h
  exact h

end Tensor

end Stacks

end
