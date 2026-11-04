module

import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv

public import StacksFrontier.CategoryTheory.FiberedInSets.TwoCategory
public import StacksFrontier.CategoryTheory.Sites.Stack.MorSeparated
public import StacksFrontier.CategoryTheory.Sites.Stack.Setoid

/-!
# A category fibred in sets is a stack exactly when its presheaf of objects is a sheaf

Let `(𝒞, J)` be a site. Under the equivalence between presheaves of sets on `𝒞` and categories
fibred in sets over `𝒞` (Categories, Stacks 02Y2) — which sends `p : 𝒮 ⥤ 𝒞` to the presheaf
`U ↦ Ob(𝒮_U)` — the stacks in sets correspond precisely to the sheaves: for a category fibred in
sets `p`, `p.IsStackInSets J` holds if and only if the presheaf of objects
`CategoryTheory.Functor.objPresheaf p` is a sheaf.

## Main definitions

* `CategoryTheory.Functor.objPresheaf`, the presheaf `U ↦ Ob(𝒮_U)` of a category fibred in sets.

## Main results

* `CategoryTheory.Functor.isMorSheaf_of_isSheaf_objPresheaf` and
  `CategoryTheory.Functor.isSeparatedFor_objPresheaf_of_isMorSheaf`: condition (2) of Stacks 026F
  is separatedness of the presheaf of objects.
* `CategoryTheory.Functor.hasEffectiveDescent_of_isSheaf_objPresheaf`: condition (3) of
  Stacks 026F follows from the sheaf condition on the presheaf of objects.
* `CategoryTheory.Functor.isStackInSets_iff_isSheaf_objPresheaf`: a category fibred in sets is a
  stack in sets if and only if its presheaf of objects is a sheaf.
-/

@[expose] public section

-- The chosen pullbacks of `CategoryTheory.Functor.IsPreFibered` and the inclusion of a fibre are
-- semireducible, so the endpoints of the composites below agree only up to unfolding them.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

open Opposite

universe v₁ v₂ u₁ u₂

namespace Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- A category fibred in sets is a fibred category. -/
local instance isFibered_of_isFiberedInSets (p : 𝒮 ⥤ 𝒞) [p.IsFiberedInSets] : p.IsFibered :=
  (IsFiberedInSets.isFiberedInGroupoids p).isFibered

namespace IsFiberedInSets

/-- In a category fibred in sets two morphisms with the same domain and codomain lying over one and
the same morphism of the base are equal. -/
lemma hom_ext_of_isHomLift (p : 𝒮 ⥤ 𝒞) [p.IsFiberedInSets] {V U : 𝒞} (f : V ⟶ U) {x y : 𝒮}
    (φ₁ φ₂ : y ⟶ x) [p.IsHomLift f φ₁] [p.IsHomLift f φ₂] : φ₁ = φ₂ := by
  obtain ⟨h, hc⟩ := IsFiberedInSets.eq_of_isHomLift p f φ₁ φ₂
  simpa using hc

end IsFiberedInSets

/-! ### The presheaf of objects

The fibres of a category fibred in sets are discrete, so the canonical comparisons between its
iterated chosen pullbacks are equalities and `U ↦ Ob(𝒮_U)` is a presheaf. -/

section ObjPresheaf

variable (p : 𝒮 ⥤ 𝒞) [p.IsFiberedInSets]

/-- The presheaf of objects `U ↦ Ob(𝒮_U)` of a category fibred in sets, the image of `p` under the
equivalence of Stacks 02Y2 between categories fibred in sets and presheaves of sets. Its
restriction maps are the chosen pullbacks. -/
@[implicit_reducible]
noncomputable def objPresheaf : 𝒞ᵒᵖ ⥤ Type u₂ where
  obj U := p.Fiber U.unop
  map f := ↾fun x ↦ pullbackFiber p x f.unop
  map_id U := by
    ext x
    exact obj_ext_of_isDiscrete (pullbackFiberIdIso x).hom
  map_comp f g := by
    ext x
    exact (obj_ext_of_isDiscrete (pullbackFiberCompIso x f.unop g.unop).hom).symm

/-- The value of `CategoryTheory.Functor.objPresheaf` at `U` is the fibre of `p` over `U`. -/
@[simp]
lemma objPresheaf_obj (U : 𝒞ᵒᵖ) : (objPresheaf p).obj U = p.Fiber U.unop := rfl

/-- The restriction map of `CategoryTheory.Functor.objPresheaf` along `f : V ⟶ U` is the chosen
pullback of objects of the fibre along `f`. -/
@[simp]
lemma objPresheaf_map {U V : 𝒞} (f : V ⟶ U) (x : p.Fiber U) :
    (objPresheaf p).map f.op x = pullbackFiber p x f := rfl

/-- `CategoryTheory.Functor.objPresheaf_map` for a morphism of `𝒞ᵒᵖ` presented as such. -/
@[simp]
lemma objPresheaf_map' {U V : 𝒞ᵒᵖ} (f : U ⟶ V) (x : p.Fiber U.unop) :
    (objPresheaf p).map f x = pullbackFiber p x f.unop := rfl

end ObjPresheaf

/-! ### Condition (2) of Stacks 026F is separatedness of the presheaf of objects

A section of `Mor(x, y)` over `f : V ⟶ U` is a morphism `f^* x ⟶ f^* y` of the fibre over `V`,
which is discrete: such a morphism exists exactly when `f^* x = f^* y`, and then it is unique. So
`Mor(x, y)` is the subterminal presheaf on `𝒞/U` cut out by that equality, and its sheaf condition
is separatedness of `objPresheaf`. -/

section MorSheaf

variable {p : 𝒮 ⥤ 𝒞} [p.IsFiberedInSets]

/-- A section of `Mor(x, y)` over `g : V ⟶ U` is a witness that the chosen pullbacks of `x` and `y`
along `g` are equal, the fibre over `V` being discrete. -/
lemma nonempty_morPresheaf_obj_iff {U : 𝒞} (x y : p.Fiber U) (g : Over U) :
    Nonempty ((morPresheaf p x y).obj (op g)) ↔
      pullbackFiber p x g.hom = pullbackFiber p y g.hom := by
  rw [morPresheaf_obj]
  exact ⟨fun ⟨m⟩ ↦ obj_ext_of_isDiscrete m, fun h ↦ ⟨eqToHom h⟩⟩

/-- The sections of `Mor(x, y)` form a subsingleton, the fibres being discrete. -/
instance subsingleton_morPresheaf_obj {U : 𝒞} (x y : p.Fiber U) (g : (Over U)ᵒᵖ) :
    Subsingleton ((morPresheaf p x y).obj g) :=
  IsDiscrete.subsingleton _ _

/-- When `objPresheaf p` is a sheaf, objects of the fibre over `X.left` that agree after
restriction along the members of a covering sieve of `X : 𝒞/U` agree. -/
lemma pullbackFiber_eq_of_locally_eq {J : GrothendieckTopology 𝒞}
    (hJ : Presieve.IsSheaf J (objPresheaf p)) {U : 𝒞} {x y : p.Fiber U} {X : Over U} (S : Sieve X)
    (hS : S ∈ (J.over U) X)
    (h : ∀ ⦃Z : Over U⦄ ⦃k : Z ⟶ X⦄, S k → pullbackFiber p x Z.hom = pullbackFiber p y Z.hom) :
    pullbackFiber p x X.hom = pullbackFiber p y X.hom := by
  refine (hJ _ ((J.mem_over_iff S).1 hS)).isSeparatedFor.ext ?_
  intro Y k hk
  simp only [objPresheaf_map]
  rw [obj_ext_of_isDiscrete (pullbackFiberCompIso x X.hom k).hom,
    obj_ext_of_isDiscrete (pullbackFiberCompIso y X.hom k).hom]
  exact h ((Sieve.overEquiv_iff S k).1 hk)

/-- Condition (2) of Stacks 026F for a category fibred in sets, when `objPresheaf p` is a sheaf:
each `Mor(x, y)` is a sheaf. -/
lemma isMorSheaf_of_isSheaf_objPresheaf {J : GrothendieckTopology 𝒞}
    (hJ : Presieve.IsSheaf J (objPresheaf p)) (U : 𝒞) (x y : p.Fiber U) :
    IsMorSheaf p J U x y := by
  refine (isSheaf_iff_isSheaf_of_type _ _).2 fun {X} S hS fam _ ↦ ?_
  obtain ⟨t⟩ : Nonempty ((morPresheaf p x y).obj (op X)) :=
    (nonempty_morPresheaf_obj_iff x y X).2
      (pullbackFiber_eq_of_locally_eq hJ S hS fun {Z} {k} hk ↦
        (nonempty_morPresheaf_obj_iff x y Z).1 ⟨fam k hk⟩)
  exact ⟨t, fun _ _ _ ↦ Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩

/-- If the morphism presheaves of a category fibred in sets are sheaves, then `objPresheaf p` is
separated. -/
lemma isSeparatedFor_objPresheaf_of_isMorSheaf {J : GrothendieckTopology 𝒞}
    (hmor : ∀ (V : 𝒞) (x y : p.Fiber V), IsMorSheaf p J V x y)
    {V : 𝒞} (S : Sieve V) (hS : S ∈ J V) :
    Presieve.IsSeparatedFor (objPresheaf p) (S : Presieve V) := by
  intro fam a b ha hb
  have hlocal : ∀ ⦃Y : 𝒞⦄ (k : Y ⟶ V), S k → pullbackFiber p a k = pullbackFiber p b k :=
    fun {_} k hk ↦ by
      simpa only [objPresheaf_map] using (ha k hk).trans (hb k hk).symm
  have hfam : ∀ ⦃Z : Over V⦄ ⦃k : Z ⟶ Over.mk (𝟙 V)⦄,
      ((Sieve.overEquiv (Over.mk (𝟙 V))).symm S) k →
        pullbackFiber p a Z.hom = pullbackFiber p b Z.hom := by
    intro Z k hk
    rw [show Z.hom = k.left by simpa using (Over.w k).symm]
    exact hlocal k.left hk
  have famMor : Presieve.FamilyOfElements (morPresheaf p a b)
      (((Sieve.overEquiv (Over.mk (𝟙 V))).symm S : Sieve (Over.mk (𝟙 V))) :
        Presieve (Over.mk (𝟙 V))) :=
    fun {Z} k hk ↦ ((nonempty_morPresheaf_obj_iff a b Z).2 (hfam hk)).some
  obtain ⟨t, -⟩ := (isSheaf_iff_isSheaf_of_type _ _).1 (hmor V a b) _
    (J.overEquiv_symm_mem_over (Over.mk (𝟙 V)) S hS) famMor
    (fun _ _ _ _ _ _ _ _ _ _ ↦ Subsingleton.elim _ _)
  have hid := (nonempty_morPresheaf_obj_iff a b (Over.mk (𝟙 V))).1 ⟨t⟩
  simp only [Over.mk_hom] at hid
  rw [← obj_ext_of_isDiscrete (pullbackFiberIdIso a).hom,
    ← obj_ext_of_isDiscrete (pullbackFiberIdIso b).hom]
  exact hid

end MorSheaf

/-! ### Condition (3) of Stacks 026F is the gluing half of the sheaf condition

A descent datum for a category fibred in sets is nothing but a compatible family of sections of
`objPresheaf p`: the gluing isomorphisms are the unique witnesses that two restrictions agree, and
the cocycle and base-change conditions hold automatically because the fibres are thin. Effectivity
of the datum is the existence of an amalgamation. -/

section Descent

variable {p : 𝒮 ⥤ 𝒞} [p.IsFiberedInSets]

/-- A compatible family of sections of `objPresheaf p` on a sieve `R` is a descent datum: the
gluing isomorphisms are the equalities the compatibility asserts. -/
noncomputable def sieveDescentDatumOfObjFamily {U : 𝒞} (R : Sieve U)
    (fam : Presieve.FamilyOfElements (objPresheaf p) (R : Presieve U)) (hfam : fam.Compatible) :
    SieveDescentDatum p R where
  obj {V} f hf := (fam f hf : p.Fiber V)
  iso {_ _ _} {_} hf {_} hg ε ε' heq := eqToIso (hfam ε ε' hf hg heq)
  cocycle := by intros; exact Subsingleton.elim _ _
  iso_pullback := by intros; exact Subsingleton.elim _ _

/-- The family of sections of `objPresheaf p` underlying a descent datum. -/
def famOfSieveDescentDatumObj {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum p R) :
    Presieve.FamilyOfElements (objPresheaf p) (R : Presieve U) :=
  fun _ f hf ↦ D.obj f hf

/-- The family of sections of `objPresheaf p` underlying a descent datum is compatible: its gluing
isomorphisms are exactly the witnesses of that compatibility, the fibres being discrete. -/
lemma famOfSieveDescentDatumObj_compatible {U : 𝒞} {R : Sieve U} (D : SieveDescentDatum p R) :
    (famOfSieveDescentDatumObj D).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
  dsimp only [objPresheaf_obj]
  exact obj_ext_of_isDiscrete (D.iso h₁ h₂ g₁ g₂ hcomm).hom

/-- The composite of a morphism of the fibre over `V` into the chosen pullback of `a` along `f`
with the cartesian map to `a` lies over `f`. -/
private lemma isHomLift_fiberInclusion_map_comp_pullbackMap {U V : 𝒞} (f : V ⟶ U) (a : p.Fiber U)
    {y : p.Fiber V} (ψ : y ⟶ pullbackFiber p a f) :
    p.IsHomLift f (Fiber.fiberInclusion.map ψ ≫ IsPreFibered.pullbackMap a.2 f) := by
  have : p.IsHomLift (𝟙 V) (Fiber.fiberInclusion.map ψ) := ψ.2
  have h0 : p.IsHomLift (𝟙 V ≫ f) (Fiber.fiberInclusion.map ψ ≫ IsPreFibered.pullbackMap a.2 f) :=
    inferInstance
  rwa [Category.id_comp] at h0

/-- Condition (3) of Stacks 026F for a category fibred in sets, when `objPresheaf p` is a sheaf:
every descent datum is effective. -/
lemma hasEffectiveDescent_of_isSheaf_objPresheaf {J : GrothendieckTopology 𝒞}
    (hJ : Presieve.IsSheaf J (objPresheaf p)) : HasEffectiveDescent p J := by
  intro U R hR D
  obtain ⟨a, ha, -⟩ := hJ R hR _ (famOfSieveDescentDatumObj_compatible D)
  have key : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R f), D.obj f hf = pullbackFiber p a f :=
    fun {_} f hf ↦ (ha f hf).symm
  refine ⟨a, fun {V} f hf ↦ Fiber.fiberInclusion.map (eqToHom (key f hf)) ≫
    IsPreFibered.pullbackMap a.2 f, fun {V} f hf ↦ ?_, fun {V W Z} {f} hf {g} hg ε ε' heq ↦ ?_⟩
  · have : IsIso (Fiber.fiberInclusion.map (eqToHom (key f hf))) :=
      inferInstanceAs (IsIso (Fiber.fiberInclusion.mapIso (eqToIso (key f hf))).hom)
    have : p.IsStronglyCartesian (𝟙 V) (Fiber.fiberInclusion.map (eqToHom (key f hf))) :=
      IsStronglyCartesian.of_isIso p (𝟙 V) _
    have hcomp : p.IsStronglyCartesian (𝟙 V ≫ f)
        (Fiber.fiberInclusion.map (eqToHom (key f hf)) ≫ IsPreFibered.pullbackMap a.2 f) :=
      IsStronglyCartesian.comp p
    rw [Category.id_comp] at hcomp
    infer_instance
  · have := isHomLift_fiberInclusion_map_comp_pullbackMap f a (eqToHom (key f hf))
    have := isHomLift_fiberInclusion_map_comp_pullbackMap g a (eqToHom (key g hg))
    have := isHomLift_fiberInclusion_map_comp_pullbackMap ε' (D.obj g hg)
      (D.iso hf hg ε ε' heq).hom
    have : p.IsHomLift (ε ≫ f) (Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom ≫
        IsPreFibered.pullbackMap (D.obj g hg).2 ε' ≫
          (Fiber.fiberInclusion.map (eqToHom (key g hg)) ≫ IsPreFibered.pullbackMap a.2 g)) := by
      rw [heq]
      infer_instance
    exact IsFiberedInSets.hom_ext_of_isHomLift p (ε ≫ f) _ _

end Descent

/-! ### Stacks in sets and sheaves -/

section Main

variable (p : 𝒮 ⥤ 𝒞) [p.IsFiberedInSets]

/-- Let `(𝒞, J)` be a site. Under the equivalence of Categories, Stacks 02Y2 between presheaves of
sets on `𝒞` and categories fibred in sets over `𝒞`, the stacks in sets correspond precisely to the
sheaves: a category fibred in sets `p : 𝒮 ⥤ 𝒞` is a stack in sets over `(𝒞, J)` if and only if its
presheaf of objects `U ↦ Ob(𝒮_U)` is a sheaf. -/
@[stacks 0430]
theorem isStackInSets_iff_isSheaf_objPresheaf (J : GrothendieckTopology 𝒞) :
    p.IsStackInSets J ↔ Presheaf.IsSheaf J (objPresheaf p) := by
  rw [isSheaf_iff_isSheaf_of_type]
  refine ⟨fun h {V} S hS fam hfam ↦ ?_, fun hJ ↦
    ⟨⟨inferInstance, isMorSheaf_of_isSheaf_objPresheaf hJ,
      hasEffectiveDescent_of_isSheaf_objPresheaf hJ⟩, fun _ ↦ inferInstance⟩⟩
  obtain ⟨x, ζ, hcart, -⟩ :=
    h.isStack.hasEffectiveDescent S hS (sieveDescentDatumOfObjFamily S fam hfam)
  have hamalg : fam.IsAmalgamation x := by
    intro Y f hf
    have := (hcart f hf).toIsHomLift
    have := (IsPreFibered.pullbackMap.IsCartesian x.2 f).toIsHomLift
    obtain ⟨hdom, -⟩ :=
      IsFiberedInSets.eq_of_isHomLift p f (IsPreFibered.pullbackMap x.2 f) (ζ f hf)
    exact Subtype.ext hdom
  exact ⟨x, hamalg,
    fun t ht ↦ isSeparatedFor_objPresheaf_of_isMorSheaf h.isStack.isMorSheaf S hS fam t x ht
      hamalg⟩

end Main

end Functor

end CategoryTheory
