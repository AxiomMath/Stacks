module

public import Mathlib.Basic.Finite.Sum
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSingleRelation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleStalkFunctor
public import StacksCore.Tactic.StacksAttribute

/-! # The stalk of a flat sheaf of modules is flat

Let `(C, O)` be a ringed site and let `p` be a point of `C`. Stacks 05VB says that if `F` is a
flat sheaf of `O`-modules then the stalk `F_p` is a flat module over the stalk `O_p`. This file
proves that.

## The argument

The source deduces 05VB from Stacks 05VD, the statement that a flat module pulls back to a flat
module along a morphism of ringed topoi, by viewing the point as such a morphism. That route is
not taken here: 05VD rests on topos-theoretic input which is not available. Instead the
*equational* criterion is used on both sides.

* Over the site, flatness of `F` gives the local equational criterion of Stacks 08FC, part (2):
  `Stacks.SheafOfModules.hasLocalSingleRelationFactorizations_of_isFlat`. A relation
  `∑ aᵢ sᵢ = 0` among sections over an object `U` admits, on a covering of `U`, a factorisation
  of the `sᵢ` through a finite free module by a matrix annihilating the relation.
* Over the stalk, Mathlib's equational criterion for a module
  (`Module.Flat.of_forall_isTrivialRelation`) says that a module is flat as soon as every
  relation `∑ fᵢ xᵢ = 0` in it is *trivial*, i.e. the `xᵢ` factor through a finite free module by
  a matrix annihilating the relation. This is the direction "factorisations imply flat".

The passage between them is the germ API. A relation in the stalk is lifted to a relation over a
neighbourhood: finitely many germs are represented over one neighbourhood because the category of
neighbourhoods of a point is cofiltered (`Stacks.exists_common_neighborhood`), and the relation
itself holds after shrinking the neighbourhood once more, because a germ vanishes exactly when the
section dies on a smaller neighbourhood. Then 08FC produces a covering of that neighbourhood, and
the defining property of a point — covering sieves are jointly surjective on fibres — selects a
member of the covering which the point's fibre still hits. Taking germs of the factorisation
found on that member gives the triviality of the original relation.

## Main definitions

* `Stacks.moduleStalkGerm` and `Stacks.ringStalkGerm`: the germ maps `F(U) → F_p` and
  `O(U) → O_p` at a neighbourhood `(U, ξ)` of the point, as an additive map and a ring
  homomorphism into the stalk of the structure sheaf taken in commutative rings.
* `Stacks.ringStalkComparison`: the comparison from the stalk of the structure sheaf computed in
  commutative rings to the stalk of its underlying sheaf of rings, along which the module stalk
  is restricted.

## Main results

* `Stacks.SheafOfModules.isFlatModuleStalk_of_isFlat`: **Stacks 05VB.** The stalk of a flat sheaf
  of modules at a point of a ringed site is flat over the stalk of the structure sheaf.
* `Stacks.exists_common_neighborhood` and `Stacks.exists_common_neighborhood₂`: a finite family,
  respectively two finite families, of neighbourhoods of a point of a site admit a common
  refinement.
* `Stacks.exists_germ_representatives`: a finite family of elements of the stalk of the structure
  sheaf together with a finite family of elements of the stalk of a sheaf of modules are all
  germs of sections over one common neighbourhood.
* `Stacks.moduleStalkGerm_smul`: the germ map is compatible with the action of the structure
  sheaf, where the stalk is a module over the stalk of the structure sheaf in commutative rings.

## Implementation notes

The universe of the sections is `max v w` rather than an independent `w`, and `HasSheafify` is
required rather than `HasWeakSheafify`. Both are inherited from
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSingleRelation`, which supplies part (1)
implies part (2) of Stacks 08FC, and ultimately from
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatEquivalence`, where the free presheaf used to
build the relation subpresheaf is free on the index set `V ⟶ U` and so lives in the morphism
universe. The helper lemmas of this file carry no such restriction and are stated for an
independent section universe `w`.

The stalk of a sheaf of modules is a module over the stalk of the structure sheaf by restriction
of scalars along `Stacks.commRingSheafFiberIso`, so its scalar action is only definitionally the
action of the stalk in rings. Instance search runs below default transparency and does not see
through that, so the scalar step is isolated as `Stacks.moduleStalkGerm_smul`, whose binders are
all at the honest types and whose proof crosses the two actions once, by `exact`. Downstream of
it nothing but `Stacks.moduleStalkGerm` and `Stacks.ringStalkGerm` is used, and those are an
`AddMonoidHom` and a `RingHom` into the two stalks as the statement of 05VB sees them.

For the same reason the restriction steps are run as term-mode chains of
`Stacks.moduleStalkGerm_restrict` and `Stacks.ringStalkGerm_restrict` composed with `Eq.trans`,
rather than by `rw` on the hypothesis produced by 08FC: the two spellings of a restricted section
differ in the instances buried in the coercion of a `ModuleCat` morphism to a function, so the
`rw` unifier does not see the pattern although `exact` accepts the term.

## References

* [Stacks Project, Tag 05VB](https://stacks.math.columbia.edu/tag/05VB)
* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [Stacks Project, Tag 00HK](https://stacks.math.columbia.edu/tag/00HK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks

/-! ### Common refinements of finite families of neighbourhoods -/

section Neighborhood

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A finite family of neighbourhoods `(U i, ξ i)` of a point `Φ` of a site has a common
refinement: a neighbourhood `(V, η)` with morphisms `V ⟶ U i` carrying `η` to `ξ i`.

This is cofilteredness of the category of neighbourhoods of `Φ`, which is part of the data of a
point of a site. -/
lemma exists_common_neighborhood (Φ : J.Point.{w}) {ι : Type*} [Finite ι] (U : ι → C)
    (ξ : ∀ i, Φ.fiber.obj (U i)) :
    ∃ (V : C) (η : Φ.fiber.obj V) (g : ∀ i, V ⟶ U i), ∀ i, Φ.fiber.map (g i) η = ξ i := by
  classical
  cases nonempty_fintype ι
  obtain ⟨S, hS⟩ := IsCofiltered.inf_objs_exists (C := Φ.fiber.Elements)
    (Finset.univ.image fun i ↦ Φ.fiber.elementsMk (U i) (ξ i))
  have h : ∀ i, Nonempty (S ⟶ Φ.fiber.elementsMk (U i) (ξ i)) := fun i ↦
    hS (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  exact ⟨S.obj, S.val, fun i ↦ (h i).some.hom, fun i ↦ (h i).some.map_val⟩

/-- Two finite families of neighbourhoods of a point of a site have a common refinement. This is
the form in which `Stacks.exists_common_neighborhood` is used: the two families are the
neighbourhoods carrying germs of sections of the structure sheaf and those carrying germs of
sections of a sheaf of modules. -/
lemma exists_common_neighborhood₂ (Φ : J.Point.{w}) {ι κ : Type*} [Finite ι] [Finite κ]
    (U : ι → C) (U' : κ → C) (ξ : ∀ i, Φ.fiber.obj (U i)) (ξ' : ∀ j, Φ.fiber.obj (U' j)) :
    ∃ (V : C) (η : Φ.fiber.obj V) (g : ∀ i, V ⟶ U i) (g' : ∀ j, V ⟶ U' j),
      (∀ i, Φ.fiber.map (g i) η = ξ i) ∧ ∀ j, Φ.fiber.map (g' j) η = ξ' j := by
  obtain ⟨V, η, g, hg⟩ := exists_common_neighborhood Φ (Sum.elim U U')
    (fun i ↦ match i with | .inl i => ξ i | .inr j => ξ' j)
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : ∀ i, V ⟶ U i, ∀ i, Φ.fiber.map (g₁ i) η = ξ i :=
    ⟨fun i ↦ g (.inl i), fun i ↦ hg (.inl i)⟩
  obtain ⟨g₂, hg₂⟩ : ∃ g₂ : ∀ j, V ⟶ U' j, ∀ j, Φ.fiber.map (g₂ j) η = ξ' j :=
    ⟨fun j ↦ g (.inr j), fun j ↦ hg (.inr j)⟩
  exact ⟨V, η, g₁, g₂, hg₁, hg₂⟩

end Neighborhood

/-! ### The germ maps into the stalks of a ringed site -/

section Germs

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (Φ : J.Point.{w}) (O : Sheaf J CommRingCat.{w})
  (F : SheafOfModules.{w} (commRingSheafToRingSheaf O))

/-- The germ at a neighbourhood `(U, ξ)` of a point `Φ` of a section of `F` over `U`, as an
element of the stalk of `F` at `Φ` viewed as a module over the stalk of the structure sheaf in
commutative rings.

This is `Stacks.toPresheafModuleFiber` read at the restricted scalars: the two have the same
underlying additive map, and the point of restating it is that its codomain is the stalk as the
statement of Stacks 05VB sees it. -/
noncomputable def moduleStalkGerm (U : C) (ξ : Φ.fiber.obj U) :
    F.val.obj (op U) →+ moduleStalk Φ O F :=
  toPresheafModuleFiber Φ F.val U ξ

/-- The germ at a neighbourhood `(U, ξ)` of a point `Φ` of a section of the structure sheaf over
`U`, as an element of the stalk of the structure sheaf taken in commutative rings. -/
noncomputable def ringStalkGerm (U : C) (ξ : Φ.fiber.obj U) :
    (commRingSheafToRingSheaf O).obj.obj (op U) →+*
      (Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj :=
  (Φ.toPresheafFiber U ξ O.obj).hom

/-- The comparison from the stalk of the structure sheaf computed in commutative rings to the
stalk of its underlying sheaf of rings. The module stalk is the stalk over the latter with its
scalars restricted along this map. -/
noncomputable def ringStalkComparison :
    (Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj →+*
      (Φ.presheafFiber (A := RingCat.{w})).obj (commRingSheafToRingSheaf O).obj :=
  (commRingSheafFiberIso Φ O).inv.hom

/-- The comparison map takes the germ of a section of the structure sheaf computed in commutative
rings to its germ computed in rings. -/
lemma ringStalkComparison_ringStalkGerm (U : C) (ξ : Φ.fiber.obj U)
    (a : (commRingSheafToRingSheaf O).obj.obj (op U)) :
    ringStalkComparison Φ O (ringStalkGerm Φ O U ξ a)
      = Φ.toPresheafFiber U ξ (commRingSheafToRingSheaf O).obj a := by
  have h := Φ.toPresheafFiber_presheafFiberCompIso_hom_app
      (F := forget₂ CommRingCat.{w} RingCat.{w}) U ξ O.obj
  have h2 : (commRingSheafFiberIso Φ O).hom.hom
      (Φ.toPresheafFiber U ξ (commRingSheafToRingSheaf O).obj a)
      = ringStalkGerm Φ O U ξ a := ConcreteCategory.congr_hom h a
  rw [← congrArg (ringStalkComparison Φ O) h2]
  exact ConcreteCategory.congr_hom (commRingSheafFiberIso Φ O).hom_inv_id _

/-- The germ of `a • m` is the germ of `a` acting on the germ of `m`. This is the one step which
crosses between the stalk of the structure sheaf in commutative rings, whose action on the module
stalk is by restriction of scalars, and the stalk in rings, whose action is the one
`Stacks.toPresheafModuleFiber_smul` describes. -/
lemma moduleStalkGerm_smul (U : C) (ξ : Φ.fiber.obj U)
    (a : (commRingSheafToRingSheaf O).obj.obj (op U)) (m : F.val.obj (op U)) :
    moduleStalkGerm Φ O F U ξ (a • m)
      = ringStalkGerm Φ O U ξ a • moduleStalkGerm Φ O F U ξ m := by
  have key : toPresheafModuleFiber Φ F.val U ξ (a • m)
      = ringStalkComparison Φ O (ringStalkGerm Φ O U ξ a) •
          toPresheafModuleFiber Φ F.val U ξ m := by
    rw [ringStalkComparison_ringStalkGerm]
    exact toPresheafModuleFiber_smul Φ F.val U ξ a m
  exact key

/-- Germs of sections of a sheaf of modules are compatible with restriction along a morphism of
neighbourhoods. -/
lemma moduleStalkGerm_restrict {V U : C} (g : V ⟶ U) (η : Φ.fiber.obj V)
    (m : F.val.obj (op U)) :
    moduleStalkGerm Φ O F V η ((F.val.map g.op).hom m)
      = moduleStalkGerm Φ O F U (Φ.fiber.map g η) m :=
  (toPresheafModuleFiber_w Φ F.val g η m).symm

omit [LocallySmall.{w} C] in
/-- Germs of sections of the structure sheaf are compatible with restriction along a morphism of
neighbourhoods. -/
lemma ringStalkGerm_restrict {V U : C} (g : V ⟶ U) (η : Φ.fiber.obj V)
    (a : (commRingSheafToRingSheaf O).obj.obj (op U)) :
    ringStalkGerm Φ O V η (((commRingSheafToRingSheaf O).obj.map g.op).hom a)
      = ringStalkGerm Φ O U (Φ.fiber.map g η) a :=
  Φ.toPresheafFiber_w_apply g η O.obj a

/-- Every element of the stalk of a sheaf of modules is a germ. -/
lemma moduleStalkGerm_jointly_surjective (m : moduleStalk Φ O F) :
    ∃ (U : C) (ξ : Φ.fiber.obj U) (s : F.val.obj (op U)),
      moduleStalkGerm Φ O F U ξ s = m :=
  toPresheafModuleFiber_jointly_surjective Φ F.val m

/-- Every element of the stalk of the structure sheaf is a germ. -/
lemma ringStalkGerm_jointly_surjective
    (r : (Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj) :
    ∃ (U : C) (ξ : Φ.fiber.obj U) (a : (commRingSheafToRingSheaf O).obj.obj (op U)),
      ringStalkGerm Φ O U ξ a = r :=
  Φ.toPresheafFiber_jointly_surjective (P := O.obj) r

/-- A finite family of elements of the stalk of the structure sheaf and a finite family of
elements of the stalk of a sheaf of modules are simultaneously germs of sections over one common
neighbourhood of the point. -/
lemma exists_germ_representatives {n : ℕ}
    (f : Fin n → (Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj)
    (x : Fin n → moduleStalk Φ O F) :
    ∃ (U : C) (ξ : Φ.fiber.obj U) (a : Fin n → (commRingSheafToRingSheaf O).obj.obj (op U))
      (s : Fin n → F.val.obj (op U)),
      (∀ i, ringStalkGerm Φ O U ξ (a i) = f i) ∧
        (∀ i, moduleStalkGerm Φ O F U ξ (s i) = x i) := by
  choose U₁ ξ₁ a₀ ha₀ using fun i ↦ ringStalkGerm_jointly_surjective Φ O (f i)
  choose U₂ ξ₂ s₀ hs₀ using fun i ↦ moduleStalkGerm_jointly_surjective Φ O F (x i)
  obtain ⟨V, η, g₁, g₂, hg₁, hg₂⟩ := exists_common_neighborhood₂ Φ U₁ U₂ ξ₁ ξ₂
  refine ⟨V, η,
    fun i ↦ ((commRingSheafToRingSheaf O).obj.map (g₁ i).op).hom (a₀ i),
    fun i ↦ (F.val.map (g₂ i).op).hom (s₀ i), fun i ↦ ?_, fun i ↦ ?_⟩
  · change ringStalkGerm Φ O V η
        (((commRingSheafToRingSheaf O).obj.map (g₁ i).op).hom (a₀ i)) = f i
    rw [ringStalkGerm_restrict, hg₁ i]
    exact ha₀ i
  · change moduleStalkGerm Φ O F V η ((F.val.map (g₂ i).op).hom (s₀ i)) = x i
    rw [moduleStalkGerm_restrict, hg₂ i]
    exact hs₀ i

/-- A section of a sheaf of modules whose germ at a neighbourhood vanishes dies after restriction
to a smaller neighbourhood. -/
lemma exists_restrict_eq_zero_of_moduleStalkGerm_eq_zero (U : C) (ξ : Φ.fiber.obj U)
    (z : F.val.obj (op U)) (hz : moduleStalkGerm Φ O F U ξ z = 0) :
    ∃ (V : C) (g : V ⟶ U) (η : Φ.fiber.obj V), Φ.fiber.map g η = ξ ∧
      (F.val.map g.op).hom z = 0 := by
  have hz' : toPresheafModuleFiber Φ F.val U ξ z = toPresheafModuleFiber Φ F.val U ξ 0 := by
    rw [map_zero]
    exact hz
  obtain ⟨V, g, η, hgη, hres⟩ := (toPresheafModuleFiber_eq_iff Φ F.val U ξ z 0).1 hz'
  exact ⟨V, g, η, hgη, hres.trans (map_zero _)⟩

end Germs

namespace SheafOfModules

/-! ### Stacks 05VB -/

section Flat

variable {C : Type u} [Category.{v} C] [LocallySmall.{max v w} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max v w} RingCat.{max v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v w}]
  [HasSheafify J AddCommGrpCat.{max v w}]

/-- **Stacks Project, Tag 05VB.** Let `(C, O)` be a ringed site and let `Φ` be a point of `C`. If
`F` is a flat sheaf of `O`-modules, then the stalk of `F` at `Φ` is a flat module over the stalk
of `O` at `Φ`.

The proof runs the equational criterion for flatness on both sides. A relation `∑ fᵢ xᵢ = 0` in
the stalk is lifted to a relation among sections over a neighbourhood of `Φ`; the local
equational criterion for a flat sheaf of modules, Stacks 08FC part (2), factors those sections
through a finite free module on a covering of that neighbourhood; the point's fibre meets one
member of the covering, and the germs of that factorisation exhibit the original relation as
trivial, which is flatness of the stalk by Mathlib's equational criterion. -/
@[stacks 05VB, sga "4 V 1.6" "assertion 1"]
theorem isFlatModuleStalk_of_isFlat (Φ : J.Point.{max v w})
    (O : Sheaf J CommRingCat.{max v w})
    (F : _root_.SheafOfModules.{max v w} (commRingSheafToRingSheaf O)) (hF : IsFlat F) :
    IsFlatModuleStalk Φ O F := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro n f x h
  -- Represent the relation by sections over a single neighbourhood `(U, ξ)`.
  obtain ⟨U, ξ, a, s, ha, hs⟩ := exists_germ_representatives Φ O F f x
  have hgerm : moduleStalkGerm Φ O F U ξ (∑ i, a i • s i) = 0 := by
    rw [map_sum]
    simp only [moduleStalkGerm_smul, ha, hs]
    exact h
  -- The relation itself holds after shrinking the neighbourhood to `(V, η)`.
  obtain ⟨V, g, η, hgη, hV⟩ :=
    exists_restrict_eq_zero_of_moduleStalkGerm_eq_zero Φ O F U ξ _ hgerm
  obtain ⟨a', ha'⟩ : ∃ a' : Fin n → (commRingSheafToRingSheaf O).obj.obj (op V),
      ∀ i, a' i = ((commRingSheafToRingSheaf O).obj.map g.op).hom (a i) := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s' : Fin n → F.val.obj (op V),
      ∀ i, s' i = (F.val.map g.op).hom (s i) := ⟨_, fun _ ↦ rfl⟩
  have hrel : ∑ i, a' i • s' i = 0 := by
    rw [map_sum] at hV
    simp only [PresheafOfModules.map_smul] at hV
    simp only [ha', hs']
    exact hV
  -- Stacks 08FC, part (2): the sections factor through a finite free module on a covering of `V`.
  obtain ⟨S, hS, hfac⟩ :=
    hasLocalSingleRelationFactorizations_of_isFlat hF V n a' s' hrel
  -- The point's fibre meets a member `k : W ⟶ V` of that covering.
  obtain ⟨W, k, hkS, ζ, hζ⟩ := Φ.jointly_surjective S hS η
  obtain ⟨l, t, B, hst, hBa⟩ := hfac k hkS
  refine ⟨l, fun i j ↦ ringStalkGerm Φ O W ζ (B j i),
    fun j ↦ moduleStalkGerm Φ O F W ζ (t j), fun i ↦ ?_, fun j ↦ ?_⟩
  · change x i = ∑ j, ringStalkGerm Φ O W ζ (B j i) • moduleStalkGerm Φ O F W ζ (t j)
    have left : moduleStalkGerm Φ O F W ζ ((F.val.map k.op).hom (s' i)) = x i := by
      have t₁ := moduleStalkGerm_restrict Φ O F k ζ (s' i)
      have t₂ := moduleStalkGerm_restrict Φ O F g η (s i)
      rw [hζ] at t₁
      rw [hgη, ← hs' i] at t₂
      exact t₁.trans (t₂.trans (hs i))
    have right : moduleStalkGerm Φ O F W ζ (∑ j, B j i • t j)
        = ∑ j, ringStalkGerm Φ O W ζ (B j i) • moduleStalkGerm Φ O F W ζ (t j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ moduleStalkGerm_smul Φ O F W ζ (B j i) (t j)
    exact left.symm.trans
      ((congrArg (fun z ↦ moduleStalkGerm Φ O F W ζ z) (hst i)).trans right)
  · change ∑ i, f i * ringStalkGerm Φ O W ζ (B j i) = 0
    have hf : ∀ i, ringStalkGerm Φ O W ζ
        (((commRingSheafToRingSheaf O).obj.map k.op).hom (a' i)) = f i := by
      intro i
      have t₁ := ringStalkGerm_restrict Φ O k ζ (a' i)
      have t₂ := ringStalkGerm_restrict Φ O g η (a i)
      rw [hζ] at t₁
      rw [hgη, ← ha' i] at t₂
      exact t₁.trans (t₂.trans (ha i))
    calc ∑ i, f i * ringStalkGerm Φ O W ζ (B j i)
        = ringStalkGerm Φ O W ζ
            (∑ i, B j i * ((commRingSheafToRingSheaf O).obj.map k.op).hom (a' i)) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [map_mul, hf i, mul_comm]
      _ = ringStalkGerm Φ O W ζ 0 := congrArg (fun z ↦ ringStalkGerm Φ O W ζ z) (hBa j 0)
      _ = 0 := map_zero _

end Flat

end SheafOfModules

end Stacks
