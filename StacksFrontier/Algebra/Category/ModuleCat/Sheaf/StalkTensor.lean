module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleStalkFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafFlatCover
public import StacksCore.Tactic.StacksAttribute

/-!
# Flatness of the stalk of a flat sheaf of modules

Let `(C, J)` be a site, `O` a sheaf of commutative rings on it, and `F` a sheaf of `O`-modules.
Stacks 05VB asserts that if `F` is flat — that is, if tensoring with `F` is an exact endofunctor
of sheaves of `O`-modules (Stacks 03ER (3)) — then for every point `Φ` of the site the stalk
`F_Φ` is a flat module over the stalk `O_Φ`.

The proof here goes through the *local equational criterion* rather than through a comparison of
the stalk of a tensor product with the tensor product of the stalks. Stacks 08FC (1) ⟹ (2), which
is `Stacks.SheafOfModules.hasLocalSingleRelationFactorizations_of_isFlat_freeUniverse`, says that
a flat sheaf of modules has the property that every relation `∑ᵢ aᵢ • sᵢ = 0` among its sections
over an object `U` has, on a covering sieve of `U`, a factorisation `sᵢ|_V = ∑_k B_{ki} tₖ` of
the restricted sections through a finite free module by a matrix `B` with
`∑ᵢ B_{ki} aᵢ|_V = 0`. That is exactly
the shape of Mathlib's `Module.IsTrivialRelation`, and by
`Module.Flat.iff_forall_isTrivialRelation` (Stacks 00HK) the triviality of every relation is
flatness. So the whole content of 05VB is the transport of a relation between the stalk and a
neighbourhood: a relation among germs comes from a relation among sections over a single
neighbourhood (`Stacks.exists_germ_relation`), and a factorisation over a member of a covering
sieve through which the point factors gives, on taking germs, a factorisation in the stalk
(`Stacks.exists_germ_factorization`).

## Main definitions

* `Stacks.stalkRingEquiv Φ O` : the comparison `Stacks.commRingSheafFiberIso` between the
  `CommRingCat`-valued stalk of `O` and the `RingCat`-valued stalk of its underlying sheaf of
  rings, packaged as a `RingEquiv`. It is needed because `Stacks.moduleStalk` is a module over
  the former by restriction of scalars along the latter, while the germ maps land in the latter.

## Main results

* `Stacks.exists_toPresheafFiber_family` : a *finite family* of elements of the fibre of a
  presheaf at a point of a site consists of germs of sections over one common neighbourhood,
  which may moreover be chosen to refine a prescribed neighbourhood. Mathlib has the cases of
  one and two elements (`GrothendieckTopology.Point.toPresheafFiber_jointly_surjective` and
  `…₂`); the refinement clause is what lets the ring germs and the module germs of a relation be
  put over the same object.
* `Stacks.exists_germ_relation` : a relation `∑ᵢ bᵢ • yᵢ = 0` among germs at `Φ` is the germ of a
  relation `∑ᵢ aᵢ • sᵢ = 0` among sections over a single neighbourhood of `Φ`.
* `Stacks.flat_of_ringEquiv_of_forall_exists_factorization` : a purely algebraic bridge. It
  deduces `Module.Flat R M` from a relation-factorisation criterion stated over a second ring `S`
  isomorphic to `R` and acting compatibly on `M`.
* `Stacks.isFlatModuleStalk_of_hasLocalSingleRelationFactorizations` : the stalk of a sheaf of
  modules satisfying the single-relation local factorisation criterion of Stacks 08FC (2) is a
  flat module over the stalk of the structure sheaf. This is the universe-general form of the
  result, and the one to reuse.
* `Stacks.isFlatModuleStalk_of_isFlat_freeUniverse` : the statement of **Stacks 05VB** at a free
  section universe, obtained by combining the previous result with Stacks 08FC (1) ⟹ (2). The
  tagged form of 05VB is `Stacks.isFlatModuleStalk_of_isFlat` in
  `StacksDraft.Ch18.Sec39.Tag05VB`, which is stated at `max v w`; see the implementation notes.
* `Stacks.forall_isFlatModuleStalk_of_isFlat` : the forward implication of **Stacks 05VC**. The
  converse is not proved here; see the implementation notes.
* `Stacks.SheafOfModules.isFlat_of_mono_sheafTensorRight_map` : flatness of a sheaf of modules
  follows from the single statement that tensoring with it keeps the first map of a short exact
  sequence a monomorphism. This reduces the converse half of Stacks 05VC to one named gap.

## Implementation notes

**Universes.** Every result of this file keeps the site universes `u` and `v` and the section
universe `w` independent, assuming only `LocallySmall.{w} C` (which
`Stacks.presheafModuleFiber` requires) and `Φ : J.Point.{w}`. Its only extra input,
`Stacks.SheafOfModules.hasLocalSingleRelationFactorizations_of_isFlat_freeUniverse`
(Stacks 08FC (1) ⟹ (2)), is itself stated at a free section universe `w` and asks nothing of
`w` beyond the three sheafification hypotheses that 05VB already carries. So no narrowing to
`max v w` is needed here, and none is imposed: a ringed site whose section universe is smaller
than its morphism universe is covered.

This is why `Stacks.isFlatModuleStalk_of_isFlat_freeUniverse` exists alongside the tagged
`Stacks.isFlatModuleStalk_of_isFlat` of `StacksDraft.Ch18.Sec39.Tag05VB`: the latter is stated
with the module universe fixed to `max v w`, so it cannot be instantiated at a free `w`
(`max v ?w =?= w` is not solvable), and `Stacks.forall_isFlatModuleStalk_of_isFlat` below —
which is stated at a free `w` — cannot be deduced from it. The two say the same thing about
05VB; only the free-universe one is proved here, and the tag sits on the other.

**Why the ring isomorphism is needed.** `Stacks.moduleStalk Φ O F` is, by construction, the
`RingCat`-valued stalk of `F` with its scalars restricted along
`Stacks.commRingSheafFiberIso Φ O`, so that it is a module over the `CommRingCat`-valued stalk
`O_Φ` — which is the only one of the two carrying a `CommRing` instance, and so the only one over
which `Module.Flat` and `Module.IsTrivialRelation` can be stated. The germ maps, by contrast,
land in the `RingCat`-valued stalk. Rather than transport each germ, the whole relation-chasing
argument is run over the `RingCat`-valued stalk and the single crossing is confined to
`Stacks.flat_of_ringEquiv_of_forall_exists_factorization`, where the two ring structures and the
two module structures are explicit variables and no instance search can pick the wrong one.

**Two spellings of the same sections.** A presheaf of modules `M` over `R` has, for `f : X ⟶ Y`,
a restriction `M.map f` whose value is typed as an element of
`(ModuleCat.restrictScalars (R.map f).hom).obj (M.obj Y)` rather than of `M.obj Y`. The two are
equal types with *different* `AddCommMonoid` instances found by typeclass search, so a
`Finset.sum` formed at the first spelling is not the sum `map_sum` expects. Every restriction in
this file is therefore written through the bundled semilinear map
`PresheafOfModules.restrictₛₗ`, and every germ through the bundled `AddMonoidHom`
`Stacks.toPresheafModuleFiber`; `rfl` bridges the remaining `0 = 0`.

**The converse of 05VC is not proved.** By
`Stacks.SheafOfModules.isFlat_of_mono_sheafTensorRight_map` it reduces to showing that
`(Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj F` preserves the monomorphism of a short
exact sequence, which in turn reduces, via `Stacks.mono_of_mono_sheafModuleFiber`, to a
comparison of the stalk of a tensor product of sheaves of modules with the tensor product of the
stalks (Stacks 03EL and 05V3) at the level of a general *site*. That comparison exists for a
ringed *space* (`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`) but not for a
site, and it is not built here.

## References

* [Stacks Project, Tag 05VB](https://stacks.math.columbia.edu/tag/05VB)
* [Stacks Project, Tag 05VC](https://stacks.math.columbia.edu/tag/05VC)
* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [Stacks Project, Tag 00HK](https://stacks.math.columbia.edu/tag/00HK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' w v' v u' u

namespace Stacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section General

variable [LocallySmall.{w} C]

section Family

variable {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]
  {FC : A → A → Type*} {CC : A → Type w'}
  [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w'} A FC]
  [PreservesFilteredColimitsOfSize.{w, w} (forget A)]

/-- A finite family of elements of the fibre of a presheaf at a point of a site comes from a
single neighbourhood, which may moreover be taken to refine any prescribed neighbourhood. -/
lemma exists_toPresheafFiber_family (Φ : J.Point.{w}) (P : Cᵒᵖ ⥤ A) (X₀ : C)
    (x₀ : Φ.fiber.obj X₀) {l : ℕ} (m : Fin l → ToType (Φ.presheafFiber.obj P)) :
    ∃ (X : C) (x : Φ.fiber.obj X) (g : X ⟶ X₀), Φ.fiber.map g x = x₀ ∧
      ∃ z : Fin l → ToType (P.obj (op X)), ∀ i, Φ.toPresheafFiber X x P (z i) = m i := by
  induction l with
  | zero => exact ⟨X₀, x₀, 𝟙 X₀, by simp, fun i => i.elim0, fun i => i.elim0⟩
  | succ l ih =>
    obtain ⟨X, x, g, hg, z, hz⟩ := ih (fun i => m i.castSucc)
    obtain ⟨Y, y, t, ht⟩ := Φ.toPresheafFiber_jointly_surjective (P := P) (m (Fin.last l))
    obtain ⟨W, p, q, -⟩ :=
      IsCofilteredOrEmpty.cone_objs (Φ.fiber.elementsMk X x) (Φ.fiber.elementsMk Y y)
    refine ⟨W.1, W.2, p.1 ≫ g, ?_, Fin.lastCases ((P.map q.1.op) t) fun i => (P.map p.1.op) (z i),
      Fin.lastCases ?_ ?_⟩
    · rw [Φ.fiber.map_comp]
      exact (congrArg (Φ.fiber.map g) p.2).trans hg
    · simpa [Φ.toPresheafFiber_w_apply q.1 W.2 P t, q.2] using ht
    · intro i
      simpa [Φ.toPresheafFiber_w_apply p.1 W.2 P (z i), p.2] using hz i

end Family

/-- The module form of `Stacks.exists_toPresheafFiber_family`: a finite family of elements of the
stalk of a presheaf of modules consists of germs of sections over a single neighbourhood. -/
lemma exists_toPresheafModuleFiber_family (Φ : J.Point.{w}) {R : Cᵒᵖ ⥤ RingCat.{w}}
    (M : PresheafOfModules.{w} R) (X₀ : C) (x₀ : Φ.fiber.obj X₀) {l : ℕ}
    (m : Fin l → (presheafModuleFiber Φ R).obj M) :
    ∃ (X : C) (x : Φ.fiber.obj X) (g : X ⟶ X₀), Φ.fiber.map g x = x₀ ∧
      ∃ z : Fin l → M.obj (op X), ∀ i, toPresheafModuleFiber Φ M X x (z i) = m i :=
  exists_toPresheafFiber_family Φ M.presheaf X₀ x₀ m

section Algebra

variable {R S M : Type*} [CommRing R] [Ring S] [AddCommGroup M] [Module S M] [Module R M]

/-- Flatness from a relation-factorisation criterion stated over a second, isomorphic ring. -/
lemma flat_of_ringEquiv_of_forall_exists_factorization (ε : R ≃+* S)
    (hε : ∀ (c : R) (m : M), c • m = ε c • m)
    (H : ∀ (l : ℕ) (b : Fin l → S) (y : Fin l → M), ∑ i, b i • y i = 0 →
      ∃ (k : ℕ) (B : Fin l → Fin k → S) (t : Fin k → M),
        (∀ i, y i = ∑ j, B i j • t j) ∧ ∀ j, ∑ i, B i j * b i = 0) :
    Module.Flat R M := by
  refine Module.Flat.of_forall_isTrivialRelation fun {l} {c} {m} hcm => ?_
  obtain ⟨k, B, t, h1, h2⟩ := H l (fun i => ε (c i)) m (by simpa [hε] using hcm)
  refine ⟨k, fun i j => ε.symm (B i j), t, fun i => ?_, fun j => ?_⟩
  · exact (h1 i).trans (Finset.sum_congr rfl fun j _ => by rw [hε, ε.apply_symm_apply])
  · have h3 := congrArg ε.symm (h2 j)
    rw [map_sum, map_zero] at h3
    simp only [map_mul, ε.symm_apply_apply] at h3
    exact Eq.trans (Finset.sum_congr rfl fun i _ => mul_comm (c i) (ε.symm (B i j))) h3

end Algebra

/-- The germ of a restricted module section is the germ of the section over the larger
neighbourhood. -/
private lemma toPresheafModuleFiber_restrictₛₗ {R : Cᵒᵖ ⥤ RingCat.{w}} (Φ : J.Point.{w})
    (M : PresheafOfModules.{w} R) {U V : C} (g : U ⟶ V) {x : Φ.fiber.obj U} {x' : Φ.fiber.obj V}
    (hx : Φ.fiber.map g x = x') (m : M.obj (op V)) :
    toPresheafModuleFiber Φ M U x (M.restrictₛₗ g.op m) = toPresheafModuleFiber Φ M V x' m :=
  hx ▸ (toPresheafModuleFiber_w Φ M g x m).symm

/-- A relation among germs at a point comes from a relation among sections over a single
neighbourhood of that point. -/
lemma exists_germ_relation (Φ : J.Point.{w}) {R : Cᵒᵖ ⥤ RingCat.{w}} (M : PresheafOfModules.{w} R)
    {l : ℕ} (b : Fin l → (Φ.presheafFiber (A := RingCat.{w})).obj R)
    (y : Fin l → (presheafModuleFiber Φ R).obj M) (hby : ∑ i, b i • y i = 0) :
    ∃ (V : C) (v : Φ.fiber.obj V) (a : Fin l → R.obj (op V)) (s : Fin l → M.obj (op V)),
      (∀ i, Φ.toPresheafFiber V v R (a i) = b i) ∧
        (∀ i, toPresheafModuleFiber Φ M V v (s i) = y i) ∧ ∑ i, a i • s i = 0 := by
  obtain ⟨@⟨X₀, x₀⟩⟩ := IsCofiltered.nonempty (C := Φ.fiber.Elements)
  obtain ⟨U₁, x₁, -, -, s₁, hs₁⟩ := exists_toPresheafModuleFiber_family Φ M X₀ x₀ y
  obtain ⟨U, x, g, hg, a, ha⟩ := exists_toPresheafFiber_family Φ R U₁ x₁ b
  have hs : ∀ i, toPresheafModuleFiber Φ M U x (M.restrictₛₗ g.op (s₁ i)) = y i := fun i =>
    (toPresheafModuleFiber_restrictₛₗ Φ M g hg _).trans (hs₁ i)
  have hrel : toPresheafModuleFiber Φ M U x (∑ i, a i • M.restrictₛₗ g.op (s₁ i)) = 0 := by
    rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hby
    rw [toPresheafModuleFiber_smul, ha i, hs i]
  obtain ⟨V, h, v, hv, hz⟩ := (toPresheafModuleFiber_eq_iff Φ M U x
    (∑ i, a i • M.restrictₛₗ g.op (s₁ i)) 0).1 (hrel.trans (map_zero _).symm)
  refine ⟨V, v, fun i => R.map h.op (a i),
    fun i => M.restrictₛₗ h.op (M.restrictₛₗ g.op (s₁ i)), fun i => ?_, fun i => ?_, ?_⟩
  · rw [Φ.toPresheafFiber_w_apply h v R (a i), hv]; exact ha i
  · exact (toPresheafModuleFiber_restrictₛₗ Φ M h hv _).trans (hs i)
  · have h0 : (M.restrictₛₗ h.op) (∑ i, a i • M.restrictₛₗ g.op (s₁ i)) = 0 := by
      rw [PresheafOfModules.restrictₛₗ_apply, hz, map_zero]
      rfl
    rw [map_sum] at h0
    simpa only [LinearMap.map_smulₛₗ] using h0

section Flat

variable (Φ : J.Point.{w}) (O : Sheaf J CommRingCat.{w})
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- `Stacks.commRingSheafFiberIso` as a ring isomorphism. -/
noncomputable def stalkRingEquiv :
    (Φ.presheafFiber (A := CommRingCat.{w})).obj O.obj ≃+*
      (Φ.presheafFiber (A := RingCat.{w})).obj (commRingSheafToRingSheaf O).obj where
  toFun := (commRingSheafFiberIso Φ O).inv.hom
  invFun := (commRingSheafFiberIso Φ O).hom.hom
  left_inv := (commRingSheafFiberIso Φ O).inv_hom_id_apply
  right_inv := (commRingSheafFiberIso Φ O).hom_inv_id_apply
  map_mul' := map_mul _
  map_add' := map_add _

/-- Stalkwise form of the local relation criterion. -/
lemma exists_germ_factorization (F : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O))
    (hF : SheafOfModules.HasLocalSingleRelationFactorizations O F) (l : ℕ)
    (b : Fin l → (Φ.presheafFiber (A := RingCat.{w})).obj (commRingSheafToRingSheaf O).obj)
    (y : Fin l → (presheafModuleFiber Φ (commRingSheafToRingSheaf O).obj).obj F.val)
    (hby : ∑ i, b i • y i = 0) :
    ∃ (k : ℕ)
      (B : Fin l → Fin k →
        (Φ.presheafFiber (A := RingCat.{w})).obj (commRingSheafToRingSheaf O).obj)
      (t : Fin k → (presheafModuleFiber Φ (commRingSheafToRingSheaf O).obj).obj F.val),
      (∀ i, y i = ∑ j, B i j • t j) ∧ ∀ j, ∑ i, B i j * b i = 0 := by
  obtain ⟨V, v, a, s, ha, hs, hrel⟩ := exists_germ_relation Φ F.val b y hby
  obtain ⟨S, hS, hfac⟩ := hF V l a s hrel
  obtain ⟨W, p, hp, w, hw⟩ := Φ.jointly_surjective S hS v
  obtain ⟨k, t, B, hB1, hB2⟩ := hfac p hp
  have hb : ∀ i, Φ.toPresheafFiber W w (commRingSheafToRingSheaf O).obj
      ((commRingSheafToRingSheaf O).obj.map p.op (a i)) = b i := fun i => by
    rw [Φ.toPresheafFiber_w_apply p w _ (a i), hw]; exact ha i
  refine ⟨k, fun i j => Φ.toPresheafFiber W w (commRingSheafToRingSheaf O).obj (B j i),
    fun j => toPresheafModuleFiber Φ F.val W w (t j), fun i => ?_, fun j => ?_⟩
  · rw [← hs i, ← hw, toPresheafModuleFiber_w Φ F.val p w (s i), hB1 i, map_sum]
    exact Finset.sum_congr rfl fun j _ => toPresheafModuleFiber_smul Φ F.val W w (B j i) (t j)
  · have h4 := congrArg (fun z => Φ.toPresheafFiber W w (commRingSheafToRingSheaf O).obj z)
      (hB2 j 0)
    rw [map_sum, map_zero] at h4
    simp only [map_mul, hb] at h4
    exact h4

/-- The stalk of a sheaf of modules satisfying the single-relation local factorisation
criterion is a flat module over the stalk of the structure sheaf. -/
theorem isFlatModuleStalk_of_hasLocalSingleRelationFactorizations
    (F : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O))
    (hF : SheafOfModules.HasLocalSingleRelationFactorizations O F) :
    IsFlatModuleStalk Φ O F := by
  let _ : Module ((Φ.presheafFiber (A := RingCat.{w})).obj (commRingSheafToRingSheaf O).obj)
      (moduleStalk Φ O F) :=
    ((presheafModuleFiber Φ (commRingSheafToRingSheaf O).obj).obj F.val).isModule
  exact flat_of_ringEquiv_of_forall_exists_factorization (stalkRingEquiv Φ O)
    (fun _ _ => rfl) (exists_germ_factorization Φ O F hF)

end Flat

end General

/-! ### Stacks 05VB, and the two halves of Stacks 05VC -/

section FlatFreeUniverse

variable [LocallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (O : Sheaf J CommRingCat.{w})
  (F : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O))

/-- **Stacks 05VB at a free section universe.** The stalk at a point of a site of a flat sheaf
of modules is a flat module over the stalk of the structure sheaf.

This is the general form of 05VB: the module universe `w` is independent of the morphism
universe `v`. The tagged form of 05VB, `Stacks.isFlatModuleStalk_of_isFlat`, fixes the module
universe to `max v w`, and so does not specialise to a free `w` — the unifier is left with
`max v ?w =?= w`. The hypotheses are otherwise the same (`HasWeakSheafify`, not `HasSheafify`),
and the two statements say the same thing about 05VB; the tag therefore sits on the other one,
and this form exists for the consumers that need a free `w` — here
`Stacks.forall_isFlatModuleStalk_of_isFlat`. -/
theorem isFlatModuleStalk_of_isFlat_freeUniverse (Φ : J.Point.{w})
    (hF : SheafOfModules.IsFlat F) :
    IsFlatModuleStalk Φ O F :=
  isFlatModuleStalk_of_hasLocalSingleRelationFactorizations Φ O F
    (SheafOfModules.hasLocalSingleRelationFactorizations_of_isFlat_freeUniverse hF)

/-- The forward implication of **Stacks 05VC**: a flat sheaf of modules has flat stalks at every
point of the site, in particular at every point of a conservative family. The conservativity of
the family is used only for the converse, which is not proved here. -/
@[sga "4 V 1.6" "assertion 1"]
theorem forall_isFlatModuleStalk_of_isFlat {I : Type*} (p : I → J.Point.{w})
    (hF : SheafOfModules.IsFlat F) : ∀ i, IsFlatModuleStalk (p i) O F :=
  fun i => isFlatModuleStalk_of_isFlat_freeUniverse O F (p i) hF

end FlatFreeUniverse

namespace SheafOfModules

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]
  (O : Sheaf J CommRingCat.{w})
  (F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))

/-- A sheaf of modules is flat as soon as tensoring with it keeps the first map of every short
exact sequence a monomorphism.

Flatness is exactness of `(Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj F`, and its
right-exactness half holds for every sheaf of modules
(`Stacks.preservesFiniteColimits_sheafTensorRight`, part of Stacks 03EX). Left exactness is, by
`CategoryTheory.Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono`, the conjunction of
the exactness of the image of a short exact sequence — which right exactness already supplies —
with the preservation of its monomorphism. So the monomorphism clause is all that is left, and
this lemma is the statement of that reduction. It is the form in which the converse half of
Stacks 05VC is still open. -/
theorem isFlat_of_mono_sheafTensorRight_map
    (h : ∀ S : ShortComplex
        (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)),
      S.ShortExact →
        Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F).map
          S.f)) :
    IsFlat F := by
  have hcolim : PreservesFiniteColimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F) :=
    inferInstance
  let : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F).Additive :=
    (additiveFunctor_iff _).1 (rightExactFunctor_le_additiveFunctor _ _ _
      ((rightExactFunctor_iff _).2 hcolim))
  refine (exactFunctor_iff _).2 ⟨?_, hcolim⟩
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  exact fun S hS => ⟨((Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (F := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj F)).1
      hcolim S hS).1, h S hS⟩

end SheafOfModules

end Stacks
