module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackPresentationData
public import StacksCore.Tactic.StacksAttribute

/-!
# Presentation data transports along the inverse image of a morphism of topoi

Let `f` be a morphism of topoi between the topoi of sheaves of sets on two sites, let `O` be a
sheaf of rings on the target site and `F` a sheaf of `O`-modules.  Written out in sections, a
finite presentation of `F` over an object `W` of the target site is a tuple `s : Fin n → F(W)`
of generating sections together with a matrix `t : Fin m → Fin n → O(W)` of relations, subject
to the three conditions of `Stacks.Sheaves.LocalGeneration.IsPresentationData`:

* **(A)** every row of `t` is a relation among the `s`, that is `∑ i, t j i • s i = 0`;
* **(B)** the `s` generate `F` locally on `W`;
* **(C)** every relation among the `s` is locally an `O`-linear combination of the rows of `t`.

This file proves that this data transports along `f⁻¹`: a point of `f⁻¹` of the sheaf of such
data, over an object `V` of the *source* site, carries presentation data for the inverse-image
module `f⁻¹F` over `V`, with the same `n` and the same `m`
(`Stacks.Sheaves.PresentationTransport.isPresentationData_pullback`, and
`pullbackPresData` for the same statement read as a map of the data sheaves of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackPresentationData`).

Together with the local criterion of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFinitePresentation` and a covering of
the source site by objects over which such a point exists, this is the inverse-image half of
Stacks 03DO (7): pullback preserves finite presentation.  The extension-of-scalars half, and
the reduction of the clause to the inverse-image factor, are in that file; the covering of the
source site is `Stacks.Topos.exists_cover_inverseImage_sections`.

## Main definitions

* `Stacks.Sheaves.PresentationTransport.PresentationDataSheaf`: the interface used here of a
  sheaf of presentation data — a sheaf of sets whose points carry `IsPresentationData`.
  `presentationDataSheaf` instantiates it at the subsheaf `presDataSheaf` of `F^n × (O^n)^m`
  of `ToposPullbackPresentationData`.
* `Stacks.Sheaves.PresentationTransport.pullbackGen` and `pullbackRel`: the generating sections
  and the relation tuples carried by a point of `f⁻¹` of a sheaf of presentation data.
* `Stacks.Sheaves.PresentationTransport.ringCombination`: an `O`-linear combination of sections
  of `O`, as a morphism of sheaves of sets, with `ringCombinationValue` on sections.
* `Stacks.Sheaves.PresentationTransport.syzygySheaf`, `relationMap`: the sheaf of relations
  among the generating sections, as an equalizer, and the matrix action into it.
* `Stacks.Sheaves.PresentationTransport.inverseImageSections`: sections over a fixed object of
  the inverse image of a sheaf of types, as a functor preserving finite limits.
* `Stacks.Sheaves.PresentationTransport.tupleObjMk`, `pointOfFanIsLimit`: points of a preserved
  product, and `exists_point_of_forkIsLimit` for a preserved equalizer.

## Main results

* `Stacks.Sheaves.PresentationTransport.isPresentationData_pullback`: the transport, and
  `pullbackPresData` the same statement between the data sheaves.
* `Stacks.Sheaves.PresentationTransport.map_ringCombination`: `f⁻¹` of an `O`-linear
  combination of sections of `O` is the `f⁻¹O`-linear combination of the images.
* `Stacks.Sheaves.PresentationTransport.relationMap_locallySurjective`: condition (C) gives
  local surjectivity of the matrix action onto the sheaf of relations.

## Implementation notes

The two sites, their homs and the section universes `w` and `w'` of the two topoi are
independent, and the only hypotheses are the four `HasSheafCompose` instances needed to speak of
the underlying sheaves of sets.

## References

* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sheaves.PresentationTransport

open Stacks.Sheaves Stacks.Sheaves.LocalGeneration

universe v u v' u' w w'

/-! ### A linear combination of relations is a relation -/

section Combination

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- An `O`-linear combination of sections of `O`, with the sections of `O` as its ascribed
type. -/
def ringCombinationValue (R : Sheaf J RingCat.{w}) {U : Cᵒᵖ} {m : ℕ}
    (c t : Fin m → R.obj.obj U) : R.obj.obj U := ∑ j, c j * t j

/-- An `O`-linear combination of relations among a tuple of sections is a relation. -/
lemma combinationValue_ringCombinationValue {M : SheafOfModules.{w} R} {U : Cᵒᵖ} {n m : ℕ}
    (s : Fin n → M.val.obj U) (t : Fin m → Fin n → R.obj.obj U) (c : Fin m → R.obj.obj U)
    (h : ∀ j, combinationValue M (t j) s = 0) :
    combinationValue M (fun i => ringCombinationValue R c (fun j => t j i)) s = 0 := by
  have h1 : ∀ i, (ringCombinationValue R c (fun j => t j i) • s i : M.val.obj U) =
      ∑ j, c j • (t j i • s i) := by
    intro i
    rw [ringCombinationValue, Finset.sum_smul]
    exact Finset.sum_congr rfl fun j _ => mul_smul (c j) (t j i) (s i)
  calc combinationValue M (fun i => ringCombinationValue R c (fun j => t j i)) s
      = ∑ i, ∑ j, c j • (t j i • s i) := Finset.sum_congr rfl fun i _ => h1 i
    _ = ∑ j, c j • combinationValue M (t j) s := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => (Finset.smul_sum ..).symm
    _ = 0 := by simp only [h, smul_zero, Finset.sum_const_zero]

end Combination

/-! ### Linear combinations of sections of a sheaf of rings -/

section RingCombination

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})]

/-- An `O`-linear combination of two families of maps into the underlying sheaf of sets of a
sheaf of rings. -/
noncomputable def ringCombination (R : Sheaf J RingCat.{w}) {T : Sheaf J (Type w)} {m : ℕ}
    (c t : Fin m → (T ⟶ Sheaf.ringSheaf R)) : T ⟶ Sheaf.ringSheaf R where
  hom :=
    { app := fun U => ↾(fun x => ringCombinationValue R
        (fun j => ringSection R ((c j).hom.app U x)) (fun j => ringSection R ((t j).hom.app U x)))
      naturality := by
        intro U V g
        ext x
        let cU : Fin m → R.obj.obj U := fun j => (c j).hom.app U x
        let tU : Fin m → R.obj.obj U := fun j => (t j).hom.app U x
        let cV : Fin m → R.obj.obj V := fun j => (c j).hom.app V (T.obj.map g x)
        let tV : Fin m → R.obj.obj V := fun j => (t j).hom.app V (T.obj.map g x)
        change (∑ j, cV j * tV j : R.obj.obj V) = R.obj.map g (∑ j, cU j * tU j)
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
        exact congrArg₂ (fun (a b : R.obj.obj V) => a * b)
          (ConcreteCategory.congr_hom ((c j).hom.naturality g) x)
          (ConcreteCategory.congr_hom ((t j).hom.naturality g) x) }

/-- A linear combination of sections of `O`, evaluated at a point. -/
@[simp]
lemma ringCombination_hom_app (R : Sheaf J RingCat.{w}) {T : Sheaf J (Type w)} {m : ℕ}
    (c t : Fin m → (T ⟶ Sheaf.ringSheaf R)) (U : Cᵒᵖ) (x : T.obj.obj U) :
    (ringCombination R c t).hom.app U x =
      ringCombinationValue R (fun j => ringSection R ((c j).hom.app U x))
        (fun j => ringSection R ((t j).hom.app U x)) :=
  rfl

/-- `ringCombination_hom_app`, with the left-hand side in the `ringSection` spelling of the
sections of `O`. -/
@[simp]
lemma ringSection_ringCombination_hom_app (R : Sheaf J RingCat.{w}) {T : Sheaf J (Type w)}
    {m : ℕ} (c t : Fin m → (T ⟶ Sheaf.ringSheaf R)) (U : Cᵒᵖ) (x : T.obj.obj U) :
    ringSection R ((ringCombination R c t).hom.app U x) =
      ringCombinationValue R (fun j => ringSection R ((c j).hom.app U x))
        (fun j => ringSection R ((t j).hom.app U x)) :=
  rfl

/-- The section of `Sheaf.ringAddHom` at a pair of maps into the underlying sheaf. -/
lemma lift_ringAddHom_app (R : Sheaf J RingCat.{w}) {T : Sheaf J (Type w)}
    (α β : T ⟶ Sheaf.ringSheaf R) (U : Cᵒᵖ) (x : T.obj.obj U) :
    (prod.lift α β ≫ Sheaf.ringAddHom R).hom.app U x =
      ringSection R (α.hom.app U x) + ringSection R (β.hom.app U x) := by
  have h : (prod.lift α β ≫ Sheaf.ringAddHom R).hom.app U x =
      ringSection R ((prod.fst : Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R ⟶
          Sheaf.ringSheaf R).hom.app U ((prod.lift α β).hom.app U x)) +
        ringSection R ((prod.snd : Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R ⟶
          Sheaf.ringSheaf R).hom.app U ((prod.lift α β).hom.app U x)) :=
    rfl
  rw [h, prod_lift_fst_apply, prod_lift_snd_apply]

/-- The section of `Sheaf.ringMulHom` at a pair of maps into the underlying sheaf. -/
lemma lift_ringMulHom_app (R : Sheaf J RingCat.{w}) {T : Sheaf J (Type w)}
    (α β : T ⟶ Sheaf.ringSheaf R) (U : Cᵒᵖ) (x : T.obj.obj U) :
    (prod.lift α β ≫ Sheaf.ringMulHom R).hom.app U x =
      ringSection R (α.hom.app U x) * ringSection R (β.hom.app U x) := by
  have h : (prod.lift α β ≫ Sheaf.ringMulHom R).hom.app U x =
      ringSection R ((prod.fst : Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R ⟶
          Sheaf.ringSheaf R).hom.app U ((prod.lift α β).hom.app U x)) *
        ringSection R ((prod.snd : Sheaf.ringSheaf R ⨯ Sheaf.ringSheaf R ⟶
          Sheaf.ringSheaf R).hom.app U ((prod.lift α β).hom.app U x)) :=
    rfl
  rw [h, prod_lift_fst_apply, prod_lift_snd_apply]

/-- The empty `O`-linear combination is the zero section. -/
theorem ringCombination_zero (R : Sheaf J RingCat.{w}) {T : Sheaf J (Type w)}
    (c t : Fin 0 → (T ⟶ Sheaf.ringSheaf R)) :
    ringCombination R c t = terminal.from T ≫ Sheaf.ringZeroHom R := by
  ext U x
  change ringCombinationValue R (fun j => ringSection R ((c j).hom.app U x))
    (fun j => ringSection R ((t j).hom.app U x)) = (0 : R.obj.obj U)
  simp [ringCombinationValue]

/-- An `O`-linear combination of `m + 1` terms, peeled at the first one. -/
theorem ringCombination_succ (R : Sheaf J RingCat.{w}) {T : Sheaf J (Type w)} {m : ℕ}
    (c t : Fin (m + 1) → (T ⟶ Sheaf.ringSheaf R)) :
    ringCombination R c t =
      prod.lift (prod.lift (c 0) (t 0) ≫ Sheaf.ringMulHom R)
        (ringCombination R (fun j => c j.succ) (fun j => t j.succ)) ≫ Sheaf.ringAddHom R := by
  ext U x
  have h := lift_ringAddHom_app R (prod.lift (c 0) (t 0) ≫ Sheaf.ringMulHom R)
    (ringCombination R (fun j => c j.succ) (fun j => t j.succ)) U x
  rw [lift_ringMulHom_app] at h
  refine Eq.trans ?_ h.symm
  change ringCombinationValue R (fun j => ringSection R ((c j).hom.app U x))
      (fun j => ringSection R ((t j).hom.app U x)) =
    ringSection R ((c 0).hom.app U x) * ringSection R ((t 0).hom.app U x) +
      ringCombinationValue R (fun j => ringSection R ((c j.succ).hom.app U x))
        (fun j => ringSection R ((t j.succ).hom.app U x))
  simp [ringCombinationValue, Fin.sum_univ_succ]

end RingCombination

/-! ### Linear combinations of sections of a sheaf of modules -/

section LinearCombination

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- Precomposition of a linear combination of maps into the underlying sheaf of a sheaf of
modules. -/
lemma linearCombination_precomp (M : SheafOfModules.{w} R) {T T' : Sheaf J (Type w)} {r : ℕ}
    (h : T' ⟶ T) (a : Fin r → (T ⟶ Sheaf.ringSheaf R))
    (s : Fin r → (T ⟶ moduleUnderlying M)) :
    h ≫ linearCombination M a s =
      linearCombination M (fun i => h ≫ a i) (fun i => h ≫ s i) :=
  rfl

/-- A linear combination of maps into the underlying sheaf of a sheaf of modules, evaluated at
a point. -/
@[simp]
lemma linearCombination_hom_app (M : SheafOfModules.{w} R) {T : Sheaf J (Type w)} {r : ℕ}
    (a : Fin r → (T ⟶ Sheaf.ringSheaf R)) (s : Fin r → (T ⟶ moduleUnderlying M)) (U : Cᵒᵖ)
    (x : T.obj.obj U) :
    (linearCombination M a s).hom.app U x =
      combinationValue M (fun i => ringSection R ((a i).hom.app U x))
        (fun i => moduleSection M ((s i).hom.app U x)) :=
  rfl

/-- A linear combination which vanishes at every point is the zero map. -/
lemma linearCombination_eq_zero (M : SheafOfModules.{w} R) {T : Sheaf J (Type w)} {r : ℕ}
    (a : Fin r → (T ⟶ Sheaf.ringSheaf R)) (s : Fin r → (T ⟶ moduleUnderlying M))
    (h : ∀ (U : Cᵒᵖ) (x : T.obj.obj U), combinationValue M
      (fun i => ringSection R ((a i).hom.app U x))
      (fun i => moduleSection M ((s i).hom.app U x)) = 0) :
    linearCombination M a s = terminal.from T ≫ Sheaf.moduleZeroHom R M := by
  ext U x
  exact h U x

end LinearCombination

/-! ### Points of a limit, through a functor to types -/

section Points

universe t

/-- A limit fork is injective on points. -/
lemma eq_of_forkIsLimit {X Y Z : Type t} {u v : X ⟶ Y} {i : Z ⟶ X} {wc : i ≫ u = i ≫ v}
    (h : IsLimit (Fork.ofι i wc)) {z₁ z₂ : Z} (he : i z₁ = i z₂) : z₁ = z₂ := by
  have h2 : (↾fun _ : PUnit.{t + 1} => z₁) ≫ i = (↾fun _ : PUnit.{t + 1} => z₂) ≫ i := by
    ext _
    exact he
  exact ConcreteCategory.congr_hom (Fork.IsLimit.hom_ext h
    (by simpa only [Fork.ι_ofι] using h2)) PUnit.unit

/-- A point at which the two legs of a limit fork agree is the image of a point of the fork. -/
lemma exists_point_of_forkIsLimit {X Y Z : Type t} {u v : X ⟶ Y} {i : Z ⟶ X}
    {wc : i ≫ u = i ≫ v} (h : IsLimit (Fork.ofι i wc)) (x : X) (hx : u x = v x) :
    ∃ z : Z, i z = x := by
  obtain ⟨l, hl⟩ := Fork.IsLimit.lift' h (↾fun _ : PUnit.{t + 1} => x) (by ext _; exact hx)
  refine ⟨l PUnit.unit, ?_⟩
  simpa only [Fork.ι_ofι, ConcreteCategory.comp_apply, TypeCat.ofHom_apply]
    using ConcreteCategory.congr_hom hl PUnit.unit

/-- A point of a limit fan with prescribed coordinates. -/
noncomputable def pointOfFanIsLimit {ι : Type*} {X : ι → Type t} {Z : Type t}
    {π : ∀ j, Z ⟶ X j} (h : IsLimit (Fan.mk Z π)) (x : ∀ j, X j) : Z :=
  h.lift (Fan.mk PUnit.{t + 1} fun j => ↾fun _ => x j) PUnit.unit

/-- The coordinates of `pointOfFanIsLimit h x` are the prescribed ones. -/
@[simp]
lemma proj_pointOfFanIsLimit {ι : Type*} {X : ι → Type t} {Z : Type t}
    {π : ∀ j, Z ⟶ X j} (h : IsLimit (Fan.mk Z π)) (x : ∀ j, X j) (j : ι) :
    π j (pointOfFanIsLimit h x) = x j := by
  simpa only [ConcreteCategory.comp_apply, TypeCat.ofHom_apply, Fan.mk_π_app,
    pointOfFanIsLimit, Discrete.functor_obj_eq_as] using ConcreteCategory.congr_hom
      (h.fac (Fan.mk PUnit.{t + 1} fun j => ↾fun _ => x j) ⟨j⟩) PUnit.unit

end Points

/-! ### Points of a tuple sheaf through a limit-preserving functor -/

section TuplePoints

universe t

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (F : Sheaf K (Type w') ⥤ Type t) [PreservesFiniteLimits F] {A : Sheaf K (Type w')} {r : ℕ}

/-- The point of the image of a tuple sheaf with prescribed coordinates, for a functor to types
which preserves finite limits.  `tupleSheaf A r` is an `r`-fold product, so this is the
universal property of that product, transported. -/
noncomputable def tupleObjMk (x : Fin r → F.obj A) : F.obj (tupleSheaf A r) :=
  pointOfFanIsLimit (isLimitFanMkObjOfIsLimit F _ _ (tupleIsLimit A r)) x

/-- The `i`-th coordinate of `tupleObjMk F x` is `x i`. -/
@[simp]
lemma map_tupleProjection_tupleObjMk (x : Fin r → F.obj A) (i : Fin r) :
    F.map (tupleProjection A r i) (tupleObjMk F x) = x i :=
  proj_pointOfFanIsLimit (isLimitFanMkObjOfIsLimit F _ _ (tupleIsLimit A r)) x i

end TuplePoints

/-! ### Sections of a sheaf of types, as a limit-preserving functor -/

section SectionsFunctor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Sections over a fixed object preserve finite limits: they are a composite of
`sheafToPresheaf`, which creates limits, with an evaluation. -/
noncomputable instance preservesFiniteLimits_sectionsFunctor (X : Cᵒᵖ) :
    PreservesFiniteLimits (Sheaf.sectionsFunctor.{w} J X) := by
  delta Sheaf.sectionsFunctor
  infer_instance

variable {J}

/-- Equal morphisms of sheaves of types agree on every section. -/
private lemma hom_app_congr {A B : Sheaf J (Type w)} {α β : A ⟶ B} (h : α = β) (U : Cᵒᵖ)
    (x : A.obj.obj U) : α.hom.app U x = β.hom.app U x := by
  rw [h]

/-- A morphism of sheaves of types which has an inverse is injective on sections. -/
lemma hom_app_injective {A B : Sheaf J (Type w)} (α : A ⟶ B) (β : B ⟶ A) (h : α ≫ β = 𝟙 A)
    (U : Cᵒᵖ) {x y : A.obj.obj U} (hxy : α.hom.app U x = α.hom.app U y) : x = y := by
  have h1 : ∀ z : A.obj.obj U, β.hom.app U (α.hom.app U z) = z := fun z =>
    hom_app_congr h U z
  rw [← h1 x, hxy, h1 y]

end SectionsFunctor

/-! ### Transport along the inverse image of a morphism of topoi -/

section Sections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

/-- Sections over `V` of the inverse image of a sheaf of types, as a functor. -/
noncomputable def inverseImageSections (V : Cᵒᵖ) : Sheaf K (Type w') ⥤ Type w :=
  f.inverseImage ⋙ Sheaf.sectionsFunctor J V

/-- Sections over `V` of the inverse image preserve finite limits. -/
noncomputable instance (V : Cᵒᵖ) : PreservesFiniteLimits (inverseImageSections f V) := by
  let _ := f.preservesFiniteLimits
  delta inverseImageSections Sheaf.sectionsFunctor
  infer_instance

/-- The sections functor of the inverse image, on elements, is evaluation of the inverse image
of the morphism. -/
lemma inverseImageSections_map_apply {V : Cᵒᵖ} {A B : Sheaf K (Type w')} (h : A ⟶ B)
    (p : (inverseImageSections f V).obj A) :
    (inverseImageSections f V).map h p = (f.inverseImage.map h).hom.app V p :=
  rfl

end Sections

/-! ### Transport of the structure maps -/

section Transport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (R : Sheaf K RingCat.{w'}) (P : ToposPullback.PullbackModuleData J K f R)

/-- Transport of an `O`-linear combination of sections of `O` along the inverse image. -/
theorem map_ringCombination {T : Sheaf K (Type w')} {m : ℕ}
    (c t : Fin m → (T ⟶ Sheaf.ringSheaf R)) :
    f.inverseImage.map (ringCombination R c t) ≫ P.ringIso.inv =
      ringCombination P.ring (fun j => f.inverseImage.map (c j) ≫ P.ringIso.inv)
        (fun j => f.inverseImage.map (t j) ≫ P.ringIso.inv) := by
  induction m with
  | zero =>
      rw [ringCombination_zero, ringCombination_zero, Functor.map_comp, P.ringZero_map]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [← Category.assoc]
      congr 1
      apply Subsingleton.elim
  | succ m ih =>
      rw [ringCombination_succ, Functor.map_comp, P.ringAdd_map]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [← Category.assoc, ← Category.assoc, map_pair, prod.lift_map, Functor.map_comp,
        P.ringMul_map]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [← Category.assoc, ← Category.assoc, map_pair, prod.lift_map]
      rw [ih, ringCombination_succ]

/-- The inverse image of the zero section of a sheaf of modules is the zero section of its
inverse image. -/
theorem map_moduleZeroHom (M : SheafOfModules.{w'} R) {T : Sheaf K (Type w')} :
    f.inverseImage.map (terminal.from T ≫ Sheaf.moduleZeroHom R M) ≫ (P.moduleIso.app M).inv =
      terminal.from (f.inverseImage.obj T) ≫
        Sheaf.moduleZeroHom P.ring (P.moduleFunctor.obj M) := by
  rw [Functor.map_comp, P.moduleZero_map]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc]
  congr 1
  apply Subsingleton.elim

/-! ### The interface of the sheaf of presentation data -/

/-- **A sheaf of presentation data for `F` with `n` generators and `m` relations**: a sheaf of
sets whose points over an object `W` carry `n` sections of `F` and `m` tuples of `n` sections of
`O` forming presentation data in the sense of `IsPresentationData`. The subsheaf
`presDataSheaf` of `F^n × (O^n)^m` is one, `presentationDataSheaf`. -/
structure PresentationDataSheaf {R : Sheaf K RingCat.{w'}} (M : SheafOfModules.{w'} R)
    (n m : ℕ) where
  /-- The sheaf of sets of presentation data. -/
  sheaf : Sheaf K (Type w')
  /-- The `n` generating sections carried by a point of the data sheaf. -/
  gen : Fin n → (sheaf ⟶ moduleUnderlying M)
  /-- The `m` relation tuples carried by a point of the data sheaf. -/
  rel : Fin m → Fin n → (sheaf ⟶ Sheaf.ringSheaf R)
  /-- Every point of the data sheaf carries presentation data. -/
  isPresentationData (W : D) (p : sheaf.obj.obj (op W)) :
    IsPresentationData M (fun i => moduleSection M ((gen i).hom.app (op W) p))
      (fun j i => ringSection R ((rel j i).hom.app (op W) p))

variable (M : SheafOfModules.{w'} R) {n m : ℕ}

/-- The `i`-th generating section carried by a point of the inverse image of the data sheaf. -/
noncomputable def pullbackGen (G : PresentationDataSheaf M n m) {V : C}
    (p : (f.inverseImage.obj G.sheaf).obj.obj (op V)) (i : Fin n) :
    (P.moduleFunctor.obj M).val.obj (op V) :=
  moduleSection (P.moduleFunctor.obj M)
    ((f.inverseImage.map (G.gen i) ≫ (P.moduleIso.app M).inv).hom.app (op V) p)

/-- The `j`-th relation tuple carried by a point of the inverse image of the data sheaf. -/
noncomputable def pullbackRel (G : PresentationDataSheaf M n m) {V : C}
    (p : (f.inverseImage.obj G.sheaf).obj.obj (op V)) (j : Fin m) (i : Fin n) :
    P.ring.obj.obj (op V) :=
  ringSection P.ring ((f.inverseImage.map (G.rel j i) ≫ P.ringIso.inv).hom.app (op V) p)

/-! ### Condition (A): the relations are relations -/

/-- Condition (A), as an equality of morphisms out of the data sheaf. -/
theorem relation_hom (G : PresentationDataSheaf M n m) (j : Fin m) :
    linearCombination M (G.rel j) G.gen = terminal.from G.sheaf ≫ Sheaf.moduleZeroHom R M := by
  ext W x
  change combinationValue M (fun i => ringSection R ((G.rel j i).hom.app W x))
    (fun i => moduleSection M ((G.gen i).hom.app W x)) = (0 : M.val.obj W)
  exact (G.isPresentationData W.unop x).1 j

/-- Condition (A) for the transported data. -/
theorem combinationValue_pullbackRel (G : PresentationDataSheaf M n m) {V : C}
    (p : (f.inverseImage.obj G.sheaf).obj.obj (op V)) (j : Fin m) :
    combinationValue (P.moduleFunctor.obj M) (pullbackRel f R P M G p j)
      (pullbackGen f R P M G p) = 0 := by
  have h := map_linearCombination f R P M (G.rel j) G.gen
  rw [relation_hom R M G j, map_moduleZeroHom f R P M] at h
  exact (hom_app_congr h _ p).symm

/-! ### Condition (B): the generators span locally -/

/-- The map from the data sheaf to the sheaf of locally spanning `n`-tuples given by the
generating sections. -/
noncomputable def toGeneratingTupleSheaf (G : PresentationDataSheaf M n m) :
    G.sheaf ⟶ generatingTupleSheaf M n where
  hom :=
    { app := fun W => ↾fun p => ⟨fun i => moduleSection M ((G.gen i).hom.app W p),
        (G.isPresentationData W.unop p).2.1⟩
      naturality := by
        intro W X g
        ext p
        exact Subtype.ext (funext fun i =>
          ConcreteCategory.congr_hom ((G.gen i).hom.naturality g) p) }

/-- The `i`-th coordinate of `toGeneratingTupleSheaf R M G` is the generating section
`G.gen i`. -/
@[simp]
lemma toGeneratingTupleSheaf_generatorProjection (G : PresentationDataSheaf M n m) (i : Fin n) :
    toGeneratingTupleSheaf R M G ≫ generatorProjection M n i = G.gen i := rfl

/-- Condition (B) for the transported data. -/
theorem locallySpans_pullbackGen (G : PresentationDataSheaf M n m) {V : C}
    (p : (f.inverseImage.obj G.sheaf).obj.obj (op V)) :
    LocallySpans (P.moduleFunctor.obj M) (pullbackGen f R P M G p) := by
  have h := pullback_generatingTuple_locallySpans f R P M n (U := V)
    ((f.inverseImage.map (toGeneratingTupleSheaf R M G)).hom.app (op V) p)
  have key : (fun i => (f.inverseImage.map (generatorProjection M n i) ≫
      (P.moduleIso.app M).inv).hom.app (op V)
        ((f.inverseImage.map (toGeneratingTupleSheaf R M G)).hom.app (op V) p)) =
      pullbackGen f R P M G p := by
    funext i
    have h2 : f.inverseImage.map (toGeneratingTupleSheaf R M G) ≫
        f.inverseImage.map (generatorProjection M n i) ≫ (P.moduleIso.app M).inv =
        f.inverseImage.map (G.gen i) ≫ (P.moduleIso.app M).inv := by
      rw [← Functor.map_comp_assoc, toGeneratingTupleSheaf_generatorProjection]
    exact hom_app_congr h2 _ p
  rwa [← key]

/-! ### Condition (C): the relations are locally spanned -/

variable (G : PresentationDataSheaf M n m)

/-- The sheaf of `k`-tuples of sections of `O` together with a point of the data sheaf. -/
noncomputable abbrev coeffSheaf (k : ℕ) : Sheaf K (Type w') :=
  tupleSheaf (Sheaf.ringSheaf R) k ⨯ G.sheaf

/-- The combination of the generating sections carried by a point of the data sheaf with a
tuple of sections of `O`. -/
noncomputable def combinationLeg : coeffSheaf R M G n ⟶ moduleUnderlying M :=
  linearCombination M (fun i => prod.fst ≫ tupleProjection (Sheaf.ringSheaf R) n i)
    (fun i => prod.snd ≫ G.gen i)

/-- The zero section of `F`, as a map out of the sheaf of tuples of sections of `O`. -/
noncomputable def zeroLeg : coeffSheaf R M G n ⟶ moduleUnderlying M :=
  terminal.from _ ≫ Sheaf.moduleZeroHom R M

/-- **The sheaf of relations among the generating sections**, as the equalizer of the two legs. -/
noncomputable def syzygySheaf : Sheaf K (Type w') :=
  equalizer (combinationLeg R M G) (zeroLeg R M G)

/-- The inclusion of the sheaf of relations into the sheaf of tuples of sections of `O`. -/
noncomputable def syzygyι : syzygySheaf R M G ⟶ coeffSheaf R M G n :=
  equalizer.ι (combinationLeg R M G) (zeroLeg R M G)

/-- The two legs agree on the sheaf of relations. -/
lemma syzygyι_condition :
    syzygyι R M G ≫ combinationLeg R M G = syzygyι R M G ≫ zeroLeg R M G :=
  equalizer.condition _ _

/-- The fork exhibiting the sheaf of relations as an equalizer. -/
noncomputable def syzygyForkIsLimit :
    IsLimit (Fork.ofι (syzygyι R M G) (syzygyι_condition R M G)) :=
  equalizerIsEqualizer _ _

/-- Two points of the sheaf of tuples of sections of `O` agree as soon as all their
coordinates and their points of the data sheaf agree. -/
lemma coeff_section_ext {k : ℕ} {U : Dᵒᵖ} {x y : (coeffSheaf R M G k).obj.obj U}
    (h₁ : ∀ i, (prod.fst ≫ tupleProjection (Sheaf.ringSheaf R) k i).hom.app U x =
      (prod.fst ≫ tupleProjection (Sheaf.ringSheaf R) k i).hom.app U y)
    (h₂ : (prod.snd : coeffSheaf R M G k ⟶ G.sheaf).hom.app U x =
      (prod.snd : coeffSheaf R M G k ⟶ G.sheaf).hom.app U y) : x = y :=
  prod_section_ext (funext h₁) h₂

/-- The matrix action: a tuple `c` of `m` sections of `O` is sent to the tuple
`(∑ j, c j * t j i)` of `n` sections of `O`, and the point of the data sheaf is kept. -/
noncomputable def relationMapAmb : coeffSheaf R M G m ⟶ coeffSheaf R M G n :=
  prod.lift (tupleLift (fun i => ringCombination R
    (fun j => prod.fst ≫ tupleProjection (Sheaf.ringSheaf R) m j)
    (fun j => prod.snd ≫ G.rel j i))) prod.snd

/-- The `i`-th coordinate of the matrix action is `∑ j, c j * t j i`. -/
lemma relationMapAmb_comp_coeff (i : Fin n) :
    relationMapAmb R M G ≫ prod.fst ≫ tupleProjection (Sheaf.ringSheaf R) n i =
      ringCombination R (fun j => prod.fst ≫ tupleProjection (Sheaf.ringSheaf R) m j)
        (fun j => prod.snd ≫ G.rel j i) := by
  rw [relationMapAmb, ← Category.assoc, prod.lift_fst, tupleLift_projection]

/-- The matrix action keeps the point of the data sheaf. -/
lemma relationMapAmb_comp_snd :
    relationMapAmb R M G ≫ (prod.snd : coeffSheaf R M G n ⟶ G.sheaf) =
      (prod.snd : coeffSheaf R M G m ⟶ G.sheaf) := by
  rw [relationMapAmb, prod.lift_snd]

/-- The matrix action does not change the generating sections carried by a point. -/
lemma relationMapAmb_comp_gen (i : Fin n) :
    relationMapAmb R M G ≫ prod.snd ≫ G.gen i =
      (prod.snd : coeffSheaf R M G m ⟶ G.sheaf) ≫ G.gen i := by
  rw [← Category.assoc, relationMapAmb_comp_snd]

/-- The zero leg after the matrix action is the zero section. -/
lemma relationMapAmb_comp_zeroLeg :
    relationMapAmb R M G ≫ zeroLeg R M G =
      terminal.from (coeffSheaf R M G m) ≫ Sheaf.moduleZeroHom R M := by
  rw [zeroLeg, ← Category.assoc, terminal.comp_from]

/-- The matrix action lands in the sheaf of relations: this is condition (A). -/
lemma relationMapAmb_condition :
    relationMapAmb R M G ≫ combinationLeg R M G =
      relationMapAmb R M G ≫ zeroLeg R M G := by
  rw [relationMapAmb_comp_zeroLeg, combinationLeg, linearCombination_precomp]
  simp only [relationMapAmb_comp_coeff, relationMapAmb_comp_gen]
  refine linearCombination_eq_zero M _ _ fun U x => ?_
  simp only [ringSection_ringCombination_hom_app]
  exact combinationValue_ringCombinationValue _ _ _
    ((G.isPresentationData U.unop ((prod.snd : coeffSheaf R M G m ⟶ G.sheaf).hom.app U x)).1)

/-- **The matrix action, as a map to the sheaf of relations.**  Condition (C) says exactly that
this map is locally surjective. -/
noncomputable def relationMap : coeffSheaf R M G m ⟶ syzygySheaf R M G :=
  equalizer.lift (relationMapAmb R M G) (relationMapAmb_condition R M G)

/-- The map to the sheaf of relations, followed by its inclusion, is the matrix action. -/
@[simp]
lemma relationMap_syzygyι : relationMap R M G ≫ syzygyι R M G = relationMapAmb R M G :=
  equalizer.lift_ι _ _

/-- The tuple of sections of `O` carried by a point of the sheaf of relations. -/
noncomputable def syzygyCoeff {U : Dᵒᵖ} (y : (syzygySheaf R M G).obj.obj U) (i : Fin n) :
    R.obj.obj U :=
  ringSection R
    ((syzygyι R M G ≫ prod.fst ≫ tupleProjection (Sheaf.ringSheaf R) n i).hom.app U y)

/-- The point of the data sheaf carried by a point of the sheaf of relations. -/
noncomputable def syzygyData {U : Dᵒᵖ} (y : (syzygySheaf R M G).obj.obj U) :
    G.sheaf.obj.obj U :=
  (syzygyι R M G ≫ prod.snd).hom.app U y

/-- The coefficients of a point of the sheaf of relations are compatible with restriction. -/
lemma syzygyCoeff_map {U V : Dᵒᵖ} (g : U ⟶ V) (y : (syzygySheaf R M G).obj.obj U) (i : Fin n) :
    syzygyCoeff R M G ((syzygySheaf R M G).obj.map g y) i =
      R.obj.map g (syzygyCoeff R M G y i) :=
  NatTrans.naturality_apply
    (syzygyι R M G ≫ prod.fst ≫ tupleProjection (Sheaf.ringSheaf R) n i).hom g y

/-- The point of the data sheaf carried by a point of the sheaf of relations is compatible with
restriction. -/
lemma syzygyData_map {U V : Dᵒᵖ} (g : U ⟶ V) (y : (syzygySheaf R M G).obj.obj U) :
    syzygyData R M G ((syzygySheaf R M G).obj.map g y) =
      G.sheaf.obj.map g (syzygyData R M G y) :=
  NatTrans.naturality_apply (syzygyι R M G ≫ prod.snd).hom g y

/-- The tuple of sections of `O` carried by a point of the sheaf of relations really is a
relation among the generating sections carried by its point of the data sheaf. -/
lemma combinationValue_syzygyCoeff {U : Dᵒᵖ} (y : (syzygySheaf R M G).obj.obj U) :
    combinationValue M (syzygyCoeff R M G y)
      (fun i => moduleSection M ((G.gen i).hom.app U (syzygyData R M G y))) = 0 :=
  hom_app_congr (syzygyι_condition R M G) U y

/-- The point of the sheaf of tuples of sections of `O` with given coordinates and given point
of the data sheaf. -/
noncomputable def coeffSectionMk {k : ℕ} {U : Dᵒᵖ} (c : Fin k → R.obj.obj U)
    (q : G.sheaf.obj.obj U) : (coeffSheaf R M G k).obj.obj U :=
  (prodSectionEquiv (tupleSheaf (Sheaf.ringSheaf R) k) G.sheaf U).symm (tupleMk c, q)

/-- The `j`-th coordinate of `coeffSectionMk R M G c q` is `c j`. -/
@[simp]
lemma coeffSectionMk_coeff {k : ℕ} {U : Dᵒᵖ} (c : Fin k → R.obj.obj U)
    (q : G.sheaf.obj.obj U) (j : Fin k) :
    ringSection R ((prod.fst ≫ tupleProjection (Sheaf.ringSheaf R) k j).hom.app U
      (coeffSectionMk R M G c q)) = c j :=
  congrArg (fun s : (tupleSheaf (Sheaf.ringSheaf R) k).obj.obj U => s j)
    (prodSectionEquiv_symm_fst (tupleSheaf (Sheaf.ringSheaf R) k) G.sheaf U (tupleMk c) q)

/-- The point of the data sheaf of `coeffSectionMk R M G c q` is `q`. -/
@[simp]
lemma coeffSectionMk_data {k : ℕ} {U : Dᵒᵖ} (c : Fin k → R.obj.obj U)
    (q : G.sheaf.obj.obj U) :
    (prod.snd : coeffSheaf R M G k ⟶ G.sheaf).hom.app U (coeffSectionMk R M G c q) = q :=
  prodSectionEquiv_symm_snd (tupleSheaf (Sheaf.ringSheaf R) k) G.sheaf U (tupleMk c) q

/-- **Condition (C) gives local surjectivity of the matrix action onto the sheaf of
relations.** -/
theorem relationMap_locallySurjective : Sheaf.IsLocallySurjective (relationMap R M G) := by
  constructor
  intro U y
  have hC := relationSpanSieve_mem_of_locallySpansKernel
    (G.isPresentationData U (syzygyData R M G y)).2.2 (combinationValue_syzygyCoeff R M G y)
  apply K.superset_covering _ hC
  rintro V g ⟨c, hc⟩
  refine ⟨coeffSectionMk R M G c (G.sheaf.obj.map g.op (syzygyData R M G y)), ?_⟩
  refine eq_of_forkIsLimit (isLimitForkMapOfIsLimit (Sheaf.sectionsFunctor K (op V))
    (syzygyι_condition R M G) (syzygyForkIsLimit R M G)) ?_
  rw [Sheaf.sectionsFunctor_map_apply, Sheaf.sectionsFunctor_map_apply]
  have hlhs : (syzygyι R M G).hom.app (op V) ((relationMap R M G).hom.app (op V)
        (coeffSectionMk R M G c (G.sheaf.obj.map g.op (syzygyData R M G y)))) =
      (relationMapAmb R M G).hom.app (op V)
        (coeffSectionMk R M G c (G.sheaf.obj.map g.op (syzygyData R M G y))) :=
    hom_app_congr (relationMap_syzygyι R M G) _ _
  rw [hlhs]
  refine coeff_section_ext R M G (fun i => ?_) ?_
  · have hL : (prod.fst ≫ tupleProjection (Sheaf.ringSheaf R) n i).hom.app (op V)
        ((relationMapAmb R M G).hom.app (op V)
          (coeffSectionMk R M G c (G.sheaf.obj.map g.op (syzygyData R M G y)))) =
        ∑ j, ringSection R ((prod.fst ≫ tupleProjection (Sheaf.ringSheaf R) m j).hom.app (op V)
            (coeffSectionMk R M G c (G.sheaf.obj.map g.op (syzygyData R M G y)))) *
          ringSection R ((prod.snd ≫ G.rel j i).hom.app (op V)
            (coeffSectionMk R M G c (G.sheaf.obj.map g.op (syzygyData R M G y)))) :=
      hom_app_congr (relationMapAmb_comp_coeff R M G i) _ _
    have hR : (prod.fst ≫ tupleProjection (Sheaf.ringSheaf R) n i).hom.app (op V)
        ((syzygyι R M G).hom.app (op V) ((syzygySheaf R M G).obj.map g.op y)) =
        R.obj.map g.op (syzygyCoeff R M G y i) := syzygyCoeff_map R M G g.op y i
    have hrel : ∀ j, ringSection R ((prod.snd ≫ G.rel j i).hom.app (op V)
          (coeffSectionMk R M G c (G.sheaf.obj.map g.op (syzygyData R M G y)))) =
        R.obj.map g.op (ringSection R ((G.rel j i).hom.app (op U) (syzygyData R M G y))) := by
      intro j
      refine Eq.trans (congrArg (fun q : G.sheaf.obj.obj (op V) =>
        ringSection R ((G.rel j i).hom.app (op V) q))
          (coeffSectionMk_data R M G c (G.sheaf.obj.map g.op (syzygyData R M G y)))) ?_
      exact NatTrans.naturality_apply (G.rel j i).hom g.op (syzygyData R M G y)
    rw [hL, hR]
    simp only [coeffSectionMk_coeff, hrel]
    exact hc i
  · have hS : (prod.snd : coeffSheaf R M G n ⟶ G.sheaf).hom.app (op V)
        ((relationMapAmb R M G).hom.app (op V)
          (coeffSectionMk R M G c (G.sheaf.obj.map g.op (syzygyData R M G y)))) =
        (prod.snd : coeffSheaf R M G m ⟶ G.sheaf).hom.app (op V)
          (coeffSectionMk R M G c (G.sheaf.obj.map g.op (syzygyData R M G y))) :=
      hom_app_congr (relationMapAmb_comp_snd R M G) _ _
    rw [hS, coeffSectionMk_data]
    exact (syzygyData_map R M G g.op y).symm

/-- **Condition (C) for the transported data.** -/
theorem locallySpansKernel_pullback {V : C}
    (p : (f.inverseImage.obj G.sheaf).obj.obj (op V)) :
    LocallySpansKernel (P.moduleFunctor.obj M) (pullbackGen f R P M G p)
      (pullbackRel f R P M G p) := by
  intro V₁ g a ha
  let Fv := inverseImageSections f (op V₁)
  have comp : ∀ {A B B' : Sheaf K (Type w')} {X : Sheaf J (Type w)} {W : Cᵒᵖ} (a : A ⟶ B')
      (b : B' ⟶ B) (θ : f.inverseImage.obj B ⟶ X) (z : (f.inverseImage.obj A).obj.obj W),
      (f.inverseImage.map (a ≫ b) ≫ θ).hom.app W z =
        (f.inverseImage.map b ≫ θ).hom.app W ((f.inverseImage.map a).hom.app W z) := by
    intros
    rw [Functor.map_comp]
    rfl
  obtain ⟨y, hcoeff, hy2⟩ :
      ∃ y : (f.inverseImage.obj (coeffSheaf R M G n)).obj.obj (op V₁),
      (∀ i, ringSection P.ring ((f.inverseImage.map
        (prod.fst ≫ tupleProjection (Sheaf.ringSheaf R) n i) ≫
          P.ringIso.inv).hom.app (op V₁) y) = a i) ∧
      Fv.map (prod.snd : coeffSheaf R M G n ⟶ G.sheaf) y =
        (f.inverseImage.obj G.sheaf).obj.map g.op p := by
    refine ⟨Functor.prodObjMk (P := Fv) (A := tupleSheaf (Sheaf.ringSheaf R) n) (B := G.sheaf)
      (tupleObjMk Fv (fun i => (P.ringIso.hom).hom.app (op V₁) (a i)))
      ((f.inverseImage.obj G.sheaf).obj.map g.op p), fun i => ?_,
      Functor.map_snd_prodObjMk _ _⟩
    have h1 : Fv.map (prod.fst ≫ tupleProjection (Sheaf.ringSheaf R) n i)
        (Functor.prodObjMk (P := Fv) (A := tupleSheaf (Sheaf.ringSheaf R) n) (B := G.sheaf)
          (tupleObjMk Fv (fun i => (P.ringIso.hom).hom.app (op V₁) (a i)))
          ((f.inverseImage.obj G.sheaf).obj.map g.op p)) =
        (P.ringIso.hom).hom.app (op V₁) (a i) := by
      refine Eq.trans (Fv.map_comp_apply _ _ _) (Eq.trans (congrArg
        (Fv.map (tupleProjection (Sheaf.ringSheaf R) n i))
        (Functor.map_fst_prodObjMk (P := Fv) _ _))
        (map_tupleProjection_tupleObjMk Fv _ i))
    refine Eq.trans (congrArg (fun q : Fv.obj (Sheaf.ringSheaf R) =>
      ringSection P.ring (P.ringIso.inv.hom.app (op V₁) q)) h1) ?_
    exact hom_app_congr P.ringIso.hom_inv_id _ (a i)
  replace hy2 : (f.inverseImage.map (prod.snd : coeffSheaf R M G n ⟶ G.sheaf)).hom.app (op V₁) y =
      (f.inverseImage.obj G.sheaf).obj.map g.op p := hy2
  have hgen : ∀ i, moduleSection (P.moduleFunctor.obj M) ((f.inverseImage.map
        (prod.snd ≫ G.gen i) ≫ (P.moduleIso.app M).inv).hom.app (op V₁) y) =
      restr (P.moduleFunctor.obj M) g.op (pullbackGen f R P M G p i) := by
    intro i
    rw [comp, hy2]
    exact NatTrans.naturality_apply
      (f.inverseImage.map (G.gen i) ≫ (P.moduleIso.app M).inv).hom g.op p
  have hlegs : Fv.map (combinationLeg R M G) y = Fv.map (zeroLeg R M G) y := by
    refine hom_app_injective (P.moduleIso.app M).inv (P.moduleIso.app M).hom
      (P.moduleIso.app M).inv_hom_id (op V₁) ?_
    have e1 : (P.moduleIso.app M).inv.hom.app (op V₁) (Fv.map (combinationLeg R M G) y) =
        (f.inverseImage.map (combinationLeg R M G) ≫
          (P.moduleIso.app M).inv).hom.app (op V₁) y := rfl
    have e2 : (P.moduleIso.app M).inv.hom.app (op V₁) (Fv.map (zeroLeg R M G) y) =
        (f.inverseImage.map (zeroLeg R M G) ≫
          (P.moduleIso.app M).inv).hom.app (op V₁) y := rfl
    rw [e1, e2, combinationLeg, zeroLeg, map_linearCombination f R P M,
      map_moduleZeroHom f R P M]
    refine Eq.trans (linearCombination_hom_app (P.moduleFunctor.obj M) _ _ (op V₁) y) ?_
    simp only [hcoeff, hgen]
    exact ha
  obtain ⟨z, hz⟩ : ∃ z : (f.inverseImage.obj (syzygySheaf R M G)).obj.obj (op V₁),
      (f.inverseImage.map (syzygyι R M G)).hom.app (op V₁) z = y :=
    exists_point_of_forkIsLimit
      (isLimitForkMapOfIsLimit Fv (syzygyι_condition R M G) (syzygyForkIsLimit R M G)) y hlegs
  have : Sheaf.IsLocallySurjective (relationMap R M G) := relationMap_locallySurjective R M G
  have hLS : Sheaf.IsLocallySurjective (f.inverseImage.map (relationMap R M G)) :=
    map_locallySurjective_of_adjunction f.adj _
  apply J.superset_covering _
    (Presheaf.imageSieve_mem J (f.inverseImage.map (relationMap R M G)).hom z)
  rintro V₂ g₂ ⟨z₂, hz₂⟩
  have key : ∀ {A : Sheaf K (Type w')} {B : Sheaf J (Type w)} (h : syzygySheaf R M G ⟶ A)
      (θ : f.inverseImage.obj A ⟶ B),
      (f.inverseImage.map (relationMap R M G ≫ h) ≫ θ).hom.app (op V₂) z₂ =
        B.obj.map g₂.op ((f.inverseImage.map h ≫ θ).hom.app (op V₁) z) := by
    intro A B h θ
    rw [comp, hz₂]
    exact NatTrans.naturality_apply (f.inverseImage.map h ≫ θ).hom g₂.op z
  have hdata : (f.inverseImage.map (prod.snd : coeffSheaf R M G m ⟶ G.sheaf)).hom.app (op V₂) z₂ =
      (f.inverseImage.obj G.sheaf).obj.map g₂.op
        ((f.inverseImage.obj G.sheaf).obj.map g.op p) := by
    have h1 := key (syzygyι R M G ≫ prod.snd) (𝟙 _)
    rw [← Category.assoc, relationMap_syzygyι, relationMapAmb_comp_snd] at h1
    rw [comp, hz] at h1
    simpa only [Category.comp_id, hy2] using h1
  refine ⟨fun j => ringSection P.ring ((f.inverseImage.map
    (prod.fst ≫ tupleProjection (Sheaf.ringSheaf R) m j) ≫
      P.ringIso.inv).hom.app (op V₂) z₂), fun i => ?_⟩
  have hrel : ∀ j, ringSection P.ring ((f.inverseImage.map (prod.snd ≫ G.rel j i) ≫
        P.ringIso.inv).hom.app (op V₂) z₂) =
      P.ring.obj.map g₂.op (P.ring.obj.map g.op (pullbackRel f R P M G p j i)) := by
    intro j
    rw [comp, hdata, NatTrans.naturality_apply
      (f.inverseImage.map (G.rel j i) ≫ P.ringIso.inv).hom g₂.op]
    exact congrArg (P.ring.obj.map g₂.op) (NatTrans.naturality_apply
      (f.inverseImage.map (G.rel j i) ≫ P.ringIso.inv).hom g.op p)
  have hmain := key (syzygyι R M G ≫ prod.fst ≫
    tupleProjection (Sheaf.ringSheaf R) n i) P.ringIso.inv
  rw [← Category.assoc, relationMap_syzygyι, relationMapAmb_comp_coeff,
    map_ringCombination f R P, ringCombination_hom_app, ringCombinationValue] at hmain
  have hright : (f.inverseImage.map (syzygyι R M G ≫ prod.fst ≫
      tupleProjection (Sheaf.ringSheaf R) n i) ≫ P.ringIso.inv).hom.app (op V₁) z = a i := by
    rw [comp, hz]
    exact hcoeff i
  rw [hright] at hmain
  simp only [hrel] at hmain
  exact hmain

/-! ### The transport -/

/-- **Presentation data transports along the inverse image of a morphism of topoi.**  A point
of `f⁻¹` of a sheaf of presentation data for `F`, over an object `V` of the source site, carries
presentation data for `f⁻¹F` over `V`, with the *same* numbers of generators and relations. -/
theorem isPresentationData_pullback {V : C}
    (p : (f.inverseImage.obj G.sheaf).obj.obj (op V)) :
    IsPresentationData (P.moduleFunctor.obj M) (pullbackGen f R P M G p)
      (pullbackRel f R P M G p) :=
  ⟨fun j => combinationValue_pullbackRel f R P M G p j,
    locallySpans_pullbackGen f R P M G p, locallySpansKernel_pullback f R P M G p⟩

/-! ### The sheaf of presentations as a sheaf of presentation data -/

/-- The relation tuples of a presentation, as morphisms out of the sheaf of presentations. -/
noncomputable def presDataRelations (M : SheafOfModules.{w'} R) (n m : ℕ) (j : Fin m)
    (i : Fin n) : presDataSheaf M n m ⟶ Sheaf.ringSheaf R where
  hom :=
    { app := fun U => ↾fun p => dataRelations M p.val j i
      naturality := by
        intro U X g
        ext p
        exact congrFun (congrFun (dataRelations_map M g p.val) j) i }

/-- **The sheaf of presentations is a sheaf of presentation data.** -/
noncomputable def presentationDataSheaf (M : SheafOfModules.{w'} R) (n m : ℕ) :
    PresentationDataSheaf M n m where
  sheaf := presDataSheaf M n m
  gen i := presDataGenerators M n m ≫ generatorProjection M n i
  rel j i := presDataRelations R M n m j i
  isPresentationData _ p := p.property

/-- The underlying sheaf of `presentationDataSheaf R M n m` is the sheaf of presentations. -/
@[simp]
lemma presentationDataSheaf_sheaf (M : SheafOfModules.{w'} R) (n m : ℕ) :
    (presentationDataSheaf R M n m).sheaf = presDataSheaf M n m := rfl

/-- **Stacks 03DO (7), the transport step.**  A point of the inverse image of the sheaf of
presentations of `F` with `n` generators and `m` relations, over an object `V` of the source
site, is a presentation of `f⁻¹F` with `n` generators and `m` relations over `V`. -/
noncomputable def pullbackPresData (M : SheafOfModules.{w'} R) (n m : ℕ) {V : C}
    (p : (f.inverseImage.obj (presDataSheaf M n m)).obj.obj (op V)) :
    (presDataSheaf (P.moduleFunctor.obj M) n m).obj.obj (op V) :=
  presDataMk (P.moduleFunctor.obj M)
    (isPresentationData_pullback f R P M (presentationDataSheaf R M n m) p)

end Transport

end Stacks.Sheaves.PresentationTransport

end
