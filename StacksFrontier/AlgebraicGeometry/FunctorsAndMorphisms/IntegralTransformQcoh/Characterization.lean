module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ExactKernelOfFunctor
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.CharacterizingProperties
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk

/-!
# The functors on quasi-coherent modules which are integral transforms

Let `R` be a ring and let `X` and `Y` be schemes over `R` with `X` quasi-compact with affine
diagonal.  This file proves [Stacks, Tag 0GPB]: the functors
`F : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` isomorphic to an integral transform
`F_K = pr_{2,*}(pr_1^*(−) ⊗ K)` are exactly those which

1. are `R`-linear and commute with arbitrary direct sums,
2. are right exact after direct image along the inclusion of every affine open of `X`, and
3. carry every short exact sequence `0 ⟶ F ⟶ G ⟶ H ⟶ 0` whose sequences of stalks are split
   short exact sequences of `𝒪_{X,x}`-modules to an exact sequence `0 ⟶ F(F) ⟶ F(G) ⟶ F(H)`.

## Main definitions

* `AlgebraicGeometry.PreservesFiniteColimitsAfterAffineOpens`: property (2).
* `AlgebraicGeometry.IsStalkwiseSplitLeftExact`: property (3).

## Main results

* `AlgebraicGeometry.nonempty_iso_quasicoherentIntegralTransform_iff`: **Tag 0GPB.**
* `AlgebraicGeometry.isStalkwiseSplitLeftExact_quasicoherentIntegralTransform`: an integral
  transform has property (3).
* `AlgebraicGeometry.exists_iso_quasicoherentIntegralTransform_of_isStalkwiseSplitLeftExact`: a
  functor with the three properties is an integral transform.
* `AlgebraicGeometry.isLimitMapConeCechMultifork`: a functor with property (3) carries the Čech
  multifork of a finite open cover to a limit.

## Implementation notes

The source proves the tag in one sentence ("these assumptions are enough to construct a
transformation `t : F ⟶ F_K` as in Lemma 0GPA and to show that it is an isomorphism"), and
this is how it is formalized.  The construction of the kernel and of `t` in Tag 0GPA only ever
evaluates `F` on direct images from affine opens, so it runs under property (2)
(`AlgebraicGeometry.affineOpenRightExactLinearCoproductFunctor`).  The transformation `t` is an
isomorphism on direct images from affine opens, and `F` carries the Čech multifork
`G ⟶ ⊕ (U_i)_*(G|_{U_i}) ⇉ ⊕ (U_i ∩ U_j)_*(G|_{U_i ∩ U_j})` of a finite affine open cover to a
limit: the Čech complex in degrees `0` and `1` breaks into the short exact sequences
`0 ⟶ G ⟶ ⊕ (U_i)_*(G|_{U_i}) ⟶ Q ⟶ 0` and `0 ⟶ Q ⟶ ⊕ (U_i ∩ U_j)_*(G|_{U_i ∩ U_j})`, both split
on the stalks at the points of `U_k` by the usual contracting homotopy of the Čech complex of a
cover with `U_k` as a member, and property (3) applies to both.

For an integral transform, property (3) holds because the integrand `pr_1^*(−) ⊗ K` keeps a
stalkwise split monomorphism injective (on the stalk at `z` it is `K_z ⊗_{𝒪_{X, pr_1 z}} (−)`),
and is right exact, while direct image along `pr_2` is left exact.

The stalks in property (3) are those of `AlgebraicGeometry.SheafOfModules.stalkFunctor`: the
stalk `M_x` of a module as a module over the stalk `𝒪_{X,x}` of the structure sheaf, and the
splitting asked for is a splitting of `𝒪_{X,x}`-modules.

## References

* [Stacks Project, Tag 0GPB](https://stacks.math.columbia.edu/tag/0GPB)
* [Stacks Project, Tag 0GPA](https://stacks.math.columbia.edu/tag/0GPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local instance] Abelian.hasFiniteBiproducts

/-! ### Property (3) -/

section Property

variable {X : Scheme.{u}} {D : Type*} [Category D] [Preadditive D]

/-- **Property (3) of Tag 0GPB.**  A functor `F` on the quasi-coherent modules of `X` carries
every short exact sequence `0 ⟶ F ⟶ G ⟶ H ⟶ 0` whose stalk `F_x ⟶ G_x` is a split injection of
`𝒪_{X,x}`-modules at every point `x` (so that the sequence of stalks is split short exact) to an
exact sequence `0 ⟶ F(F) ⟶ F(G) ⟶ F(H)`. -/
def IsStalkwiseSplitLeftExact (F : Scheme.QuasicoherentModules X ⥤ D)
    [F.PreservesZeroMorphisms] : Prop :=
  ∀ S : ShortComplex (Scheme.QuasicoherentModules X), S.ShortExact →
    (∀ x : X, IsSplitMono
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map S.f.hom)) →
    Mono (F.map S.f) ∧ (S.map F).Exact

/-- Property (3) of Tag 0GPB is invariant under isomorphism of functors. -/
theorem IsStalkwiseSplitLeftExact.of_iso {F G : Scheme.QuasicoherentModules X ⥤ D}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (e : F ≅ G)
    (h : IsStalkwiseSplitLeftExact F) : IsStalkwiseSplitLeftExact G := fun S hS hs =>
  ((ShortComplex.exact_and_mono_f_iff_of_iso (S.mapNatIso e)).mp
    ⟨(h S hS hs).2, (h S hS hs).1⟩).symm

end Property

/-! ### Stalks and restriction to an open -/

section Stalk

variable {Z : Scheme.{u}}

/-- **A morphism of modules which is invertible over an open is invertible on the stalks at the
points of that open.** -/
theorem isIso_stalkFunctor_map_of_isIso_restrictFunctor_map {M N : Z.Modules} (φ : M ⟶ N)
    (U : Z.Opens) [IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ)] (x : U) :
    IsIso ((AlgebraicGeometry.SheafOfModules.stalkFunctor Z.ringCatSheaf (U.ι x)).map φ) := by
  have h0 : IsIso ((Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.toPresheaf U ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ) := by
    simp only [Functor.comp_map]
    infer_instance
  have h := (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso U.ι x) φ).mp h0
  have hb := (ConcreteCategory.isIso_iff_bijective _).mp h
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hb

end Stalk

/-! ### An additive functor and the components of a biproduct -/

section BiproductExt

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  (Φ : C ⥤ D) [Φ.Additive] {J : Type*} [Fintype J] [DecidableEq J] (f : J → C) [HasBiproduct f]

omit [Fintype J] [DecidableEq J] in
/-- Morphisms into the image of a finite biproduct under an additive functor are determined by
their composites with the images of the projections. -/
theorem hom_ext_map_biproduct [Finite J] {A : D} {a b : A ⟶ Φ.obj (⨁ f)}
    (h : ∀ j, a ≫ Φ.map (biproduct.π f j) = b ≫ Φ.map (biproduct.π f j)) : a = b := by
  have := Fintype.ofFinite J
  have ht : ∑ j, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f) :=
    IsBilimit.total (biproduct.isBilimit f)
  have e : ∀ c : A ⟶ Φ.obj (⨁ f),
      c = ∑ j, (c ≫ Φ.map (biproduct.π f j)) ≫ Φ.map (biproduct.ι f j) := fun c => by
    conv_lhs => rw [← Category.comp_id c, ← Φ.map_id, ← ht, Φ.map_sum, Preadditive.comp_sum]
    simp only [Φ.map_comp, Category.assoc]
  rw [e a, e b]
  simp only [h]

omit [DecidableEq J] in
/-- The image of a sum of maps into the summands of a biproduct, read on one component. -/
theorem sum_comp_map_ι_comp_map_π {A : D} (g : ∀ j, A ⟶ Φ.obj (f j)) (l : J) :
    (∑ j, g j ≫ Φ.map (biproduct.ι f j)) ≫ Φ.map (biproduct.π f l) = g l := by
  rw [Preadditive.sum_comp, Finset.sum_eq_single l]
  · rw [Category.assoc, ← Φ.map_comp, biproduct.ι_π_self, Φ.map_id, Category.comp_id]
  · intro j _ hj
    rw [Category.assoc, ← Φ.map_comp, biproduct.ι_π_ne _ hj, Φ.map_zero, Limits.comp_zero]
  · intro h
    exact absurd (Finset.mem_univ l) h

end BiproductExt

/-! ### An augmented cosimplicial diagram in degrees `0` and `1` with a contraction -/

section AbstractCech

variable {C : Type*} [Category C] [Preadditive C] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {G : C} (A : ι → C) (B : ι × ι → C) [HasBiproduct A] [HasBiproduct B]
  (η : ∀ i, G ⟶ A i) (fst : ∀ p : ι × ι, A p.1 ⟶ B p) (snd : ∀ p : ι × ι, A p.2 ⟶ B p)

/-- The augmentation `G ⟶ ⊕_i A_i`. -/
abbrev augMap : G ⟶ ⨁ A := biproduct.lift η

/-- The differential `⊕_i A_i ⟶ ⊕_{i,j} B_{ij}`, `(a_i) ↦ (fst a_i - snd a_j)`. -/
abbrev diffMap : (⨁ A) ⟶ ⨁ B :=
  biproduct.lift fun p => biproduct.π A p.1 ≫ fst p - biproduct.π A p.2 ≫ snd p

omit [Fintype ι] [DecidableEq ι] in
/-- The `(i, j)`-component of the differential is `fst_{ij} ∘ π_i - snd_{ij} ∘ π_j`. -/
theorem diffMap_π (p : ι × ι) :
    diffMap A B fst snd ≫ biproduct.π B p = biproduct.π A p.1 ≫ fst p - biproduct.π A p.2 ≫ snd p :=
  biproduct.lift_π _ _

omit [Fintype ι] [DecidableEq ι] in
/-- The `i`-th component of the augmentation is `η_i`. -/
theorem augMap_π (i : ι) : augMap A η ≫ biproduct.π A i = η i :=
  biproduct.lift_π _ _

omit [Fintype ι] [DecidableEq ι] in
/-- A morphism into `⊕_i A_i` is killed by the differential exactly when its components are
compatible with `fst` and `snd`. -/
theorem comp_diffMap_eq_zero_iff {T : C} (a : T ⟶ ⨁ A) :
    a ≫ diffMap A B fst snd = 0 ↔
      ∀ p : ι × ι, (a ≫ biproduct.π A p.1) ≫ fst p = (a ≫ biproduct.π A p.2) ≫ snd p := by
  constructor
  · intro ha p
    have e1 : a ≫ diffMap A B fst snd ≫ biproduct.π B p = 0 := by
      rw [← Category.assoc, ha, zero_comp]
    rw [diffMap_π, Preadditive.comp_sub, sub_eq_zero] at e1
    simpa only [Category.assoc] using e1
  · intro h
    refine biproduct.hom_ext _ _ fun p => ?_
    rw [Category.assoc, diffMap_π, zero_comp, Preadditive.comp_sub, sub_eq_zero,
      ← Category.assoc, ← Category.assoc]
    exact h p

variable (hη : ∀ p : ι × ι, η p.1 ≫ fst p = η p.2 ≫ snd p)

omit [Fintype ι] [DecidableEq ι] in
include hη in
/-- The augmentation followed by the differential is zero. -/
theorem augMap_diffMap : augMap A η ≫ diffMap A B fst snd = 0 :=
  (comp_diffMap_eq_zero_iff A B fst snd _).mpr fun p => by
    simpa only [augMap_π] using hη p

variable {D : Type*} [Category D] [Preadditive D] (Ψ : C ⥤ D) [Ψ.Additive] (k : ι)
  [IsIso (Ψ.map (η k))] [∀ i, IsIso (Ψ.map (snd (k, i)))]

/-- The retraction of the augmentation after `Ψ`: the projection to the `k`-th term followed by
the inverse of `Ψ(η_k)`. -/
def augRetraction : Ψ.obj (⨁ A) ⟶ Ψ.obj G :=
  Ψ.map (biproduct.π A k) ≫ inv (Ψ.map (η k))

omit [Fintype ι] [DecidableEq ι] [Preadditive D] [Ψ.Additive] in
/-- `augRetraction` is a left inverse of the image of the augmentation under `Ψ`. -/
theorem map_augMap_comp_augRetraction :
    Ψ.map (augMap A η) ≫ augRetraction A η Ψ k = 𝟙 _ := by
  rw [augRetraction, ← Category.assoc, ← Ψ.map_comp, augMap_π, IsIso.hom_inv_id]

/-- The contracting homotopy in degree `1` after `Ψ`. -/
def diffHomotopy : Ψ.obj (⨁ B) ⟶ Ψ.obj (⨁ A) :=
  -∑ i, Ψ.map (biproduct.π B (k, i)) ≫ inv (Ψ.map (snd (k, i))) ≫ Ψ.map (biproduct.ι A i)

omit [DecidableEq ι] in
/-- The `l`-th component of the contracting homotopy is `-(Ψ(snd_{kl})⁻¹ ∘ Ψ(π_{kl}))`. -/
theorem diffHomotopy_comp_map_π (l : ι) :
    diffHomotopy A B snd Ψ k ≫ Ψ.map (biproduct.π A l) =
      -(Ψ.map (biproduct.π B (k, l)) ≫ inv (Ψ.map (snd (k, l)))) := by
  rw [diffHomotopy, Preadditive.neg_comp]
  congr 1
  simpa only [Category.assoc] using sum_comp_map_ι_comp_map_π Ψ A
    (fun i => Ψ.map (biproduct.π B (k, i)) ≫ inv (Ψ.map (snd (k, i)))) l

omit [DecidableEq ι] in
include hη in
/-- **The homotopy identity `d ∘ h + ε ∘ s = id` in degree `0`** after `Ψ`. -/
theorem map_diffMap_comp_diffHomotopy :
    Ψ.map (diffMap A B fst snd) ≫ diffHomotopy A B snd Ψ k =
      𝟙 _ - augRetraction A η Ψ k ≫ Ψ.map (augMap A η) := by
  refine hom_ext_map_biproduct Ψ A fun l => ?_
  have hd : Ψ.map (diffMap A B fst snd) ≫ Ψ.map (biproduct.π B (k, l)) =
      Ψ.map (biproduct.π A k) ≫ Ψ.map (fst (k, l)) -
        Ψ.map (biproduct.π A l) ≫ Ψ.map (snd (k, l)) := by
    rw [← Ψ.map_comp, diffMap_π, Ψ.map_sub, Ψ.map_comp, Ψ.map_comp]
  have hc : Ψ.map (fst (k, l)) ≫ inv (Ψ.map (snd (k, l))) =
      inv (Ψ.map (η k)) ≫ Ψ.map (η l) := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, ← Ψ.map_comp, ← Ψ.map_comp]
    exact congrArg Ψ.map (hη (k, l))
  rw [Category.assoc, diffHomotopy_comp_map_π, Preadditive.comp_neg, ← Category.assoc, hd,
    Preadditive.sub_comp, Preadditive.sub_comp, Category.id_comp, Category.assoc, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id, hc, augRetraction, Category.assoc, Category.assoc,
    ← Ψ.map_comp, augMap_π, neg_sub]

omit [Fintype ι] [DecidableEq ι] [Preadditive D] [Ψ.Additive] in
include k in
/-- **The augmentation is split injective after `Ψ`.** -/
theorem isSplitMono_map_augMap : IsSplitMono (Ψ.map (augMap A η)) :=
  IsSplitMono.mk' ⟨augRetraction A η Ψ k, map_augMap_comp_augRetraction A η Ψ k⟩

variable [HasCokernel (augMap A η)]

omit [Fintype ι] [DecidableEq ι] in
include hη k in
/-- **The map from the cokernel of the augmentation to `⊕_{i,j} B_{ij}` is split injective after
`Ψ`**, as soon as `Ψ` keeps the projection onto the cokernel an epimorphism: the contracting
homotopy followed by that projection is a retraction. -/
theorem isSplitMono_map_cokernelDesc [Finite ι] [Epi (Ψ.map (cokernel.π (augMap A η)))] :
    IsSplitMono (Ψ.map (cokernel.desc (augMap A η) (diffMap A B fst snd)
      (augMap_diffMap A B η fst snd hη))) := by
  have := Fintype.ofFinite ι
  refine IsSplitMono.mk' ⟨diffHomotopy A B snd Ψ k ≫ Ψ.map (cokernel.π (augMap A η)), ?_⟩
  rw [← cancel_epi (Ψ.map (cokernel.π (augMap A η))), ← Category.assoc, ← Ψ.map_comp,
    cokernel.π_desc, ← Category.assoc, map_diffMap_comp_diffHomotopy A B η fst snd hη Ψ k,
    Preadditive.sub_comp, Category.id_comp, Category.assoc, ← Ψ.map_comp, cokernel.condition,
    Ψ.map_zero, Limits.comp_zero, sub_zero, Category.comp_id]

end AbstractCech

/-! ### Exactness of the image of the augmented diagram -/

section AbstractLimit

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D] (F : C ⥤ D) [F.Additive]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {G : C} (A : ι → C) (B : ι × ι → C)
  (η : ∀ i, G ⟶ A i) (fst : ∀ p : ι × ι, A p.1 ⟶ B p) (snd : ∀ p : ι × ι, A p.2 ⟶ B p)
  (hη : ∀ p : ι × ι, η p.1 ≫ fst p = η p.2 ≫ snd p)
  (h₁ : Mono (F.map (augMap A η)))
  (h₂ : ((ShortComplex.mk (augMap A η) (cokernel.π (augMap A η)) (cokernel.condition _)).map
    F).Exact)
  (h₃ : Mono (F.map (cokernel.desc (augMap A η) (diffMap A B fst snd)
    (augMap_diffMap A B η fst snd hη))))
  {T : D} (t : ∀ i, T ⟶ F.obj (A i))
  (ht : ∀ p : ι × ι, t p.1 ≫ F.map (fst p) = t p.2 ≫ F.map (snd p))

/-- The morphism `T ⟶ F(⊕_i A_i)` with components `t_i`. -/
def sumMap : T ⟶ F.obj (⨁ A) := ∑ i, t i ≫ F.map (biproduct.ι A i)

omit [DecidableEq ι] in
/-- The `i`-th component of `sumMap` is `t_i`. -/
theorem sumMap_comp_map_π (i : ι) : sumMap F A t ≫ F.map (biproduct.π A i) = t i :=
  sum_comp_map_ι_comp_map_π F A t i

omit [DecidableEq ι] in
include ht in
/-- `sumMap` of a family compatible with `fst` and `snd` is killed by the image of the
differential. -/
theorem sumMap_comp_map_diffMap : sumMap F A t ≫ F.map (diffMap A B fst snd) = 0 := by
  refine hom_ext_map_biproduct F B fun p => ?_
  rw [Category.assoc, ← F.map_comp, diffMap_π, F.map_sub, F.map_comp, F.map_comp,
    Preadditive.comp_sub, ← Category.assoc, ← Category.assoc, sumMap_comp_map_π,
    sumMap_comp_map_π, zero_comp, sub_eq_zero]
  exact ht p

omit [DecidableEq ι] in
include h₃ ht in
/-- `sumMap` of a compatible family is killed by the image of the projection onto the cokernel of
the augmentation. -/
theorem sumMap_comp_map_cokernelπ : sumMap F A t ≫ F.map (cokernel.π (augMap A η)) = 0 := by
  have := h₃
  rw [← cancel_mono (F.map (cokernel.desc (augMap A η) (diffMap A B fst snd)
    (augMap_diffMap A B η fst snd hη))), zero_comp, Category.assoc, ← F.map_comp,
    cokernel.π_desc]
  exact sumMap_comp_map_diffMap F A B fst snd t ht

/-- The factorisation through `F(G)` of a family of morphisms compatible with `fst` and `snd`. -/
def liftOfExact : T ⟶ F.obj G :=
  have : Mono ((ShortComplex.mk (augMap A η) (cokernel.π (augMap A η))
    (cokernel.condition _)).map F).f := h₁
  h₂.lift (sumMap F A t) (sumMap_comp_map_cokernelπ F A B η fst snd hη h₃ t ht)

omit [DecidableEq ι] in
/-- `liftOfExact` followed by the image of the augmentation is `sumMap`. -/
theorem liftOfExact_comp_map_augMap :
    liftOfExact F A B η fst snd hη h₁ h₂ h₃ t ht ≫ F.map (augMap A η) = sumMap F A t :=
  have : Mono ((ShortComplex.mk (augMap A η) (cokernel.π (augMap A η))
    (cokernel.condition _)).map F).f := h₁
  h₂.lift_f _ _

omit [DecidableEq ι] in
/-- `liftOfExact` followed by `F(η_i)` is `t_i`. -/
theorem liftOfExact_comp_map (i : ι) :
    liftOfExact F A B η fst snd hη h₁ h₂ h₃ t ht ≫ F.map (η i) = t i := by
  rw [← augMap_π A η i, F.map_comp, ← Category.assoc, liftOfExact_comp_map_augMap,
    sumMap_comp_map_π]

omit [DecidableEq ι] in
include h₁ in
/-- A morphism `T ⟶ F(G)` whose composites with the `F(η_i)` are the `t_i` is `liftOfExact`. -/
theorem eq_liftOfExact (m : T ⟶ F.obj G) (hm : ∀ i, m ≫ F.map (η i) = t i) :
    m = liftOfExact F A B η fst snd hη h₁ h₂ h₃ t ht := by
  have := h₁
  rw [← cancel_mono (F.map (augMap A η)), liftOfExact_comp_map_augMap]
  refine hom_ext_map_biproduct F A fun i => ?_
  rw [sumMap_comp_map_π, Category.assoc, ← F.map_comp, augMap_π]
  exact hm i

end AbstractLimit

/-! ### The Čech complex of a finite open cover in degrees `0` and `1` -/

section CechComplex

variable {Z : Scheme.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι] (V : ι → Z.Opens)
  [∀ i, QuasiCompact (V i).ι] [∀ i, QuasiSeparated (V i).ι]
  [∀ i j, QuasiCompact (V i ⊓ V j).ι] [∀ i j, QuasiSeparated (V i ⊓ V j).ι]
  (G : Scheme.QuasicoherentModules Z)

/-- The terms `(V_i)_*(G|_{V_i})` of the Čech complex in degree `0`. -/
abbrev cechTerm₀ : ι → Scheme.QuasicoherentModules Z := fun i => (cechObj (V i)).obj G

/-- The terms `(V_i ∩ V_j)_*(G|_{V_i ∩ V_j})` of the Čech complex in degree `1`. -/
abbrev cechTerm₁ : ι × ι → Scheme.QuasicoherentModules Z := fun p => (cechObj (V p.1 ⊓ V p.2)).obj G

/-- The augmentation `G ⟶ ⊕_i (V_i)_*(G|_{V_i})` of the Čech complex. -/
abbrev cechAug : G ⟶ ⨁ cechTerm₀ V G :=
  augMap (cechTerm₀ V G) fun i => (cechUnit (V i)).app G

/-- The first differential `⊕_i (V_i)_*(G|_{V_i}) ⟶ ⊕_{i,j} (V_i ∩ V_j)_*(G|_{V_i ∩ V_j})` of the
Čech complex. -/
abbrev cechDiff : (⨁ cechTerm₀ V G) ⟶ ⨁ cechTerm₁ V G :=
  diffMap (cechTerm₀ V G) (cechTerm₁ V G) (cechIndex V G).fst (cechIndex V G).snd

omit [DecidableEq ι] in
/-- The `(i, j)`-component of the first Čech differential is the difference of the two
restrictions to `V_i ∩ V_j`. -/
theorem cechDiff_π (p : ι × ι) :
    cechDiff V G ≫ biproduct.π (cechTerm₁ V G) p =
      biproduct.π (cechTerm₀ V G) p.1 ≫ (cechIndex V G).fst p -
        biproduct.π (cechTerm₀ V G) p.2 ≫ (cechIndex V G).snd p :=
  diffMap_π _ _ _ _ p

omit [DecidableEq ι] [∀ i j, QuasiCompact (V i ⊓ V j).ι] [∀ i j, QuasiSeparated (V i ⊓ V j).ι] in
/-- The `i`-th component of the Čech augmentation is the unit `G ⟶ (V_i)_*(G|_{V_i})`. -/
theorem cechAug_π (i : ι) :
    cechAug V G ≫ biproduct.π (cechTerm₀ V G) i = (cechUnit (V i)).app G :=
  augMap_π _ _ i

omit [DecidableEq ι] in
/-- The Čech augmentation followed by the first Čech differential is zero. -/
theorem cechAug_cechDiff : cechAug V G ≫ cechDiff V G = 0 :=
  augMap_diffMap (cechTerm₀ V G) (cechTerm₁ V G) (fun i => (cechUnit (V i)).app G)
    (cechIndex V G).fst (cechIndex V G).snd (cechMultifork V G).condition

/-- The Čech complex in degrees `0` and `1`, as a short complex. -/
abbrev cechShortComplex : ShortComplex (Scheme.QuasicoherentModules Z) :=
  ShortComplex.mk (cechAug V G) (cechDiff V G) (cechAug_cechDiff V G)

end CechComplex

/-! ### The Čech complex is split on the stalks -/

section CechStalk

variable {Z : Scheme.{u}} {ι : Type u} [Fintype ι] [DecidableEq ι] (V : ι → Z.Opens)
  [∀ i, QuasiCompact (V i).ι] [∀ i, QuasiSeparated (V i).ι]
  [∀ i j, QuasiCompact (V i ⊓ V j).ι] [∀ i j, QuasiSeparated (V i ⊓ V j).ι]
  (G : Scheme.QuasicoherentModules Z)

/-- The stalk at a point, on quasi-coherent modules. -/
def qcohStalk (x : Z) :=
  (SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι ⋙
    AlgebraicGeometry.SheafOfModules.stalkFunctor Z.ringCatSheaf x

/-- The stalk functor on quasi-coherent modules is additive. -/
instance (x : Z) : (qcohStalk x).Additive :=
  Functor.instAdditiveComp _ _

/-- The stalk functor on quasi-coherent modules preserves epimorphisms. -/
instance (x : Z) : (qcohStalk x).PreservesEpimorphisms := by
  unfold qcohStalk
  infer_instance

/-- `qcohStalk x` sends a morphism of quasi-coherent modules to the map it induces on the stalks
at `x` of the underlying sheaves of modules. -/
theorem qcohStalk_map (x : Z) {M N : Scheme.QuasicoherentModules Z} (φ : M ⟶ N) :
    (qcohStalk x).map φ =
      (AlgebraicGeometry.SheafOfModules.stalkFunctor Z.ringCatSheaf x).map φ.hom := rfl

/-- The unit `G ⟶ (V_k)_*(G|_{V_k})` is invertible on the stalks at the points of `V_k`. -/
instance isIso_qcohStalk_map_cechUnit (k : ι) (x : V k) :
    IsIso ((qcohStalk ((V k).ι x)).map ((cechUnit (V k)).app G)) := by
  have : IsIso ((Scheme.Modules.restrictFunctor (V k).ι).map ((cechUnit (V k)).app G).hom) := by
    rw [cechUnit_app_hom]
    exact isIso_restrictFunctor_map_unit (V k) G.obj
  rw [qcohStalk_map]
  exact isIso_stalkFunctor_map_of_isIso_restrictFunctor_map _ (V k) x

/-- The restriction `(V_i)_*(G|_{V_i}) ⟶ (V_k ∩ V_i)_*(G|_{V_k ∩ V_i})` is invertible on the stalks
at the points of `V_k`. -/
instance isIso_qcohStalk_map_cechIndex_snd (k i : ι) (x : V k) :
    IsIso ((qcohStalk ((V k).ι x)).map (X := cechTerm₀ V G i) (Y := cechTerm₁ V G (k, i))
      ((cechIndex V G).snd (k, i))) := by
  have : IsIso ((Scheme.Modules.restrictFunctor (V k).ι).map
      ((cechIndex V G).snd (k, i)).hom) :=
    isIso_restrictFunctor_map_restrictPushModMap (inf_le_right : V k ⊓ V i ≤ V i) le_rfl G.obj
  exact @isIso_stalkFunctor_map_of_isIso_restrictFunctor_map _ _ _ _ (V k) this x

end CechStalk

section CechExact

variable (R : Type u) [CommRing R] (X : Over (Spec (.of R)))
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (V : ι → X.left.Opens)
  [∀ i, QuasiCompact (V i).ι] [∀ i, QuasiSeparated (V i).ι]
  [∀ i j, QuasiCompact (V i ⊓ V j).ι] [∀ i j, QuasiSeparated (V i ⊓ V j).ι]
  (hV : TopologicalSpace.IsOpenCover V) (G : Scheme.QuasicoherentModules X.left)

/-- The factorisation through `G` of a morphism into `⊕_i (V_i)_*(G|_{V_i})` killed by the
first differential. -/
def cechAugLift {T : Scheme.QuasicoherentModules X.left} (a : T ⟶ ⨁ cechTerm₀ V G)
    (ha : a ≫ cechDiff V G = 0) : T ⟶ G :=
  (isLimitCechMultifork R X V hV G).lift
    (Multifork.ofι _ T (fun i => a ≫ biproduct.π (cechTerm₀ V G) i)
      ((comp_diffMap_eq_zero_iff (cechTerm₀ V G) (cechTerm₁ V G) (cechIndex V G).fst
        (cechIndex V G).snd a).mp ha))

omit [CompactSpace X.left] [QuasiSeparatedSpace X.left] [DecidableEq ι] in
/-- `cechAugLift a` followed by the unit `G ⟶ (V_i)_*(G|_{V_i})` is the `i`-th component of `a`. -/
theorem cechAugLift_comp {T : Scheme.QuasicoherentModules X.left} (a : T ⟶ ⨁ cechTerm₀ V G)
    (ha : a ≫ cechDiff V G = 0) (i : ι) :
    cechAugLift R X V hV G a ha ≫ (cechUnit (V i)).app G =
      a ≫ biproduct.π (cechTerm₀ V G) i :=
  (isLimitCechMultifork R X V hV G).fac _ (.left i)

/-- **The augmentation of the Čech complex of an open cover is a kernel of its first
differential**: this is the sheaf condition, read through the Čech multifork. -/
def isLimitCechAug :
    IsLimit (KernelFork.ofι (cechAug V G) (cechAug_cechDiff V G)) :=
  KernelFork.IsLimit.ofι _ _ (fun a ha => cechAugLift R X V hV G a ha)
    (fun a ha => biproduct.hom_ext _ _ fun j =>
      (Category.assoc _ _ _).trans ((congrArg (cechAugLift R X V hV G a ha ≫ ·)
        (augMap_π (cechTerm₀ V G) (fun i => (cechUnit (V i)).app G) j)).trans
          (cechAugLift_comp R X V hV G a ha j)))
    (fun a ha m hm => Multifork.IsLimit.hom_ext (isLimitCechMultifork R X V hV G)
      fun j => (congrArg (m ≫ ·)
        (augMap_π (cechTerm₀ V G) (fun i => (cechUnit (V i)).app G) j).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ biproduct.π (cechTerm₀ V G) j) hm).trans
            (cechAugLift_comp R X V hV G a ha j).symm)))

omit [CompactSpace X.left] [QuasiSeparatedSpace X.left] [DecidableEq ι] in
include hV in
/-- The Čech complex of an open cover is exact in degree `0`. -/
theorem cechShortComplex_exact : (cechShortComplex V G).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (isLimitCechAug R X V hV G)

omit [CompactSpace X.left] [QuasiSeparatedSpace X.left] [DecidableEq ι] in
include hV in
/-- The augmentation of the Čech complex of an open cover is a monomorphism. -/
theorem mono_cechAug : Mono (cechAug V G) :=
  Fork.IsLimit.mono (isLimitCechAug R X V hV G)

end CechExact


/-! ### A functor with property (3) preserves the Čech multiforks -/

section Converse

variable (R : Type u) [CommRing R] (X : Over (Spec (.of R)))
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  {ι : Type u} [Fintype ι] [DecidableEq ι] (V : ι → X.left.Opens)
  [∀ i, QuasiCompact (V i).ι] [∀ i, QuasiSeparated (V i).ι]
  [∀ i j, QuasiCompact (V i ⊓ V j).ι] [∀ i j, QuasiSeparated (V i ⊓ V j).ι]
  (hV : TopologicalSpace.IsOpenCover V) (G : Scheme.QuasicoherentModules X.left)

omit [CompactSpace X.left] [QuasiSeparatedSpace X.left] [Fintype ι] [DecidableEq ι]
  [∀ i, QuasiCompact (V i).ι] [∀ i, QuasiSeparated (V i).ι] [∀ i j, QuasiCompact (V i ⊓ V j).ι]
  [∀ i j, QuasiSeparated (V i ⊓ V j).ι] in
include hV in
/-- Every point lies in some member of an open cover. -/
theorem exists_mem_of_isOpenCover (x : X.left) : ∃ k, x ∈ V k := by
  have hx : x ∈ iSup V := by
    rw [show iSup V = ⊤ from hV]
    trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hx

omit [CompactSpace X.left] [QuasiSeparatedSpace X.left] [DecidableEq ι]
  [∀ i j, QuasiCompact (V i ⊓ V j).ι] [∀ i j, QuasiSeparated (V i ⊓ V j).ι] in
include hV in
/-- The augmentation of the Čech complex is split injective on every stalk. -/
theorem isSplitMono_stalkFunctor_map_cechAug (x : X.left) :
    IsSplitMono ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.left.ringCatSheaf x).map
      (cechAug V G).hom) := by
  obtain ⟨k, hk⟩ := exists_mem_of_isOpenCover R X V hV x
  exact isSplitMono_map_augMap (cechTerm₀ V G) (fun i => (cechUnit (V i)).app G)
    (qcohStalk ((V k).ι ⟨x, hk⟩)) k

omit [CompactSpace X.left] [QuasiSeparatedSpace X.left] [DecidableEq ι] in
include hV in
/-- The map from the cokernel of the augmentation of the Čech complex to its degree `1` term is
split injective on every stalk. -/
theorem isSplitMono_stalkFunctor_map_cokernelDesc (x : X.left) :
    IsSplitMono ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.left.ringCatSheaf x).map
      (cokernel.desc (cechAug V G) (cechDiff V G) (cechAug_cechDiff V G)).hom) := by
  obtain ⟨k, hk⟩ := exists_mem_of_isOpenCover R X V hV x
  exact isSplitMono_map_cokernelDesc (cechTerm₀ V G) (cechTerm₁ V G)
    (fun i => (cechUnit (V i)).app G) (cechIndex V G).fst (cechIndex V G).snd
    (cechMultifork V G).condition (qcohStalk ((V k).ι ⟨x, hk⟩)) k

variable {D : Type*} [Category D] [Abelian D] (F : Scheme.QuasicoherentModules X.left ⥤ D)
  [F.Additive]

/-- **A functor with property (3) of Tag 0GPB carries the Čech multifork of a finite open cover
to a limit.**  The Čech complex `0 ⟶ G ⟶ ⊕ (V_i)_*(G|_{V_i}) ⟶ ⊕ (V_i ∩ V_j)_*(G|_{V_i ∩ V_j})`
breaks into two short exact sequences which are split on every stalk, and property (3) makes
the image of the complex exact. -/
def isLimitMapConeCechMultifork (hF : IsStalkwiseSplitLeftExact F) :
    IsLimit (F.mapCone (cechMultifork V G)) := by
  let ε := cechAug V G
  have hε : Mono ε := mono_cechAug R X V hV G
  let S₁ := ShortComplex.mk ε (cokernel.π ε) (cokernel.condition ε)
  have hS₁ : S₁.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ε) }
  have h₁ := hF S₁ hS₁ (isSplitMono_stalkFunctor_map_cechAug R X V hV G)
  let δ := cokernel.desc ε (cechDiff V G) (cechAug_cechDiff V G)
  have hδ : Mono δ := (cechShortComplex_exact R X V hV G).mono_cokernelDesc
  let S₂ := ShortComplex.mk δ (cokernel.π δ) (cokernel.condition δ)
  have hS₂ : S₂.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel δ) }
  have h₂ := hF S₂ hS₂ (isSplitMono_stalkFunctor_map_cokernelDesc R X V hV G)
  let A := cechTerm₀ V G
  let B := cechTerm₁ V G
  let η : ∀ i, G ⟶ A i := fun i => (cechUnit (V i)).app G
  have hη := (cechMultifork V G).condition
  exact
    { lift := fun K => liftOfExact F A B η (cechIndex V G).fst (cechIndex V G).snd hη h₁.1 h₁.2 h₂.1
        (fun i => K.π.app (.left i)) fun p => by
          have h1 : K.π.app (.left p.1) ≫ F.map ((cechIndex V G).fst p) = K.π.app (.right p) :=
            K.w (multicospanFst p)
          have h2 : K.π.app (.left p.2) ≫ F.map ((cechIndex V G).snd p) = K.π.app (.right p) :=
            K.w (multicospanSnd p)
          exact h1.trans h2.symm
      fac := fun K j => by
        rcases j with i | p
        · exact liftOfExact_comp_map F A B η _ _ hη h₁.1 h₁.2 h₂.1 _ _ i
        · refine (congrArg (_ ≫ ·) (F.congr_map
            (Multifork.app_right_eq_ι_comp_fst (cechMultifork V G) p))).trans ?_
          refine (congrArg (_ ≫ ·) (F.map_comp _ _)).trans ((Category.assoc _ _ _).symm.trans ?_)
          exact (congrArg (· ≫ F.map ((cechIndex V G).fst p))
            (liftOfExact_comp_map F A B η _ _ hη h₁.1 h₁.2 h₂.1 _ _ p.1)).trans
              (K.w (multicospanFst p))
      uniq := fun K m hm =>
        eq_liftOfExact F A B η _ _ hη h₁.1 h₁.2 h₂.1 _ _ m fun i => hm (.left i) }

end Converse

/-! ### The converse: a functor with the three properties is an integral transform -/

section Kernel

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [CompactSpace X.left]
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]

attribute [local instance] isAffineHom_ι_affineOpens isAffineHom_ι_affineOpens_inf

/-- **Property (2) of Tag 0GPB.**  `F ∘ j_*` is right exact for the inclusion `j : U ⟶ X` of
every affine open `U` of `X`. -/
def PreservesFiniteColimitsAfterAffineOpens {D : Type*} [Category D]
    (F : Scheme.QuasicoherentModules X.left ⥤ D) : Prop :=
  ∀ (U : X.left.Opens) (hU : IsAffineOpen U),
    let : IsAffineHom U.ι := isAffineHom_ι_of_isAffineOpen hU
    PreservesFiniteColimits (quasicoherentPushforward U.ι ⋙ F)

omit [CompactSpace X.left] in
/-- Property (2) of Tag 0GPB gives right exactness after direct image along every open
immersion with affine source: such an immersion is an isomorphism onto an affine open followed
by its inclusion. -/
theorem preservesFiniteColimits_pushforward_comp_of_isOpenImmersion {D : Type*} [Category D]
    (F : Scheme.QuasicoherentModules X.left ⥤ D)
    (hF : PreservesFiniteColimitsAfterAffineOpens R X F) {X' : Over (Spec (.of R))}
    [IsAffine X'.left] (f : X' ⟶ X) [IsOpenImmersion f.left] :
    letI : IsAffineHom f.left := isAffineHom_left_of_isAffine_left R X f
    PreservesFiniteColimits (quasicoherentPushforward f.left ⋙ F) := by
  let : IsAffineHom f.left := isAffineHom_left_of_isAffine_left R X f
  have hU : IsAffineOpen f.left.opensRange := isAffineOpen_opensRange f.left
  let : IsAffineHom f.left.opensRange.ι := isAffineHom_ι_of_isAffineOpen hU
  have hU' : PreservesFiniteColimits (quasicoherentPushforward f.left.opensRange.ι ⋙ F) :=
    hF _ hU
  have key : ∀ (g : X'.left ⟶ X.left) [QuasiCompact g] [QuasiSeparated g],
      f.left.isoOpensRange.hom ≫ f.left.opensRange.ι = g →
        PreservesFiniteColimits (quasicoherentPushforward g ⋙ F) := by
    rintro g _ _ rfl
    have : PreservesFiniteColimits (quasicoherentPushforward f.left.isoOpensRange.hom) :=
      preservesFiniteColimits_quasicoherentPushforward _
    have : PreservesFiniteColimits ((quasicoherentPushforward f.left.isoOpensRange.hom ⋙
        quasicoherentPushforward f.left.opensRange.ι) ⋙ F) :=
      inferInstanceAs (PreservesFiniteColimits (quasicoherentPushforward
        f.left.isoOpensRange.hom ⋙ quasicoherentPushforward f.left.opensRange.ι ⋙ F))
    exact preservesFiniteColimits_of_natIso
      (Functor.isoWhiskerRight (quasicoherentPushforwardComp _ _) F)
  exact key f.left (Scheme.Hom.isoOpensRange_hom_ι f.left)

/-- **The direction (1) + (2) + (3) ⇒ integral transform of Tag 0GPB.**  An `R`-linear functor
commuting with arbitrary direct sums, right exact after direct image along the inclusions of the
affine opens of `X`, and with property (3), is isomorphic to the integral transform of the kernel
glued from the kernels of the affine opens (`AlgebraicGeometry.openKernelSystem`).  The
transformation `t : F ⟶ F_K` of Tag 0GPA is an isomorphism on direct images from affine opens,
and both functors carry the Čech multifork of a finite affine open cover to a limit: `F_K`
because it is an integral transform, `F` by property (3). -/
theorem exists_iso_quasicoherentIntegralTransform_of_isStalkwiseSplitLeftExact
    (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left)
    (hadd : F.Additive)
    (hlin : letI : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
      letI : Linear R (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear R Y
      F.Linear R)
    (hsum : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) F)
    (h₂ : PreservesFiniteColimitsAfterAffineOpens R X F) (h₃ : IsStalkwiseSplitLeftExact F) :
    ∃ K : Scheme.QuasicoherentModules (pullback X.hom Y.hom),
      Nonempty (F ≅ quasicoherentIntegralTransform R X Y K) := by
  classical
  have hF : affineOpenRightExactLinearCoproductFunctor R X Y F :=
    ⟨⟨hadd, hlin⟩, fun X' _ f _ =>
      preservesFiniteColimits_pushforward_comp_of_isOpenImmersion R X F h₂ f, hsum⟩
  obtain ⟨s, hs⟩ := isOpenCover_finset_affineOpens R X
  have := hadd
  have := isIso_kernelTransform_of_isLimit R X Y F hF s hs fun G =>
    isLimitMapConeCechMultifork R X (fun i : s => ((i : X.left.affineOpens) : X.left.Opens)) hs
      G F h₃
  exact ⟨_, ⟨asIso (kernelTransform R X Y F hF)⟩⟩

end Kernel


/-! ### Integral transforms have property (3) -/

section Forward

open Stacks.SheafOfModules.TensorStalkRingedSpace (O ringStalk grpStalk grpGerm stalkModule
  stalkModule_germ_smul stalkMapL)

/-- **The two scalar actions on the stalk of a sheaf of modules agree**: the action of the
`CommRingCat`-valued stalk `𝒪_{Z,y}` built from germ representatives is the action of the
`RingCat`-valued stalk transported along the comparison of the two stalks. -/
theorem stalkModule_smul_eq {Z : RingedSpace.{u, u}} (M : PresheafOfModules.{u} (O Z))
    (y : Z.carrier) (b : ringStalk Z y) (n : grpStalk Z M y) :
    letI := stalkModule Z M y
    b • n = (SemilinearStalk.commStalkRingEquiv Z.presheaf y).symm b • n := by
  obtain ⟨V, hV, a, rfl⟩ := Z.presheaf.exists_germ_eq b
  obtain ⟨W, hW, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf n
  have hy : y ∈ V ⊓ W := ⟨hV, hW⟩
  rw [← TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE (inf_le_left : V ⊓ W ≤ V)) y hy a,
    ← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE (inf_le_right : V ⊓ W ≤ W)) y hy t]
  generalize Z.presheaf.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op a = a'
  generalize M.presheaf.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op t = t'
  have h2 : (SemilinearStalk.commStalkRingEquiv Z.presheaf y).symm
      (Z.presheaf.germ (V ⊓ W) y hy a') =
        TopCat.Presheaf.germ (C := RingCat.{u}) (Z.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u})
          (V ⊓ W) y hy a' := by
    rw [RingEquiv.symm_apply_eq]
    exact (SemilinearStalk.commStalkRingEquiv_germ Z.presheaf y (V ⊓ W) hy a').symm
  rw [h2]
  exact (stalkModule_germ_smul Z M y (V ⊓ W) hy a' t').symm.trans
    (PresheafOfModules.germ_ringCat_smul M y (V ⊓ W) hy a' t')

/-- **A stalk map which is a split monomorphism of modules over the `RingCat`-valued stalk has an
`𝒪_{Z,y}`-linear retraction**, for the module structure of
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`. -/
theorem exists_comp_stalkMapL_eq_id {Z : RingedSpace.{u, u}}
    {M N : SheafOfModules.{u} (structureSheafRing Z)} (φ : M ⟶ N) (y : Z.carrier)
    (h : IsSplitMono
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Z) y).map φ)) :
    ∃ r : grpStalk Z N.val y →ₗ[ringStalk Z y] grpStalk Z M.val y,
      r ∘ₗ stalkMapL Z M.val N.val φ.val y = LinearMap.id := by
  obtain ⟨⟨ρ, hρ⟩⟩ := h
  refine ⟨{ toFun := ρ.hom, map_add' := ρ.hom.map_add, map_smul' := fun b n => ?_ }, ?_⟩
  · rw [RingHom.id_apply, stalkModule_smul_eq N.val y b n, stalkModule_smul_eq M.val y b (ρ.hom n)]
    exact ρ.hom.map_smul _ n
  · exact LinearMap.ext fun m => congrArg (fun q => q.hom m) hρ

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))

/-- **The integrand of an integral transform carries a stalkwise split monomorphism to a
monomorphism.**  It is `pr_1^*(−) ⊗ K`, and on the stalk at a point `z` of `X ×_R Y` it is
`K_z ⊗_{𝒪_{X, pr_1 z}} (−)_{pr_1 z}`. -/
theorem mono_integralTransformIntegrand_map
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
    {A B : Scheme.QuasicoherentModules X.left} (φ : A ⟶ B)
    (hφ : ∀ x : X.left, IsSplitMono
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.left.ringCatSheaf x).map φ.hom)) :
    Mono ((integralTransformIntegrand R X Y K).map φ) := by
  have h : Mono ((Stacks.SheafOfModules.pullbackTensorFunctor
      (pullback.fst X.hom Y.hom).toLRSHom.toShHom K.obj).map φ.hom) :=
    Stacks.SheafOfModules.pullbackTensorFunctor_map_mono _ _ φ.hom fun z =>
      exists_comp_stalkMapL_eq_id φ.hom _ (hφ _)
  let e := Functor.isoWhiskerLeft (Scheme.Modules.pullback (pullback.fst X.hom Y.hom))
    ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
      ((pullback X.hom Y.hom)).presheaf ((pullback X.hom Y.hom)).ringCatSheaf.2 (K.obj)))
  have hn := e.hom.naturality φ.hom
  have : Mono (e.hom.app A.obj) := inferInstanceAs (Mono (e.app A.obj).hom)
  have : Mono ((Scheme.Modules.pullback (pullback.fst X.hom Y.hom) ⋙
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨(pullback X.hom Y.hom).presheaf, Presheaf.isSheaf_of_isSheaf_comp _
          ((pullback X.hom Y.hom).presheaf) (forget₂ CommRingCat RingCat)
          ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj (K.obj))).map φ.hom ≫
        e.hom.app B.obj) := by
    rw [hn]
    exact @mono_comp _ _ _ _ _ _ _ _ h
  exact @mono_of_mono _ _ _ _ _ _ _ this


/-- The integrand `pr_1^*(−) ⊗ K` of an integral transform is right exact, with no hypothesis on
the kernel: inverse image is a left adjoint and tensor product commutes with colimits. -/
theorem preservesFiniteColimits_integralTransformIntegrand
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    PreservesFiniteColimits (integralTransformIntegrand R X Y K) := by
  let J := Opens.grothendieckTopology (pullback X.hom Y.hom).carrier
  let R' : Sheaf J CommRingCat := ⟨(pullback X.hom Y.hom).presheaf, (pullback X.hom Y.hom).IsSheaf⟩
  have hten : PreservesColimitsOfSize.{u, u}
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨(pullback X.hom Y.hom).presheaf, Presheaf.isSheaf_of_isSheaf_comp _
          ((pullback X.hom Y.hom).presheaf) (forget₂ CommRingCat RingCat)
          ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj (K.obj))) :=
    Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits J R' K.obj
  have h₁ : PreservesFiniteColimits
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨(pullback X.hom Y.hom).presheaf, Presheaf.isSheaf_of_isSheaf_comp _
          ((pullback X.hom Y.hom).presheaf) (forget₂ CommRingCat RingCat)
          ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj (K.obj))) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have h₂ : PreservesFiniteColimits (Scheme.Modules.pullback (pullback.fst X.hom Y.hom)) :=
    inferInstance
  have h₃ : PreservesFiniteColimits
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.left.ringCatSheaf)) := inferInstance
  have h₄ := @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ h₂ h₁
  exact @comp_preservesFiniteColimits _ _ _ _ _ _ _ _ h₃ h₄

/-- **An integral transform has property (3) of Tag 0GPB.**  For a short exact sequence
`0 ⟶ F ⟶ G ⟶ H ⟶ 0` of quasi-coherent modules on `X` which is split on every stalk, the
integrand `pr_1^*(−) ⊗ K` keeps it short exact (it is right exact, and keeps the first map
injective on stalks), and direct image along the second projection is left exact. -/
theorem isStalkwiseSplitLeftExact_quasicoherentIntegralTransform [CompactSpace X.left]
    [QuasiSeparatedSpace X.left] (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    letI := quasicoherentIntegralTransform_additive R X Y K
    IsStalkwiseSplitLeftExact (quasicoherentIntegralTransform R X Y K) := by
  let := quasicoherentIntegralTransform_additive R X Y K
  intro S hS hsplit
  let I := integralTransformIntegrand R X Y K
  have hI : PreservesFiniteColimits I := preservesFiniteColimits_integralTransformIntegrand R X Y K
  have hzI : I.PreservesZeroMorphisms := by
    have : PreservesColimit (Functor.empty.{0} _) I := inferInstance
    exact Functor.preservesZeroMorphisms_of_preserves_initial_object (F := I)
  have : I.Additive := rightExactFunctor_le_additiveFunctor _ _ I hI
  have htf : PreservesFiniteColimits I ↔ ∀ S : ShortComplex (Scheme.QuasicoherentModules X.left),
      S.ShortExact → (S.map I).Exact ∧ Epi (I.map S.g) :=
    (Functor.preservesFiniteColimits_tfae I).out 4 1
  obtain ⟨hex, hepi⟩ := htf.mp hI S hS
  have hSI : (S.map I).ShortExact := ShortComplex.ShortExact.mk' hex
    (mono_integralTransformIntegrand_map R X Y K S.f hsplit) hepi
  let P := Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)
  have hPz : P.PreservesZeroMorphisms := inferInstanceAs
    (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).PreservesZeroMorphisms
  have htf' : PreservesFiniteLimits P ↔ ∀ S : ShortComplex (pullback X.hom Y.hom).Modules,
      S.ShortExact → (S.map P).Exact ∧ Mono (P.map S.f) :=
    (Functor.preservesFiniteLimits_tfae P).out 4 1
  obtain ⟨hPex, hPmono⟩ := htf'.mp inferInstance (S.map I) hSI
  let T := quasicoherentIntegralTransform R X Y K
  let ιY := ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf)
  let c := (quasicoherentIntegralTransformData R X Y K).comparison
  let e : (S.map T).map ιY ≅ @ShortComplex.map _ _ _ _ _ _ (S.map I) P hPz :=
    ShortComplex.isoMk (c.app S.X₁) (c.app S.X₂) (c.app S.X₃)
      (c.hom.naturality S.f).symm (c.hom.naturality S.g).symm
  obtain ⟨hex, hm⟩ := (ShortComplex.exact_and_mono_f_iff_of_iso e).mpr ⟨hPex, hPmono⟩
  exact ⟨ιY.mono_of_mono_map hm, (ShortComplex.exact_map_iff_of_faithful (S.map T) ιY).mp hex⟩

end Forward

/-! ### Tag 0GPB -/

section Main

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R))) [CompactSpace X.left]
  [IsAffineHom (pullback.diagonal (terminal.from X.left))]

/-- **Stacks Project, Tag 0GPB.**  Let `R` be a ring and let `X` and `Y` be schemes over `R`,
with `X` quasi-compact with affine diagonal.  A functor `F : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` is
isomorphic to the integral transform `F_K = pr_{2,*}(pr_1^*(−) ⊗ K)` of a quasi-coherent module
`K` on `X ×_R Y` if and only if

1. `F` is `R`-linear (in particular additive) and commutes with arbitrary direct sums,
2. `F ∘ j_*` is right exact for the inclusion `j : U ⟶ X` of every affine open `U`
   (`AlgebraicGeometry.PreservesFiniteColimitsAfterAffineOpens`), and
3. `0 ⟶ F(F) ⟶ F(G) ⟶ F(H)` is exact for every short exact sequence
   `0 ⟶ F ⟶ G ⟶ H ⟶ 0` of quasi-coherent modules whose sequences of stalks are split short
   exact sequences of `𝒪_{X,x}`-modules (`AlgebraicGeometry.IsStalkwiseSplitLeftExact`). -/
@[stacks 0GPB]
theorem nonempty_iso_quasicoherentIntegralTransform_iff
    (F : Scheme.QuasicoherentModules X.left ⥤ Scheme.QuasicoherentModules Y.left) :
    letI : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
    letI : Linear R (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear R Y
    (∃ K : Scheme.QuasicoherentModules (pullback X.hom Y.hom),
        Nonempty (F ≅ quasicoherentIntegralTransform R X Y K)) ↔
      ∃ _ : F.Additive, F.Linear R ∧ (∀ I : Type u, PreservesColimitsOfShape (Discrete I) F) ∧
        PreservesFiniteColimitsAfterAffineOpens R X F ∧ IsStalkwiseSplitLeftExact F := by
  let : Linear R (SheafOfModules.{u} X.left.ringCatSheaf) := modulesLinear R X
  let : Linear R (SheafOfModules.{u} Y.left.ringCatSheaf) := modulesLinear R Y
  constructor
  · rintro ⟨K, ⟨e⟩⟩
    let := quasicoherentIntegralTransform_additive R X Y K
    let := quasicoherentIntegralTransform_isLinearOverBase R X Y K
    let : F.Additive := Functor.additive_of_iso e.symm
    refine ⟨inferInstance, Functor.linear_of_iso (R := R) e.symm, fun I => ?_, fun U hU => ?_, ?_⟩
    · have := quasicoherentIntegralTransform_preservesDirectSums R X Y K I
      exact preservesColimitsOfShape_of_natIso e.symm
    · let : IsAffineHom U.ι := isAffineHom_ι_of_isAffineOpen hU
      have : PreservesFiniteColimits
          (quasicoherentPushforward U.ι ⋙ quasicoherentIntegralTransform R X Y K) :=
        preservesFiniteColimits_affineOpenPushforward_comp_integralTransform R X Y hU K
      exact preservesFiniteColimits_of_natIso (Functor.isoWhiskerLeft _ e.symm)
    · exact (isStalkwiseSplitLeftExact_quasicoherentIntegralTransform R X Y K).of_iso e.symm
  · exact fun ⟨hadd, hlin, hsum, h₂, h₃⟩ =>
      exists_iso_quasicoherentIntegralTransform_of_isStalkwiseSplitLeftExact R X Y F hadd hlin
        hsum h₂ h₃

end Main

end AlgebraicGeometry

end
