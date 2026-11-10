module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicTopology.CechNerve
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.CoskeletalAcyclicity

/-!
# Acyclicity of a locally covering augmented simplicial presheaf

Let `C` be a site with Grothendieck topology `J` and let `K` be an augmented simplicial presheaf
of sets on `C`, that is an object of `SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)`.  Write
`K₀ ⟶ G` for the degree-zero component `K.hom.app (op ⦋0⦌)` of the augmentation.  Assume

1. the augmentation `K₀ ⟶ G` is locally surjective,
2. the relation map `K₁ ⟶ K₀ ×_G K₀` is locally surjective,
3. for every `n ≥ 1` the matching map `Kₙ₊₁ ⟶ (cosk_n K)ₙ₊₁` is locally surjective.

This file proves that the homology sheaves of Stacks Project, Tag 01GB then vanish in every
positive degree, and that the degree-zero homology sheaf is the free abelian sheaf `**Z**_G^♯`
on the presheaf of augmentation points.  This is Stacks Project, Tag 01GE.

The homology sheaves are the ones of `StacksFrontier.CategoryTheory.Sites.CechNerveHomology`,
namely `CategoryTheory.SimplicialObject.sheafHomology`, the homology of the alternating face
map complex of the degreewise free abelian sheaf `s(**Z**_K^♯)`.

## Main definitions

* `CategoryTheory.SimplicialObject.Augmented.edgesToFiberProduct` is the relation map
  `(d₀, d₁) : K₁ ⟶ K₀ ×_G K₀` of condition (2); its defining compatibility is naturality of
  the augmentation.
* `CategoryTheory.SimplicialObject.coskSuccToCosk` is the canonical transition
  `cosk_{n+1} K ⟶ cosk_n K` of the coskeleton tower, obtained from the coskeleton adjunction.
* `CategoryTheory.SimplicialObject.Augmented.toCechNerve` is the canonical map from `K.left`
  to the Čech nerve of the degree-zero augmentation, and
  `CategoryTheory.SimplicialObject.Augmented.coskOneToCechNerve` is the induced map out of the
  first coskeleton of `K.left`.
* `CategoryTheory.Arrow.cechNerveOneToPullback` identifies degree one of a Čech nerve with the
  fibre product of two copies of the source.
* `CategoryTheory.SimplicialObject.sheafHomologyCoskIsoCoskOne` and
  `CategoryTheory.SimplicialObject.Augmented.sheafHomologyIsoCechNerve` are the comparison
  isomorphisms on homology sheaves obtained along the coskeleton tower, respectively from `K`
  itself to the Čech nerve of its degree-zero augmentation.

## Main results

* `isZero_sheafHomology_of_isLocallySurjective_matchingMaps`, in the namespace
  `CategoryTheory.SimplicialObject.Augmented`, is the positive-degree vanishing of Tag 01GE.
* `sheafHomologyZeroIso_of_isLocallySurjective_matchingMaps`, in the same namespace, is the
  degree-zero identification of Tag 01GE.
* `CategoryTheory.SimplicialObject.isIso_sheafHomologyFunctor_map_of_isIso_lowDegrees`: a map of
  simplicial presheaves which is an isomorphism through degree `i + 1` induces an isomorphism on
  degree-`i` homology sheaves.
* `CategoryTheory.SimplicialObject.isIso_sheafHomologyFunctor_map_coskSuccToCosk`: a locally
  surjective matching map makes the transition between successive coskeleta an isomorphism on
  homology sheaves.
* `CategoryTheory.SimplicialObject.Augmented.isIso_sheafHomologyFunctor_map_coskOneToCechNerve`:
  local surjectivity of the relation map makes the first coskeleton and the Čech nerve have
  isomorphic homology sheaves.

## Implementation notes

The universes are those of `StacksFrontier.CategoryTheory.Sites.CechNerveHomology`: the site is
`C : Type u` with `Category.{v} C`, and the presheaves of sets take values in `Type w` with `w`
*independent* of `u` and `v`.  This is forced by the statement rather than chosen: nothing here
fixes `w = max u v`, sheafification of type-valued presheaves is never used, and the only
sheafification hypothesis is the one Tag 01GB needs, `HasSheafify J AddCommGrpCat.{w}`.  The
source's phrase "surjective after sheafification" is accordingly expressed by the intrinsic
condition `CategoryTheory.Presheaf.IsLocallySurjective` on the map of presheaves, which keeps
`w` free.

An augmentation is packaged as a `CategoryTheory.SimplicialObject.Augmented`, so the degree-zero
augmentation is `K.hom.app (op ⦋0⦌)` and the presheaf of augmentation points is `K.right`.  The
two conclusions of Tag 01GE are separate declarations, the first stating positive-degree
vanishing via `CategoryTheory.Limits.IsZero` and the second supplying the degree-zero
isomorphism; the latter is a `def` because it produces an isomorphism rather than a proposition.

The proof follows the source.  The comparison with the Čech nerve of the degree-zero
augmentation is assembled from three isomorphisms on homology sheaves: `K.left ⟶ cosk_{i+1}`
from `isIso_sheafHomologyFunctor_map_of_isIso_lowDegrees`, the descent `cosk_{i+1} ⟶ cosk_1`
along the coskeleton tower from the matching-map hypothesis, and `cosk_1 ⟶ cechNerve` from the
relation map.  Each step is an instance of Tag 01GD,
`CategoryTheory.SimplicialObject.isIso_sheafHomologyFunctor_map_of_coskeletal`; the
coskeletality hypotheses it needs come from
`CategoryTheory.SimplicialObject.nonempty_truncCoskAdj_and_isIso_coskAdj_unit_app` and, for the
Čech nerve, from `CategoryTheory.Arrow.cechNerve_isCoskeletal`.

The degree-zero map out of homology is taken to be
`CategoryTheory.Presheaf.cechNerveSheafHomologyZeroAugmentation`, the `homologyMap` of the
augmentation followed by `HomologicalComplex.singleObjHomologySelfIso`.  The equivalent
`homologyι`/`descOpcycles` presentation is available as
`CategoryTheory.Presheaf.cechNerveSheafHomologyZeroAugmentation_eq_homologyι_descOpcycles`, but
is not needed here: the target of the isomorphism is `(Presheaf.freeAbelianSheaf J).obj K.right`,
which is `(presheafToSheaf J AddCommGrpCat.{w}).obj (K.right ⋙ AddCommGrpCat.free)` by
definitional unfolding of `CategoryTheory.Presheaf.freeAbelianSheaf`, so no transport is
required.

## References

* [Stacks Project, Tag 01GB](https://stacks.math.columbia.edu/tag/01GB)
* [Stacks Project, Tag 01GC](https://stacks.math.columbia.edu/tag/01GC)
* [Stacks Project, Tag 01GD](https://stacks.math.columbia.edu/tag/01GD)
* [Stacks Project, Tag 01GE](https://stacks.math.columbia.edu/tag/01GE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- The single projection of a wide pullback of one copy of a morphism of presheaves of sets is
an isomorphism: it is degree zero of a Čech nerve. -/
theorem isIso_widePullback_π_fin_one {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) :
    IsIso (WidePullback.π (fun _ : Fin 1 => f) 0) := by
  let g : F ⟶ (Arrow.mk f).cechNerve.obj (op (SimplexCategory.mk 0)) :=
    WidePullback.lift f (fun _ : Fin 1 => 𝟙 F) (by intro i; fin_cases i; simp)
  refine ⟨g, ?_, ?_⟩
  · apply WidePullback.hom_ext
    · intro i; fin_cases i; simp [g, Category.assoc]
    · simp [g, Category.assoc, WidePullback.π_arrow]
  · simp [g]

end CategoryTheory.Limits

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C]

/-- Degree one of the Čech nerve of a morphism of presheaves of sets `f : F ⟶ G`, compared with
the fibre product of two copies of `F` over `G`.  The two projections are taken in the reverse
order, which is the one matching the face maps `δ 0` and `δ 1`. -/
noncomputable def cechNerveOneToPullback {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) :
    (Arrow.mk f).cechNerve.obj (op (SimplexCategory.mk 1)) ⟶ pullback f f :=
  pullback.lift
    (WidePullback.π (fun _ : Fin 2 => f) 1)
    (WidePullback.π (fun _ : Fin 2 => f) 0)
    (by simp [WidePullback.π_arrow])

/-- The comparison `CategoryTheory.Arrow.cechNerveOneToPullback` is an isomorphism: both sides
are the fibre product `F ×_G F`. -/
theorem isIso_cechNerveOneToPullback {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) :
    IsIso (cechNerveOneToPullback f) := by
  let g : pullback f f ⟶ (Arrow.mk f).cechNerve.obj
      (op (SimplexCategory.mk 1)) :=
    WidePullback.lift (pullback.fst f f ≫ f)
      (fun i : Fin 2 => if i = 0 then pullback.snd f f else pullback.fst f f)
      (by intro i; fin_cases i <;> simp [pullback.condition])
  refine ⟨g, ?_, ?_⟩
  · apply WidePullback.hom_ext
    · intro i
      fin_cases i <;> simp [cechNerveOneToPullback, g, Category.assoc]
    · dsimp [g]
      rw [Category.assoc, WidePullback.lift_base, ← Category.assoc]
      simp only [cechNerveOneToPullback, pullback.lift_fst, WidePullback.π_arrow,
        Category.id_comp]
  · apply pullback.hom_ext <;> simp [cechNerveOneToPullback, g, Category.assoc]

end CategoryTheory.Arrow

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The degree-`j` component of the map of free abelian sheaf complexes induced by a map of
simplicial presheaves which is an isomorphism in degree `j`. -/
theorem isIso_freeAbelianSheafComplexFunctor_map_f (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}]
    {K L : SimplicialObject (Cᵒᵖ ⥤ Type w)} (f : K ⟶ L) (j : ℕ)
    [IsIso (f.app (op (SimplexCategory.mk j)))] :
    IsIso (((freeAbelianSheafComplexFunctor J).map f).f j) := by
  dsimp [freeAbelianSheafComplexFunctor]
  infer_instance

/-- A map of simplicial presheaves that is an isomorphism through degree `i + 1` induces an
isomorphism on degree-`i` homology sheaves: the degrees `i - 1`, `i`, `i + 1` of the two
complexes already agree, and homology in degree `i` only depends on those. -/
theorem isIso_sheafHomologyFunctor_map_of_isIso_lowDegrees (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}]
    {K L : SimplicialObject (Cᵒᵖ ⥤ Type w)} (f : K ⟶ L) (i : ℕ)
    (h : ∀ j : ℕ, j ≤ i + 1 → IsIso (f.app (op (SimplexCategory.mk j)))) :
    IsIso ((sheafHomologyFunctor J i).map f) := by
  let g := (freeAbelianSheafComplexFunctor J).map f
  have hp : IsIso (g.f ((ComplexShape.down ℕ).prev i)) := by
    rw [ChainComplex.prev]
    have := h (i + 1) (le_refl _)
    exact isIso_freeAbelianSheafComplexFunctor_map_f J f (i + 1)
  have hc : IsIso (g.f i) := by
    have := h i (by omega)
    exact isIso_freeAbelianSheafComplexFunctor_map_f J f i
  have hn : IsIso (g.f ((ComplexShape.down ℕ).next i)) := by
    cases i with
    | zero =>
      rw [ChainComplex.next_nat_zero]
      have := h 0 (by omega)
      exact isIso_freeAbelianSheafComplexFunctor_map_f J f 0
    | succ i =>
      rw [ChainComplex.next_nat_succ]
      have := h i (by omega)
      exact isIso_freeAbelianSheafComplexFunctor_map_f J f i
  let φ := (HomologicalComplex.shortComplexFunctor _ (ComplexShape.down ℕ) i).map g
  have hφ₁ : IsIso φ.τ₁ := by
    dsimp [φ, HomologicalComplex.shortComplexFunctor]
    exact hp
  have hφ₂ : IsIso φ.τ₂ := by
    dsimp [φ, HomologicalComplex.shortComplexFunctor]
    exact hc
  have hφ₃ : IsIso φ.τ₃ := by
    dsimp [φ, HomologicalComplex.shortComplexFunctor]
    exact hn
  have : IsIso φ := ShortComplex.isIso_of_isIso φ
  change IsIso ((ShortComplex.homologyFunctor (Sheaf J AddCommGrpCat.{w})).map φ)
  infer_instance

/-- The canonical transition `cosk_{n+1} K ⟶ cosk_n K` of the coskeleton tower.  It is the
adjunct of the inverse of the `n`-truncation of the unit at level `n + 1`, which is an
isomorphism because truncating further forgets the difference. -/
noncomputable def coskSuccToCosk
    (K : SimplicialObject (Cᵒᵖ ⥤ Type w)) (n : ℕ) :
    (SimplicialObject.cosk (n+1)).obj K ⟶ (SimplicialObject.cosk n).obj K := by
  let u := (SimplicialObject.coskAdj (n+1)).unit.app K
  haveI hu : IsIso ((SimplicialObject.truncation n).map u) := by
    change IsIso ((SimplicialObject.Truncated.trunc _ (n+1) n (by omega)).map
      ((SimplicialObject.truncation (n+1)).map u))
    infer_instance
  exact (SimplicialObject.coskAdj n).homEquiv _ _ (inv ((SimplicialObject.truncation n).map u))

/-- The unit of the coskeleton adjunction is an isomorphism in every simplicial degree at
most `n`, since the `n`-truncation of the unit is an isomorphism. -/
theorem isIso_coskAdj_unit_app_app_of_le (K : SimplicialObject (Cᵒᵖ ⥤ Type w))
    (n j : ℕ) (hj : j ≤ n) :
    IsIso (((SimplicialObject.coskAdj n).unit.app K).app
      (op (SimplexCategory.mk j))) :=
  NatIso.isIso_app_of_isIso ((SimplicialObject.truncation n).map
    ((SimplicialObject.coskAdj n).unit.app K))
    (op (⟨SimplexCategory.mk j, hj⟩ : SimplexCategory.Truncated n))

/-- The transition `CategoryTheory.SimplicialObject.coskSuccToCosk` is compatible with the units
of the two coskeleton adjunctions. -/
theorem coskAdj_unit_app_comp_coskSuccToCosk (K : SimplicialObject (Cᵒᵖ ⥤ Type w)) (n : ℕ) :
    (SimplicialObject.coskAdj (n+1)).unit.app K ≫ coskSuccToCosk K n =
      (SimplicialObject.coskAdj n).unit.app K := by
  let a := SimplicialObject.coskAdj (C := Cᵒᵖ ⥤ Type w) n
  let u := (SimplicialObject.coskAdj (n+1)).unit.app K
  have hu : IsIso ((SimplicialObject.truncation n).map u) := by
    change IsIso ((SimplicialObject.Truncated.trunc _ (n+1) n (by omega)).map
      ((SimplicialObject.truncation (n+1)).map u))
    infer_instance
  apply (a.homEquiv K _).symm.injective
  rw [a.homEquiv_naturality_left_symm]
  simp [coskSuccToCosk, a]

/-- If `u ≫ g = t` and `u` and `t` are isomorphisms in degree `j`, then so is `g`. -/
private theorem isIso_app_of_comp_eq_of_isIso {C : Type u} [Category.{v} C]
    {X Y Z : SimplicialObject (Cᵒᵖ ⥤ Type w)} (u : X ⟶ Y) (g : Y ⟶ Z) (t : X ⟶ Z)
    (h : u ≫ g = t) (j : SimplexCategoryᵒᵖ) [IsIso (u.app j)] [IsIso (t.app j)] :
    IsIso (g.app j) := by
  have : IsIso (u.app j ≫ g.app j) := by
    rw [← NatTrans.comp_app, h]
    infer_instance
  exact IsIso.of_isIso_comp_left (u.app j) (g.app j)

/-- If `u ≫ g = t` and `t` is locally surjective in degree `j`, then so is `g`. -/
private theorem isLocallySurjective_app_of_comp_eq {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {X Y Z : SimplicialObject (Cᵒᵖ ⥤ Type w)}
    (u : X ⟶ Y) (g : Y ⟶ Z) (t : X ⟶ Z) (h : u ≫ g = t) (j : SimplexCategoryᵒᵖ)
    [Presheaf.IsLocallySurjective J (t.app j)] : Presheaf.IsLocallySurjective J (g.app j) :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac J (f₁ := u.app j)
    (by rw [← NatTrans.comp_app, h])

/-- A locally surjective matching map makes the transition between successive coskeleta an
isomorphism on every homology sheaf.  This is Tag 01GD applied to
`CategoryTheory.SimplicialObject.coskSuccToCosk`: both coskeleta are `(n+1)`-coskeletal, the
transition is an isomorphism in degrees `< n + 1`, and in degree `n + 1` it is locally surjective
because the unit at level `n` factors through it. -/
theorem isIso_sheafHomologyFunctor_map_coskSuccToCosk (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}]
    (K : SimplicialObject (Cᵒᵖ ⥤ Type w))
    (hmatching : ∀ n : ℕ, 1 ≤ n → Presheaf.IsLocallySurjective J
      (((SimplicialObject.coskAdj n).unit.app K).app
        (op (SimplexCategory.mk (n + 1)))))
    (n i : ℕ) (hn : 1 ≤ n) :
    IsIso ((sheafHomologyFunctor J i).map (coskSuccToCosk K n)) := by
  have hlt : ∀ j : ℕ, j < n+1 →
      IsIso ((coskSuccToCosk K n).app (op (SimplexCategory.mk j))) := by
    intro j hj
    have := isIso_coskAdj_unit_app_app_of_le K (n+1) j (by omega)
    have := isIso_coskAdj_unit_app_app_of_le K n j (by omega)
    exact isIso_app_of_comp_eq_of_isIso _ _ _ (coskAdj_unit_app_comp_coskSuccToCosk K n) _
  have hsurj : Presheaf.IsLocallySurjective J
      ((coskSuccToCosk K n).app (op (SimplexCategory.mk (n+1)))) := by
    have := hmatching n hn
    exact isLocallySurjective_app_of_comp_eq J _ _ _ (coskAdj_unit_app_comp_coskSuccToCosk K n) _
  have hL : IsIso ((SimplicialObject.coskAdj (n+1)).unit.app
      ((SimplicialObject.cosk (n+1)).obj K)) :=
    (SimplicialObject.nonempty_truncCoskAdj_and_isIso_coskAdj_unit_app
      (le_refl (n+1))).2.1 ((SimplicialObject.truncation (n+1)).obj K)
  have hK : IsIso ((SimplicialObject.coskAdj (n+1)).unit.app
      ((SimplicialObject.cosk n).obj K)) :=
    (SimplicialObject.nonempty_truncCoskAdj_and_isIso_coskAdj_unit_app
      (Nat.le_succ n)).2.1 ((SimplicialObject.truncation n).obj K)
  exact isIso_sheafHomologyFunctor_map_of_coskeletal J (coskSuccToCosk K n) (n+1) i
    hlt hsurj hL hK

/-- The canonical isomorphism on degree-`i` homology sheaves from the `m`-th coskeleton to the
first coskeleton, obtained by descending the coskeleton tower one step at a time with
`CategoryTheory.SimplicialObject.isIso_sheafHomologyFunctor_map_coskSuccToCosk`. -/
noncomputable def sheafHomologyCoskIsoCoskOne (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}]
    (K : SimplicialObject (Cᵒᵖ ⥤ Type w))
    (hmatching : ∀ n : ℕ, 1 ≤ n → Presheaf.IsLocallySurjective J
      (((SimplicialObject.coskAdj n).unit.app K).app
        (op (SimplexCategory.mk (n + 1)))))
    (m i : ℕ) (hm : 1 ≤ m) :
    sheafHomology J ((SimplicialObject.cosk m).obj K) i ≅
      sheafHomology J ((SimplicialObject.cosk 1).obj K) i := by
  induction m with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero => exact Iso.refl _
      | succ n =>
          haveI : IsIso ((sheafHomologyFunctor J i).map (coskSuccToCosk K (n + 1))) :=
            isIso_sheafHomologyFunctor_map_coskSuccToCosk J K hmatching (n + 1) i (by omega)
          exact asIso ((sheafHomologyFunctor J i).map (coskSuccToCosk K (n + 1))) ≪≫
            ih (by omega)

end CategoryTheory.SimplicialObject

namespace CategoryTheory.SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]

/-- The relation map `(d₀, d₁) : K₁ ⟶ K₀ ×_G K₀` of an augmented simplicial presheaf.  Both
face maps are compatible with the augmentation by naturality, which is what defines the map into
the fibre product. -/
noncomputable def edgesToFiberProduct
    (K : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) :
    K.left.obj (op (SimplexCategory.mk 1)) ⟶
      pullback (K.hom.app (op (SimplexCategory.mk 0)))
        (K.hom.app (op (SimplexCategory.mk 0))) :=
  pullback.lift (K.left.δ 0) (K.left.δ 1) (by
    calc
      _ = K.hom.app (op (SimplexCategory.mk 1)) := by
        simpa only [SimplicialObject.δ, Functor.id_obj, Functor.id_map,
          Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, Nat.zero_add] using
            K.hom.naturality (SimplexCategory.δ 0).op
      _ = _ := by
        simpa only [SimplicialObject.δ, Functor.id_obj, Functor.id_map,
          Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, Nat.zero_add] using
            (K.hom.naturality (SimplexCategory.δ 1).op).symm)

/-- The canonical map from an augmented simplicial presheaf to the Čech nerve of its degree-zero
augmentation, characterised by being a section of the degree-zero projection. -/
noncomputable def toCechNerve
    (K : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) :
    K.left ⟶ (Arrow.mk (K.hom.app (op (SimplexCategory.mk 0)))).cechNerve :=
  (SimplicialObject.existsUnique_hom_cechNerve_app_zero_comp_π_eq_id
    K.left K.right K.hom).exists.choose

/-- The defining property of `CategoryTheory.SimplicialObject.Augmented.toCechNerve`: in degree
zero it is a section of the projection. -/
theorem toCechNerve_app_zero_comp_π
    (K : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) :
    (toCechNerve K).app (op (SimplexCategory.mk 0)) ≫
      WidePullback.π _ 0 = 𝟙 _ :=
  (SimplicialObject.existsUnique_hom_cechNerve_app_zero_comp_π_eq_id
    K.left K.right K.hom).exists.choose_spec

/-- In degree one, `CategoryTheory.SimplicialObject.Augmented.toCechNerve` followed by the
projection indexed by `Fin.rev i` is the face map `δ i`.  The reversal is the one relating the
constant maps `⦋0⦌ ⟶ ⦋1⦌` to the face maps. -/
theorem toCechNerve_app_one_comp_π
    (K : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) (i : Fin 2) :
    (toCechNerve K).app (op (SimplexCategory.mk 1)) ≫
      WidePullback.π (fun _ : Fin 2 => K.hom.app (op (SimplexCategory.mk 0)))
        (Fin.rev i) = K.left.δ i := by
  let f := Arrow.mk (K.hom.app (op (SimplexCategory.mk 0)))
  have : f.HasCechPullbacks := ⟨fun _ => inferInstance⟩
  have hmap : f.cechNerve.map (SimplexCategory.δ i).op ≫ Arrow.π₀ f =
      WidePullback.π (fun _ : Fin 2 => f.hom) (Fin.rev i) := by
    rw [show (SimplexCategory.δ i : SimplexCategory.mk 0 ⟶ SimplexCategory.mk 1) =
      SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1)
        (Fin.rev i) from by ext j; fin_cases i <;> fin_cases j <;> rfl]
    exact Arrow.cechNerve_map_const_π₀ f (Fin.rev i)
  calc
    _ = (toCechNerve K).app (op (SimplexCategory.mk 1)) ≫
        f.cechNerve.map (SimplexCategory.δ i).op ≫ Arrow.π₀ f := by
          convert congrArg ((toCechNerve K).app (op (SimplexCategory.mk 1)) ≫ ·)
            hmap.symm using 1
          simp [f, Arrow.mk_hom]
    _ = K.left.δ i ≫ (toCechNerve K).app (op (SimplexCategory.mk 0)) ≫
        Arrow.π₀ f := by
          simpa only [SimplicialObject.δ, Category.assoc] using
            congrArg (fun p => p ≫ Arrow.π₀ f)
              (((toCechNerve K).naturality (SimplexCategory.δ i).op).symm)
    _ = K.left.δ i := by
      simp only [f, Arrow.π₀, toCechNerve_app_zero_comp_π, Category.comp_id]

/-- In degree one, `CategoryTheory.SimplicialObject.Augmented.toCechNerve` composed with the
comparison `CategoryTheory.Arrow.cechNerveOneToPullback` is the relation map
`CategoryTheory.SimplicialObject.Augmented.edgesToFiberProduct`. -/
theorem toCechNerve_app_one_comp_cechNerveOneToPullback
    (K : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) :
    (toCechNerve K).app (op (SimplexCategory.mk 1)) ≫
      Arrow.cechNerveOneToPullback (K.hom.app (op (SimplexCategory.mk 0))) =
      edgesToFiberProduct K := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Arrow.cechNerveOneToPullback, pullback.lift_fst]
    convert toCechNerve_app_one_comp_π K 0 using 1 <;>
      simp [edgesToFiberProduct, Fin.rev]
  · simp only [Category.assoc, Arrow.cechNerveOneToPullback, pullback.lift_snd]
    convert toCechNerve_app_one_comp_π K 1 using 1 <;>
      simp [edgesToFiberProduct, Fin.rev]

/-- If the relation map is locally surjective then so is
`CategoryTheory.SimplicialObject.Augmented.toCechNerve` in degree one, since the two differ by
the isomorphism `CategoryTheory.Arrow.cechNerveOneToPullback`. -/
theorem isLocallySurjective_toCechNerve_app_one (J : GrothendieckTopology C)
    (K : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w))
    (h₁ : Presheaf.IsLocallySurjective J (edgesToFiberProduct K)) :
    Presheaf.IsLocallySurjective J
      ((toCechNerve K).app (op (SimplexCategory.mk 1))) := by
  let p := Arrow.cechNerveOneToPullback (K.hom.app (op (SimplexCategory.mk 0)))
  have : IsIso p := Arrow.isIso_cechNerveOneToPullback _
  have : Presheaf.IsLocallyInjective J p := inferInstance
  have : Presheaf.IsLocallySurjective J
      ((toCechNerve K).app (op (SimplexCategory.mk 1)) ≫ p) := by
    rw [show _ = edgesToFiberProduct K from
      toCechNerve_app_one_comp_cechNerveOneToPullback K]
    exact h₁
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective J
    ((toCechNerve K).app (op (SimplexCategory.mk 1))) p

/-- In degree zero, `CategoryTheory.SimplicialObject.Augmented.toCechNerve` is an isomorphism:
it is a section of the degree-zero projection, which is itself an isomorphism. -/
theorem isIso_toCechNerve_app_zero
    (K : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) :
    IsIso ((toCechNerve K).app (op (SimplexCategory.mk 0))) := by
  let f := Arrow.mk (K.hom.app (op (SimplexCategory.mk 0)))
  have : f.HasCechPullbacks := ⟨fun _ => inferInstance⟩
  let p := Arrow.π₀ f
  have : IsIso p := by
    change IsIso (WidePullback.π (fun _ : Fin 1 => K.hom.app
      (op (SimplexCategory.mk 0))) 0)
    exact isIso_widePullback_π_fin_one _
  have heq : (toCechNerve K).app (op (SimplexCategory.mk 0)) ≫ p = 𝟙 _ :=
    toCechNerve_app_zero_comp_π K
  have : IsIso ((toCechNerve K).app (op (SimplexCategory.mk 0)) ≫ p) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_right _ p

/-- The map induced by `CategoryTheory.SimplicialObject.Augmented.toCechNerve` from the first
coskeleton of `K.left` to the Čech nerve of the degree-zero augmentation, using that the Čech
nerve is `1`-coskeletal. -/
noncomputable def coskOneToCechNerve
    (K : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) :
    (SimplicialObject.cosk 1).obj K.left ⟶
      (Arrow.mk (K.hom.app (op (SimplexCategory.mk 0)))).cechNerve := by
  let f := Arrow.mk (K.hom.app (op (SimplexCategory.mk 0)))
  letI : f.HasCechPullbacks := ⟨fun _ => inferInstance⟩
  letI : SimplicialObject.HasCosk₁ (Cᵒᵖ ⥤ Type w) :=
    ⟨fun _ => inferInstance⟩
  haveI : IsIso ((SimplicialObject.coskAdj 1).unit.app f.cechNerve) :=
    Arrow.cechNerve_isCoskeletal f
  exact (SimplicialObject.cosk 1).map (toCechNerve K) ≫
    inv ((SimplicialObject.coskAdj 1).unit.app f.cechNerve)

/-- `CategoryTheory.SimplicialObject.Augmented.coskOneToCechNerve` is compatible with the unit of
the coskeleton adjunction and `CategoryTheory.SimplicialObject.Augmented.toCechNerve`. -/
theorem coskAdj_unit_app_comp_coskOneToCechNerve
    (K : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w)) :
    (SimplicialObject.coskAdj 1).unit.app K.left ≫ coskOneToCechNerve K = toCechNerve K := by
  let f := Arrow.mk (K.hom.app (op (SimplexCategory.mk 0)))
  have : f.HasCechPullbacks := ⟨fun _ => inferInstance⟩
  have : SimplicialObject.HasCosk₁ (Cᵒᵖ ⥤ Type w) :=
    ⟨fun _ => inferInstance⟩
  have : IsIso ((SimplicialObject.coskAdj 1).unit.app f.cechNerve) :=
    Arrow.cechNerve_isCoskeletal f
  have hnat : (SimplicialObject.coskAdj 1).unit.app K.left ≫
      (SimplicialObject.cosk 1).map (toCechNerve K) =
      toCechNerve K ≫ (SimplicialObject.coskAdj 1).unit.app f.cechNerve := by
    simpa only [Functor.id_map, Functor.comp_map] using
      ((SimplicialObject.coskAdj 1).unit.naturality (toCechNerve K)).symm
  change ((SimplicialObject.coskAdj 1).unit.app K.left ≫
    (SimplicialObject.cosk 1).map (toCechNerve K)) ≫
    inv ((SimplicialObject.coskAdj 1).unit.app f.cechNerve) = toCechNerve K
  rw [hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- Local surjectivity of the relation map makes the first coskeleton and the Čech nerve of the
degree-zero augmentation have isomorphic homology sheaves.  This is Tag 01GD applied to
`CategoryTheory.SimplicialObject.Augmented.coskOneToCechNerve`. -/
theorem isIso_sheafHomologyFunctor_map_coskOneToCechNerve (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}]
    (K : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w))
    (h₁ : Presheaf.IsLocallySurjective J (edgesToFiberProduct K))
    (i : ℕ) :
    IsIso ((SimplicialObject.sheafHomologyFunctor J i).map (coskOneToCechNerve K)) := by
  have hlt : ∀ j : ℕ, j < 1 →
      IsIso ((coskOneToCechNerve K).app (op (SimplexCategory.mk j))) := by
    intro j hj
    obtain rfl : j = 0 := by omega
    have := SimplicialObject.isIso_coskAdj_unit_app_app_of_le K.left 1 0 (by omega)
    have := isIso_toCechNerve_app_zero K
    exact SimplicialObject.isIso_app_of_comp_eq_of_isIso _ _ _
      (coskAdj_unit_app_comp_coskOneToCechNerve K) _
  have hsurj : Presheaf.IsLocallySurjective J
      ((coskOneToCechNerve K).app (op (SimplexCategory.mk 1))) := by
    have := isLocallySurjective_toCechNerve_app_one J K h₁
    exact SimplicialObject.isLocallySurjective_app_of_comp_eq J _ _ _
      (coskAdj_unit_app_comp_coskOneToCechNerve K) _
  let f := Arrow.mk (K.hom.app (op (SimplexCategory.mk 0)))
  have : f.HasCechPullbacks := ⟨fun _ => inferInstance⟩
  have : SimplicialObject.HasCosk₁ (Cᵒᵖ ⥤ Type w) :=
    ⟨fun _ => inferInstance⟩
  have hL : IsIso ((SimplicialObject.coskAdj 1).unit.app
      ((SimplicialObject.cosk 1).obj K.left)) :=
    (SimplicialObject.nonempty_truncCoskAdj_and_isIso_coskAdj_unit_app
      (le_refl 1)).2.1 ((SimplicialObject.truncation 1).obj K.left)
  have hK : IsIso ((SimplicialObject.coskAdj 1).unit.app f.cechNerve) :=
    Arrow.cechNerve_isCoskeletal f
  exact SimplicialObject.isIso_sheafHomologyFunctor_map_of_coskeletal J
    (coskOneToCechNerve K) 1 i hlt hsurj hL hK

/-- The canonical isomorphism on homology sheaves from a locally covering augmented simplicial
presheaf to the Čech nerve of its degree-zero augmentation.  It is the composite of the
comparison with the `(i+1)`-st coskeleton, the descent of the coskeleton tower
`CategoryTheory.SimplicialObject.sheafHomologyCoskIsoCoskOne`, and
`CategoryTheory.SimplicialObject.Augmented.coskOneToCechNerve`. -/
noncomputable def sheafHomologyIsoCechNerve (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{w}]
    (K : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w))
    (h₁ : Presheaf.IsLocallySurjective J (edgesToFiberProduct K))
    (hmatching : ∀ n : ℕ, 1 ≤ n → Presheaf.IsLocallySurjective J
      (((SimplicialObject.coskAdj n).unit.app K.left).app
        (op (SimplexCategory.mk (n + 1)))))
    (i : ℕ) :
    SimplicialObject.sheafHomology J K.left i ≅
      SimplicialObject.sheafHomology J
        (Arrow.mk (K.hom.app (op (SimplexCategory.mk 0)))).cechNerve i := by
  haveI : IsIso ((SimplicialObject.sheafHomologyFunctor J i).map
      ((SimplicialObject.coskAdj (i + 1)).unit.app K.left)) := by
    apply SimplicialObject.isIso_sheafHomologyFunctor_map_of_isIso_lowDegrees
    intro j hj
    exact SimplicialObject.isIso_coskAdj_unit_app_app_of_le K.left (i + 1) j hj
  haveI : IsIso ((SimplicialObject.sheafHomologyFunctor J i).map (coskOneToCechNerve K)) :=
    isIso_sheafHomologyFunctor_map_coskOneToCechNerve J K h₁ i
  exact asIso ((SimplicialObject.sheafHomologyFunctor J i).map
      ((SimplicialObject.coskAdj (i + 1)).unit.app K.left)) ≪≫
    SimplicialObject.sheafHomologyCoskIsoCoskOne J K.left hmatching (i + 1) i (by omega) ≪≫
    asIso ((SimplicialObject.sheafHomologyFunctor J i).map (coskOneToCechNerve K))

/-- **Stacks Project, Tag 01GE (positive degrees).** An augmented simplicial presheaf whose
degree-zero augmentation, relation map and matching maps are all locally surjective has zero
homology sheaf in every positive degree. -/
@[stacks 01GE "positive-degree vanishing", sga "4 V 7.3.2" "more general"]
theorem isZero_sheafHomology_of_isLocallySurjective_matchingMaps
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]
    (K : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w))
    (h₀ : Presheaf.IsLocallySurjective J
      (K.hom.app (op (SimplexCategory.mk 0))))
    (h₁ : Presheaf.IsLocallySurjective J (edgesToFiberProduct K))
    (hmatching : ∀ n : ℕ, 1 ≤ n → Presheaf.IsLocallySurjective J
      (((SimplicialObject.coskAdj n).unit.app K.left).app
        (op (SimplexCategory.mk (n + 1)))))
    (i : ℕ) (hi : 0 < i) :
    IsZero (SimplicialObject.sheafHomology J K.left i) :=
  IsZero.of_iso
    (Presheaf.isZero_sheafHomology_cechNerve_of_isLocallySurjective J
      (K.hom.app (op (SimplexCategory.mk 0))) h₀ i hi)
    (sheafHomologyIsoCechNerve J K h₁ hmatching i)

/-- **Stacks Project, Tag 01GE (degree zero).** The degree-zero homology sheaf of an augmented
simplicial presheaf whose degree-zero augmentation, relation map and matching maps are all
locally surjective is the free abelian sheaf on its presheaf of augmentation points. -/
@[stacks 01GE "degree-zero identification"]
noncomputable def sheafHomologyZeroIso_of_isLocallySurjective_matchingMaps
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]
    (K : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w))
    (h₀ : Presheaf.IsLocallySurjective J
      (K.hom.app (op (SimplexCategory.mk 0))))
    (h₁ : Presheaf.IsLocallySurjective J (edgesToFiberProduct K))
    (hmatching : ∀ n : ℕ, 1 ≤ n → Presheaf.IsLocallySurjective J
      (((SimplicialObject.coskAdj n).unit.app K.left).app
        (op (SimplexCategory.mk (n + 1))))) :
    SimplicialObject.sheafHomology J K.left 0 ≅
      (Presheaf.freeAbelianSheaf J).obj K.right :=
  haveI : IsIso (Presheaf.cechNerveSheafHomologyZeroAugmentation J
      (K.hom.app (op (SimplexCategory.mk 0)))) :=
    Presheaf.isIso_cechNerveSheafHomologyZeroAugmentation J
      (K.hom.app (op (SimplexCategory.mk 0))) h₀
  sheafHomologyIsoCechNerve J K h₁ hmatching 0 ≪≫
    asIso (Presheaf.cechNerveSheafHomologyZeroAugmentation J
      (K.hom.app (op (SimplexCategory.mk 0))))

end CategoryTheory.SimplicialObject.Augmented

end
