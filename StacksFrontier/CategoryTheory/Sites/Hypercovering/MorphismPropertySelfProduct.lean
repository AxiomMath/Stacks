module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.MorphismProperty
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal
public import Mathlib.AlgebraicTopology.CechNerve

/-!
# Augmented self-product simplicial objects are hypercoverings

Let `P` be a property of morphisms of a category `C` with fibre products which contains the
isomorphisms. An augmented simplicial object `a : U ⟶ X` whose term `U_n` is, over `X`, the
product of `n + 1` copies of `U_0`, with the simplicial structure acting on coordinates (the
Čech nerve of `a_0 : U_0 ⟶ X`, in any model), is a `P`-hypercovering as soon as `a_0` belongs to
`P`: its canonical degree-one morphism `U_1 ⟶ U_0 ×_X U_0` and its higher matching morphisms are
isomorphisms, because over `X` it is the `0`-coskeleton of `U_0` (Stacks 0182).

The hypotheses are product cones over `X` on the terms, not a chosen model of the Čech nerve, so
that the result applies to the base change of a Čech nerve without identifying it with the Čech
nerve of the base-changed morphism.

## Main results

* `CategoryTheory.SimplicialObject.Augmented.isCoskeletal_over_of_isLimit_fan`: such an augmented
  simplicial object is `0`-coskeletal over `X`.
* `CategoryTheory.MorphismProperty.isHypercovering_of_isLimit_fan`: it is a `P`-hypercovering as
  soon as `a_0` belongs to `P`.

## References

* [Stacks Project, Tag 0182](https://stacks.math.columbia.edu/tag/0182)
* [Stacks Project, Tag 0DER](https://stacks.math.columbia.edu/tag/0DER)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open CategoryTheory.SimplicialObject.Truncated

namespace CategoryTheory

namespace SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C] (A : SimplicialObject.Augmented C)
  (π : ∀ n : ℕ, Fin (n + 1) → (A.left.obj (op ⦋n⦌) ⟶ A.left.obj (op ⦋0⦌)))
  (hπa : ∀ (n : ℕ) (i : Fin (n + 1)),
    π n i ≫ A.hom.app (op ⦋0⦌) = A.hom.app (op ⦋n⦌))

/-- The coordinate projections of a self-product augmented simplicial object, as morphisms over
the point of the augmentation. -/
def overProj (n : ℕ) (i : Fin (n + 1)) :
    A.over.obj (op ⦋n⦌) ⟶ A.over.obj (op ⦋0⦌) :=
  Over.homMk (π n i) (hπa n i)

/-- The underlying morphism of `CategoryTheory.SimplicialObject.Augmented.overProj`. -/
@[simp]
theorem overProj_left (n : ℕ) (i : Fin (n + 1)) : (A.overProj π hπa n i).left = π n i :=
  rfl

variable (hU : ∀ n : ℕ, IsLimit (Fan.mk (A.over.obj (op ⦋n⦌)) (A.overProj π hπa n)))
  (hπ : ∀ {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)),
    A.left.map φ.op ≫ π n i = π m (φ.toOrderHom i))

include hU in
/-- Two morphisms into a term of a self-product augmented simplicial object agree when they
agree over the point of the augmentation and after every coordinate projection. -/
theorem hom_ext_of_isLimit_fan {n : ℕ} {Q : C} {g h : Q ⟶ A.left.obj (op ⦋n⦌)}
    (hb : g ≫ A.hom.app (op ⦋n⦌) = h ≫ A.hom.app (op ⦋n⦌))
    (hi : ∀ i, g ≫ π n i = h ≫ π n i) : g = h := by
  have := (hU n).hom_ext (f := (Over.homMk g rfl : Over.mk (g ≫ A.hom.app (op ⦋n⦌)) ⟶
      A.over.obj (op ⦋n⦌)))
    (f' := Over.homMk h hb.symm) fun j => by
      refine Over.OverMorphism.ext ?_
      show g ≫ π n j.as = h ≫ π n j.as
      exact hi j.as
  exact congrArg CommaMorphism.left this

include hU in
/-- A family of morphisms to the degree-zero term agreeing over the point of the augmentation
lifts to the degree-`n` term of a self-product augmented simplicial object. -/
theorem exists_lift_of_isLimit_fan (n : ℕ) {Q : C} (b : Q ⟶ A.right)
    (s : Fin (n + 1) → (Q ⟶ A.left.obj (op ⦋0⦌))) (hs : ∀ i, s i ≫ A.hom.app (op ⦋0⦌) = b) :
    ∃ ℓ : Q ⟶ A.left.obj (op ⦋n⦌), ℓ ≫ A.hom.app (op ⦋n⦌) = b ∧ ∀ i, ℓ ≫ π n i = s i := by
  let ℓ := (hU n).lift (Fan.mk (Over.mk b) fun i => Over.homMk (s i) (hs i))
  exact ⟨ℓ.left, Over.w ℓ, fun i => congrArg CommaMorphism.left
    ((hU n).fac (Fan.mk (Over.mk b) fun i => Over.homMk (s i) (hs i)) ⟨i⟩)⟩

include hU in
/-- The degree-zero coordinate projection of a self-product augmented simplicial object is an
isomorphism: a product of one copy of `U_0` is `U_0`. -/
theorem isIso_π_zero_of_isLimit_fan : IsIso (π 0 0) := by
  obtain ⟨ℓ, hℓb, hℓ⟩ := A.exists_lift_of_isLimit_fan π hπa hU 0 (A.hom.app (op ⦋0⦌))
    (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  refine ⟨ℓ, ?_, hℓ 0⟩
  refine A.hom_ext_of_isLimit_fan π hπa hU ?_ fun i => ?_
  · rw [Category.assoc, hℓb, hπa, Category.id_comp]
  · obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    simp [hℓ 0]

/-- The `0`-truncated simplex category has a single object. -/
theorem truncZero_eq (x y : SimplexCategory.Truncated 0) : x = y := by
  apply ObjectProperty.FullSubcategory.ext
  rw [← SimplexCategory.mk_len x.obj, ← SimplexCategory.mk_len y.obj,
    Nat.le_zero.mp x.2, Nat.le_zero.mp y.2]

include hU hπ in
/-- **A self-product augmented simplicial object is `0`-coskeletal over the point of its
augmentation** (Stacks 0182): over `X`, the term `U_n` is the product of `n + 1` copies of
`U_0`, so a morphism of simplicial objects over `X` into it is determined by its degree-zero
component. -/
theorem isCoskeletal_over_of_isLimit_fan [HasPullbacks C] : A.over.IsCoskeletal 0 := by
  let K := A.over
  let π' : ∀ n : ℕ, Fin (n + 1) → (K.obj (op ⦋n⦌) ⟶ K.obj (op ⦋0⦌)) := A.overProj π hπa
  have hπ' : ∀ {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)),
      K.map φ.op ≫ π' n i = π' m (φ.toOrderHom i) := by
    intro n m φ i
    ext
    exact hπ φ i
  have hbij (G : SimplicialObject (Over A.right)) :
      Function.Bijective (fun g : G ⟶ K ↦ g.app (op ⦋0⦌) ≫ π' 0 0) :=
    SimplicialObject.bijective_app_zero_comp_π π' hU hπ' G
  have hiso : IsIso (π' 0 0) :=
    (isIso_iff_of_reflects_iso _ (Over.forget A.right)).mp (A.isIso_π_zero_of_isLimit_fan π hπa hU)
  let L := (SimplexCategory.Truncated.inclusion 0).op
  let z₀ : (SimplexCategory.Truncated 0)ᵒᵖ := op ⟨⦋0⦌, by simp⟩
  have hz : ∀ z : (SimplexCategory.Truncated 0)ᵒᵖ, z = z₀ := fun z =>
    congrArg op (truncZero_eq z.unop z₀.unop)
  have hα (G : SimplicialObject (Over A.right)) :
      Function.Bijective (fun g : G ⟶ K ↦ Functor.whiskerLeft L g ≫ 𝟙 (L ⋙ K)) := by
    constructor
    · intro g h hEq
      apply (hbij G).injective
      have h0 := congrArg (fun η ↦ η.app z₀) hEq
      simpa [L, z₀] using congrArg (fun q ↦ q ≫ π' 0 0) h0
    · intro η
      obtain ⟨g, hg⟩ := (hbij G).surjective (η.app z₀ ≫ π' 0 0)
      have hg0 : g.app (op ⦋0⦌) = η.app z₀ := (cancel_mono (π' 0 0)).1 hg
      refine ⟨g, ?_⟩
      apply NatTrans.ext
      funext z
      obtain rfl := hz z
      simpa [L, z₀] using hg0
  refine ⟨⟨⟨IsTerminal.ofUniqueHom
    (fun E ↦ CostructuredArrow.homMk ((Equiv.ofBijective _ (hα E.left)).symm E.hom)
      ((Equiv.ofBijective _ (hα E.left)).apply_symm_apply E.hom))
    fun E φ ↦ CostructuredArrow.hom_ext _ _ <| (hα E.left).injective <|
      (CostructuredArrow.w φ).trans
        ((Equiv.ofBijective _ (hα E.left)).apply_symm_apply E.hom).symm⟩⟩⟩

section Vertex

variable {C : Type u} [Category.{v} C] (A : SimplicialObject.Augmented C)

/-- The vertex maps `U_n ⟶ U_0` of an augmented simplicial object, induced by the maps
`⦋0⦌ ⟶ ⦋n⦌` with value `i`. -/
abbrev vertexMap (n : ℕ) (i : Fin (n + 1)) : A.left.obj (op ⦋n⦌) ⟶ A.left.obj (op ⦋0⦌) :=
  A.left.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op

/-- The vertex maps lie over the point of the augmentation. -/
theorem vertexMap_comp_hom (n : ℕ) (i : Fin (n + 1)) :
    A.vertexMap n i ≫ A.hom.app (op ⦋0⦌) = A.hom.app (op ⦋n⦌) := by
  simp

/-- The simplicial structure maps act on the vertex maps by their action on vertices. -/
theorem map_comp_vertexMap {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) :
    A.left.map φ.op ≫ A.vertexMap n i = A.vertexMap m (φ.toOrderHom i) := by
  rw [← A.left.map_comp, ← op_comp, SimplexCategory.const_comp]

end Vertex

end SimplicialObject.Augmented

section CechNerve

variable {C : Type u} [Category.{v} C] (f : Arrow C)
  [∀ n : ℕ, HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]

/-- A vertex map of the Čech nerve, followed by the unique coordinate of the degree-zero term,
is the coordinate of the vertex. -/
@[reassoc]
theorem Arrow.augmentedCechNerve_vertexMap_π (n : ℕ) (i : Fin (n + 1)) :
    f.augmentedCechNerve.vertexMap n i ≫
        WidePullback.π (fun _ : Fin 1 => f.hom) 0 =
      WidePullback.π (fun _ : Fin (n + 1) => f.hom) i := by
  show f.cechNerve.map _ ≫ _ = _
  simp [Arrow.cechNerve_map, WidePullback.lift_π, SimplexCategory.const_apply]

/-- **The terms of the Čech nerve of `f : U ⟶ X` are, over `X`, the self-products of its
degree-zero term**, through the vertex maps. -/
def Arrow.isLimitVertexFanAugmentedCechNerve (n : ℕ) :
    IsLimit (Fan.mk (f.augmentedCechNerve.over.obj (op ⦋n⦌))
      (f.augmentedCechNerve.overProj f.augmentedCechNerve.vertexMap
        f.augmentedCechNerve.vertexMap_comp_hom n)) := by
  haveI : ∀ k : ℕ, HasWidePullback f.augmentedCechNerve.right
      (fun _ : Fin (k + 1) => f.left) fun _ => f.hom := fun k =>
    (inferInstance : HasWidePullback f.right (fun _ : Fin (k + 1) => f.left) fun _ => f.hom)
  have hw : ∀ (s : Fan fun _ : Fin (n + 1) => f.augmentedCechNerve.over.obj (op ⦋0⦌))
      (i : Fin (n + 1)),
      ((s.proj i).left ≫ WidePullback.π (fun _ : Fin 1 => f.hom) 0) ≫ f.hom = s.pt.hom :=
    fun s i => (Category.assoc _ _ _).trans
      ((congrArg _ (WidePullback.π_arrow _ _)).trans (Over.w (s.proj i)))
  let ℓ : ∀ s : Fan fun _ : Fin (n + 1) => f.augmentedCechNerve.over.obj (op ⦋0⦌),
      s.pt.left ⟶ widePullback f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom :=
    fun s => WidePullback.lift s.pt.hom
      (fun i => (s.proj i).left ≫ WidePullback.π (fun _ : Fin 1 => f.hom) 0) (hw s)
  have hℓb : ∀ s, ℓ s ≫ WidePullback.base (fun _ : Fin (n + 1) => f.hom) = s.pt.hom :=
    fun s => WidePullback.lift_base _ _ _ _
  have hℓπ : ∀ s i, ℓ s ≫ WidePullback.π (fun _ : Fin (n + 1) => f.hom) i =
      (s.proj i).left ≫ WidePullback.π (fun _ : Fin 1 => f.hom) 0 :=
    fun s i => WidePullback.lift_π _ _ _ _ _
  refine mkFanLimit _ (fun s => Over.homMk (ℓ s) (hℓb s)) (fun s i => ?_) (fun s m hm => ?_)
  · refine Over.OverMorphism.ext ?_
    change ℓ s ≫ f.augmentedCechNerve.vertexMap n i = (s.proj i).left
    apply WidePullback.hom_ext
    · intro j
      obtain rfl : j = 0 := Fin.fin_one_eq_zero j
      exact (Category.assoc _ _ _).trans ((congrArg (ℓ s ≫ ·)
        (Arrow.augmentedCechNerve_vertexMap_π f n i)).trans (hℓπ s i))
    · exact (Category.assoc _ _ _).trans ((congrArg (ℓ s ≫ ·)
        (f.augmentedCechNerve.vertexMap_comp_hom n i)).trans
          ((hℓb s).trans (Over.w (s.proj i)).symm))
  · refine Over.OverMorphism.ext ?_
    change m.left = ℓ s
    apply WidePullback.hom_ext
    · intro i
      calc m.left ≫ WidePullback.π (fun _ : Fin (n + 1) => f.hom) i
          = m.left ≫ (f.augmentedCechNerve.vertexMap n i ≫
              WidePullback.π (fun _ : Fin 1 => f.hom) 0) :=
            congrArg (m.left ≫ ·) (Arrow.augmentedCechNerve_vertexMap_π f n i).symm
        _ = (m.left ≫ f.augmentedCechNerve.vertexMap n i) ≫
              WidePullback.π (fun _ : Fin 1 => f.hom) 0 := (Category.assoc _ _ _).symm
        _ = (s.proj i).left ≫ WidePullback.π (fun _ : Fin 1 => f.hom) 0 :=
            congrArg (· ≫ WidePullback.π (fun _ : Fin 1 => f.hom) 0)
              (congrArg CommaMorphism.left (hm i))
        _ = _ := (hℓπ s i).symm
    · exact (Over.w m).trans (hℓb s).symm

end CechNerve

section Hypercovering

variable {C : Type u} [Category.{v} C] [HasPullbacks C] (P : MorphismProperty C)
  [P.RespectsIso] [P.ContainsIdentities] (A : SimplicialObject.Augmented C)
  (π : ∀ n : ℕ, Fin (n + 1) → (A.left.obj (Opposite.op ⦋n⦌) ⟶ A.left.obj (Opposite.op ⦋0⦌)))
  (hπa : ∀ (n : ℕ) (i : Fin (n + 1)),
    π n i ≫ A.hom.app (Opposite.op ⦋0⦌) = A.hom.app (Opposite.op ⦋n⦌))
  (hU : ∀ n : ℕ, IsLimit (Fan.mk (A.over.obj (Opposite.op ⦋n⦌)) (A.overProj π hπa n)))
  (hπ : ∀ {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)),
    A.left.map φ.op ≫ π n i = π m (φ.toOrderHom i))

include hU hπ in
/-- **A self-product augmented simplicial object is a `P`-hypercovering** (Stacks 0DER) as soon
as its degree-zero augmentation belongs to `P`, for a property `P` containing the
isomorphisms: the canonical degree-one morphism and the higher matching morphisms are
isomorphisms, the object being `0`-coskeletal over the point of its augmentation. -/
theorem MorphismProperty.isHypercovering_of_isLimit_fan (h₀ : P (A.hom.app (Opposite.op ⦋0⦌))) :
    P.IsHypercovering A where
  map_zero := h₀
  map_one := by
    have hiso := A.isIso_π_zero_of_isLimit_fan π hπa hU
    have hδ1 : A.left.δ 1 ≫ π 0 0 = π 1 0 := hπ (SimplexCategory.δ 1) 0
    have hδ0 : A.left.δ 0 ≫ π 0 0 = π 1 1 := hπ (SimplexCategory.δ 0) 0
    have hnat : A.left.δ 1 ≫ A.hom.app (Opposite.op ⦋0⦌) = A.hom.app (Opposite.op ⦋1⦌) := by
      simp [SimplicialObject.δ]
    obtain ⟨ℓ, hℓb, hℓ⟩ := A.exists_lift_of_isLimit_fan π hπa hU 1
      (pullback.fst (A.hom.app (Opposite.op ⦋0⦌)) (A.hom.app (Opposite.op ⦋0⦌)) ≫
        A.hom.app (Opposite.op ⦋0⦌))
      ![pullback.fst (A.hom.app (Opposite.op ⦋0⦌)) (A.hom.app (Opposite.op ⦋0⦌)) ≫ π 0 0,
        pullback.snd (A.hom.app (Opposite.op ⦋0⦌)) (A.hom.app (Opposite.op ⦋0⦌)) ≫ π 0 0]
      (fun i => by
        fin_cases i
        · simp [hπa]
        · simp [hπa, pullback.condition])
    have : IsIso (SimplicialObject.Augmented.firstMatchingArrow A).hom := by
      refine ⟨ℓ, ?_, ?_⟩
      · refine A.hom_ext_of_isLimit_fan π hπa hU ?_ fun i => ?_
        · rw [Category.assoc, hℓb, Category.id_comp,
            SimplicialObject.Augmented.firstMatchingArrow_hom_fst_assoc, hnat]
        · rw [Category.assoc, hℓ, Category.id_comp]
          fin_cases i
          · simpa [SimplicialObject.Augmented.firstMatchingArrow_hom_fst_assoc] using hδ1
          · simpa [SimplicialObject.Augmented.firstMatchingArrow_hom_snd_assoc] using hδ0
      · apply pullback.hom_ext
        · simp only [Category.assoc, Category.id_comp,
            SimplicialObject.Augmented.firstMatchingArrow_hom_fst]
          exact (cancel_mono (π 0 0)).1 (by rw [Category.assoc, hδ1]; exact hℓ 0)
        · simp only [Category.assoc, Category.id_comp,
            SimplicialObject.Augmented.firstMatchingArrow_hom_snd]
          exact (cancel_mono (π 0 0)).1 (by rw [Category.assoc, hδ0]; exact hℓ 1)
    exact P.of_isIso _
  matching n _ := by
    have : HasFiniteLimits (Over A.right) := hasFiniteLimits_of_hasTerminal_and_pullbacks
    have : ∀ k : ℕ, ∀ F : SimplicialObject.Truncated (Over A.right) k,
        (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F := by
      intro k F
      rcases k with _ | k
      · exact (hasPointwiseRightKanExtension_of_hasBinaryProducts_or_hasFiniteConnectedLimits
          (C := Over A.right)).1 inferInstance F
      · exact (hasPointwiseRightKanExtension_of_hasBinaryProducts_or_hasFiniteConnectedLimits
          (C := Over A.right)).2 (fun _ ↦ inferInstance) (k + 1) (by omega) F
    have hn : IsIso ((SimplicialObject.coskAdj n).unit.app A.over) :=
      (SimplicialObject.nonempty_truncCoskAdj_and_isIso_coskAdj_unit_app
        (Nat.zero_le n)).2.2 _ ((SimplicialObject.isCoskeletal_iff_isIso _ 0).mp
          (A.isCoskeletal_over_of_isLimit_fan π hπa hU hπ))
    have : IsIso (SimplicialObject.Augmented.matchingArrow A n).hom := by
      show IsIso ((Over.forget A.right).map
        (((SimplicialObject.coskAdj n).unit.app A.over).app (Opposite.op ⦋n + 1⦌)))
      infer_instance
    exact P.of_isIso _

/-- **An augmented simplicial object whose terms are, over the point of the augmentation, the
self-products of `U_0` through the vertex maps is a `P`-hypercovering** as soon as its
degree-zero augmentation belongs to `P`:
`CategoryTheory.MorphismProperty.isHypercovering_of_isLimit_fan`
with the vertex maps as coordinate projections. -/
theorem MorphismProperty.isHypercovering_of_isLimit_vertexFan
    (hV : ∀ n : ℕ, IsLimit (Fan.mk (A.over.obj (Opposite.op ⦋n⦌))
      (A.overProj A.vertexMap A.vertexMap_comp_hom n)))
    (h₀ : P (A.hom.app (Opposite.op ⦋0⦌))) : P.IsHypercovering A :=
  P.isHypercovering_of_isLimit_fan A A.vertexMap A.vertexMap_comp_hom hV
    (fun φ i => A.map_comp_vertexMap φ i) h₀

end Hypercovering

end CategoryTheory

end
