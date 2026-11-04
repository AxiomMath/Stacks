module

public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import
  StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedFullyFaithfulDerivedHom

/-!
# The endomorphism algebra of a K-injective complex computes its Ext groups

Let `(C, O)` be a ringed site, let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded algebra. If `K` is
K-injective, then

`Hom_{D(E, d)}(E, E[n]) ⟶ Hom_{D(O)}(E ⊗_E^𝐋 K, (E ⊗_E^𝐋 K)[n]) = Ext^n_{D(O)}(K, K)`,

the map induced by the derived tensor product `- ⊗_E^𝐋 K` of Tag 09LX, is bijective for every
`n`. This is hypothesis (2) of Tag 09LZ, "`E` computes the ext groups of `K`", and the step
"since `K^•` is K-injective we have `H^n(E) = Ext^n(K^•, K^•)`" of the proof of Tag 09M5.

## Main results

* `CategoryTheory.Adjunction.isIso_unit_app_of_injective_natural`: a Yoneda argument. If `A`
  corepresents, through an injective natural map, the functor `Hom(B, -)` composed with the right
  adjoint, and `A ≅ R B` is sent to the identity of `B`, then the unit of the adjunction is
  invertible at `A`.
* `AlgebraicGeometry.RingedSite.isIso_tensorWithComplexDG_adjunction_unit_app_rep`: the unit of
  the differential graded tensor-Hom adjunction of Tag 09LV is invertible at `Hom(K, K)`.
* `AlgebraicGeometry.RingedSite.isIso_tensorWithComplexDerived_adj_unit_app_repRegularDerived`:
  the unit of the derived adjunction of Tag 09LY is invertible at the regular module, as soon as
  `K` is K-injective.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_map_bijective_of_isKInjective`: the
  bijectivity above.

## Implementation notes

The unit of the differential graded adjunction is not given by a formula: the adjunction is a
field of `AlgebraicGeometry.RingedSite.TensorWithComplexData`. It is identified at `Hom(K, K)` by
the Yoneda argument, using only the structure of the representable functor `Hom(K, -)`
(`DGCategory.HomRepresentation`): a closed degree-zero homomorphism of differential graded
modules out of `Hom(K, K)` is determined by its value at the identity of `K`, and that value is
a closed degree-zero morphism out of `K`. The unit is then carried along the identifications of
Tag 09LC to complexes, along the quotient to homotopy categories, and to the derived categories
through `CategoryTheory.Adjunction.derivedη_fac_app`, where the two comparison maps of the
derived functors are invertible at `Hom(K, K)` (a module orthogonal on the left to the acyclic
modules) and at `K` (a K-injective complex) respectively.

## References

* [Stacks Project, Tag 09LZ](https://stacks.math.columbia.edu/tag/09LZ)
* [Stacks Project, Tag 09M5](https://stacks.math.columbia.edu/tag/09M5)
* [Stacks Project, Tag 09LY](https://stacks.math.columbia.edu/tag/09LY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DifferentialGradedModule

namespace CategoryTheory

namespace Adjunction

/-- **A Yoneda criterion for the unit of an adjunction to be invertible.** Let `L ⊣ R`, let
`A` be an object of the source of `L` and `B` one of its target, and let
`θ : Hom(A, R Y) → Hom(B, Y)` be natural in `Y` and injective at `Y = L A`. If some isomorphism
`γ : A ≅ R B` is sent by `θ` to the identity of `B`, then the unit of the adjunction is
invertible at `A`. -/
theorem isIso_unit_app_of_injective_natural {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {A : C} {B : D}
    (θ : ∀ Y : D, (A ⟶ R.obj Y) → (B ⟶ Y))
    (hθ : ∀ {Y Y' : D} (f : A ⟶ R.obj Y) (g : Y ⟶ Y'), θ Y' (f ≫ R.map g) = θ Y f ≫ g)
    (hinj : Function.Injective (θ (L.obj A)))
    (γ : A ≅ R.obj B) (hγ : θ B γ.hom = 𝟙 B) : IsIso (adj.unit.app A) := by
  let β : B ⟶ L.obj A := θ (L.obj A) (adj.unit.app A)
  let δ : L.obj A ⟶ B := (adj.homEquiv A B).symm γ.hom
  have h₁ : adj.unit.app A ≫ R.map δ = γ.hom := (adj.homEquiv A B).apply_symm_apply γ.hom
  have hβδ : β ≫ δ = 𝟙 B := by
    show θ (L.obj A) (adj.unit.app A) ≫ δ = 𝟙 B
    rw [← hθ, h₁, hγ]
  have hu : adj.unit.app A = γ.hom ≫ R.map β := hinj (by
    rw [hθ, hγ, Category.id_comp])
  have hδβ : δ ≫ β = 𝟙 (L.obj A) := by
    apply (adj.homEquiv A (L.obj A)).injective
    rw [Adjunction.homEquiv_id]
    apply hinj
    show θ (L.obj A) (adj.unit.app A ≫ R.map (δ ≫ β)) = θ (L.obj A) (adj.unit.app A)
    rw [Functor.map_comp, ← Category.assoc, h₁, hθ, hγ, Category.id_comp]
  have : IsIso β := ⟨⟨δ, hβδ, hδβ⟩⟩
  rw [hu]
  infer_instance

/-- **The unit of an adjunction is invertible exactly where the left adjoint is bijective on
morphisms out of every object**: in one direction, the left adjoint `L` acts on `Hom(W, Z)` as
postcomposition with the unit at `Z` followed by the adjunction bijection. This is the direction
used: if the unit is invertible at `Z`, then `L` is bijective on `Hom(W, Z)` for every `W`. -/
theorem map_bijective_of_isIso_unit_app {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (W : C) {Z : C} [IsIso (adj.unit.app Z)] :
    Function.Bijective (fun f : W ⟶ Z => L.map f) := by
  have key : (fun f : W ⟶ Z => L.map f) =
      (adj.homEquiv W (L.obj Z)).symm ∘ (fun f : W ⟶ Z => f ≫ adj.unit.app Z) := by
    funext f
    simp [Adjunction.homEquiv_counit]
  rw [key]
  exact (Equiv.bijective _).comp ⟨fun f g h => (cancel_mono (adj.unit.app Z)).1 h,
    fun g => ⟨g ≫ inv (adj.unit.app Z), by simp⟩⟩

end Adjunction

/-- A natural transformation invertible at an object is invertible at every isomorphic one. -/
theorem NatTrans.isIso_app_of_iso_of_isIso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (τ : F ⟶ G) {X Y : C} (e : X ≅ Y) [IsIso (τ.app Y)] : IsIso (τ.app X) := by
  have h : τ.app X = F.map e.hom ≫ τ.app Y ≫ G.map e.inv := by
    rw [← Category.assoc, τ.naturality, Category.assoc, ← G.map_comp, e.hom_inv_id,
      G.map_id, Category.comp_id]
  rw [h]
  infer_instance

namespace Quotient

variable {C : Type*} [Category C] {D : Type*} [Category D]
  (r : HomRel C) (s : HomRel D) {L : C ⥤ D} {R : D ⥤ C}

/-- The unit of an adjunction descended to quotient categories is invertible at the image of an
object at which the unit downstairs is invertible. -/
theorem isIso_adjunctionOfSquares_unit_app {L' : Quotient r ⥤ Quotient s}
    {R' : Quotient s ⥤ Quotient r} (adj : L ⊣ R) (α : L ⋙ functor s ≅ functor r ⋙ L')
    (β : R ⋙ functor r ≅ functor s ⋙ R') (X : C) [IsIso (adj.unit.app X)] :
    IsIso ((adjunctionOfSquares r s adj α β).unit.app ((functor r).obj X)) := by
  dsimp only [adjunctionOfSquares, Adjunction.ofNatIsoLeft, Adjunction.ofNatIsoRight,
    adjunctionLift, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  have hτ : ∀ {F G : Quotient r ⥤ Quotient r} (τ : functor r ⋙ F ⟶ functor r ⋙ G),
      IsIso (τ.app X) → IsIso ((natTransLift r τ).app ((functor r).obj X)) := fun _ h => h
  refine IsIso.comp_isIso' (IsIso.comp_isIso' (hτ _ ?_) inferInstance) inferInstance
  exact (inferInstance : IsIso ((functor r).map (adj.unit.app X)))

end Quotient

end CategoryTheory

namespace AlgebraicGeometry.RingedSite

universe u v w t s

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

/-! ### The differential graded level -/

/-- The identity of `K`, as a closed element of degree zero of `Hom(K, K)`. -/
def repIdentity :
    ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading 0 :=
  ((Rep.{u, v, w, t, s, 0} X ℤ K).moduleHom (liftComplex.{u, v, w, t, s} X K) 0).symm
    ((CompDG.{u, v, w, t, s, 0} X ℤ).id (liftComplex.{u, v, w, t, s} X K))

/-- The element `repIdentity` of `Hom(K, K)` is the identity morphism of `K`. -/
theorem moduleHom_repIdentity :
    (Rep.{u, v, w, t, s, 0} X ℤ K).moduleHom (liftComplex.{u, v, w, t, s} X K) 0
        (repIdentity.{u, v, w, t, s} X K) =
      (CompDG.{u, v, w, t, s, 0} X ℤ).id (liftComplex.{u, v, w, t, s} X K) :=
  LinearEquiv.apply_symm_apply _ _

/-- The identity of `K` is a cocycle of `Hom(K, K)`. -/
theorem d_repIdentity :
    ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj (liftComplex.{u, v, w, t, s} X K)).d
      (repIdentity.{u, v, w, t, s} X K).1 = 0 := by
  have h := (Rep.{u, v, w, t, s, 0} X ℤ K).module_d (liftComplex.{u, v, w, t, s} X K) 0
    (repIdentity.{u, v, w, t, s} X K)
  rw [moduleHom_repIdentity, (CompDG.{u, v, w, t, s, 0} X ℤ).d_id] at h
  exact congrArg Subtype.val
    (((Rep.{u, v, w, t, s, 0} X ℤ K).moduleHom (liftComplex.{u, v, w, t, s} X K)
      (0 + 1)).injective (h.trans (map_zero _).symm))

/-- The value at the identity of `K` of a closed degree-zero homomorphism out of `Hom(K, K)` has
degree zero. -/
theorem repEval_mem (Y : (CompDG.{u, v, w, t, s, 0} X ℤ).Obj)
    (f : (show (dgCategory.{0, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Comp from
          (Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj (liftComplex.{u, v, w, t, s} X K)) ⟶
      (show (dgCategory.{0, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Comp from
          (Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj Y)) :
    f.1.1 (repIdentity.{u, v, w, t, s} X K).1 ∈
      ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj Y).grading 0 :=
  f.1.2.1 0 _ (repIdentity.{u, v, w, t, s} X K).2

/-- Evaluation at the identity of `K`: a closed degree-zero homomorphism of differential graded
modules `Hom(K, K) ⟶ Hom(K, Y)` gives a closed degree-zero morphism `K ⟶ Y`. -/
def repEval (Y : (CompDG.{u, v, w, t, s, 0} X ℤ).Obj)
    (f : (show (dgCategory.{0, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Comp from
          (Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj (liftComplex.{u, v, w, t, s} X K)) ⟶
      (show (dgCategory.{0, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Comp from
          (Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj Y)) :
    (show (CompDG.{u, v, w, t, s, 0} X ℤ).Comp from liftComplex.{u, v, w, t, s} X K) ⟶
      (show (CompDG.{u, v, w, t, s, 0} X ℤ).Comp from Y) :=
  ⟨(Rep.{u, v, w, t, s, 0} X ℤ K).moduleHom Y 0
      ⟨f.1.1 (repIdentity.{u, v, w, t, s} X K).1, repEval_mem.{u, v, w, t, s} X K Y f⟩, by
    have hd : ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj Y).d
        (f.1.1 (repIdentity.{u, v, w, t, s} X K).1) = 0 := by
      have h := LinearMap.congr_fun (congrArg Subtype.val f.2) (repIdentity.{u, v, w, t, s} X K).1
      change ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj Y).d
          (f.1.1 (repIdentity.{u, v, w, t, s} X K).1) -
        DifferentialGraded.gradedSign ℤ 0 • f.1.1
          (((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj (liftComplex.{u, v, w, t, s} X K)).d
            (repIdentity.{u, v, w, t, s} X K).1) = 0 at h
      rwa [d_repIdentity, map_zero, smul_zero, sub_zero] at h
    rw [← (Rep.{u, v, w, t, s, 0} X ℤ K).module_d Y 0]
    refine (congrArg ((Rep.{u, v, w, t, s, 0} X ℤ K).moduleHom Y (0 + 1))
      (Subtype.ext hd : (_ : ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj Y).grading (0 + 1)) =
        0)).trans (map_zero _)⟩

/-- The morphism `repEval Y f` is the value of `f` at the identity of `K`, read as a morphism
`K ⟶ Y`. -/
theorem repEval_val (Y : (CompDG.{u, v, w, t, s, 0} X ℤ).Obj)
    (f : (show (dgCategory.{0, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Comp from
          (Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj (liftComplex.{u, v, w, t, s} X K)) ⟶
      (show (dgCategory.{0, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Comp from
          (Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj Y)) :
    (repEval.{u, v, w, t, s} X K Y f).1 = (Rep.{u, v, w, t, s, 0} X ℤ K).moduleHom Y 0
      ⟨f.1.1 (repIdentity.{u, v, w, t, s} X K).1, repEval_mem.{u, v, w, t, s} X K Y f⟩ :=
  rfl

/-- Evaluation at the identity is natural in the target. -/
theorem repEval_comp {Y Y' : (CompDG.{u, v, w, t, s, 0} X ℤ).Obj}
    (f : (show (dgCategory.{0, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Comp from
          (Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj (liftComplex.{u, v, w, t, s} X K)) ⟶
      (show (dgCategory.{0, max u v w t s, max u v w t s}
        (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Comp from
          (Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj Y))
    (g : (show (CompDG.{u, v, w, t, s, 0} X ℤ).Comp from Y) ⟶
      (show (CompDG.{u, v, w, t, s, 0} X ℤ).Comp from Y')) :
    repEval.{u, v, w, t, s} X K Y' (f ≫ (Rep.{u, v, w, t, s, 0} X ℤ K).functor.onComp.map g) =
      repEval.{u, v, w, t, s} X K Y f ≫ g := by
  obtain ⟨c, hc₁, hc₂⟩ := (Rep.{u, v, w, t, s, 0} X ℤ K).map_comp Y Y' 0 0 0 (by omega) g.1
    ⟨f.1.1 (repIdentity.{u, v, w, t, s} X K).1, repEval_mem.{u, v, w, t, s} X K Y f⟩
  apply Subtype.ext
  rw [repEval_val]
  refine Eq.trans ?_ hc₂
  congr 1
  exact Subtype.ext hc₁.symm

/-- A closed degree-zero homomorphism out of `Hom(K, K)` is determined by its value at the
identity of `K`. -/
theorem repEval_injective (Y : (CompDG.{u, v, w, t, s, 0} X ℤ).Obj) :
    Function.Injective (repEval.{u, v, w, t, s} X K Y) := by
  intro f f' h
  have h₀ : f.1.1 (repIdentity.{u, v, w, t, s} X K).1 =
      f'.1.1 (repIdentity.{u, v, w, t, s} X K).1 :=
    congrArg Subtype.val
      (((Rep.{u, v, w, t, s, 0} X ℤ K).moduleHom Y 0).injective (congrArg Subtype.val h))
  refine Subtype.ext (Subtype.ext (LinearMap.ext fun z => ?_))
  induction z using DirectSum.Decomposition.inductionOn
      ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj (liftComplex.{u, v, w, t, s} X K)).grading with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | @homogeneous i z =>
    let b : (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.grading i :=
      ((Rep.{u, v, w, t, s, 0} X ℤ K).algebraHom i).symm
        ((Rep.{u, v, w, t, s, 0} X ℤ K).moduleHom (liftComplex.{u, v, w, t, s} X K) i z)
    obtain ⟨c, hc₁, hc₂⟩ := (Rep.{u, v, w, t, s, 0} X ℤ K).module_action
      (liftComplex.{u, v, w, t, s} X K) 0 i i (zero_add i) (repIdentity.{u, v, w, t, s} X K) b
    rw [moduleHom_repIdentity, LinearEquiv.apply_symm_apply,
      (CompDG.{u, v, w, t, s, 0} X ℤ).id_comp] at hc₂
    have hcz : c = z :=
      ((Rep.{u, v, w, t, s, 0} X ℤ K).moduleHom (liftComplex.{u, v, w, t, s} X K) i).injective hc₂
    have hz : (z : ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj
        (liftComplex.{u, v, w, t, s} X K)).M) =
        MulOpposite.op (b : (Rep.{u, v, w, t, s, 0} X ℤ K).algebra.A) •
          (repIdentity.{u, v, w, t, s} X K).1 := by
      rw [← hcz, hc₁]
    rw [hz, f.1.2.2, f'.1.2.2, h₀]

/-- The identity of `K` is sent to itself by evaluation at the identity. -/
theorem repEval_id :
    repEval.{u, v, w, t, s} X K (liftComplex.{u, v, w, t, s} X K) (𝟙 _) = 𝟙 _ :=
  Subtype.ext (moduleHom_repIdentity.{u, v, w, t, s} X K)

/-- **The unit of the differential graded tensor-Hom adjunction is invertible at `Hom(K, K)`.**
By the Yoneda criterion `CategoryTheory.Adjunction.isIso_unit_app_of_injective_natural`, applied
to evaluation at the identity of `K`. -/
theorem isIso_tensorWithComplexDG_adjunction_unit_app_rep :
    IsIso ((tensorWithComplexDG.{u, v, w, t, s, 0} X ℤ K).adjunction.unit.app
      ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj (liftComplex.{u, v, w, t, s} X K))) :=
  (tensorWithComplexDG.{u, v, w, t, s, 0} X ℤ K).adjunction.isIso_unit_app_of_injective_natural
    (B := liftComplex.{u, v, w, t, s} X K)
    (repEval.{u, v, w, t, s} X K) (fun f g => repEval_comp.{u, v, w, t, s} X K f g)
    (repEval_injective.{u, v, w, t, s} X K _) (Iso.refl _) (repEval_id.{u, v, w, t, s} X K)

/-! ### Complexes and homotopy categories -/

/-- The unit of the tensor-Hom adjunction on complexes is invertible at `Hom(K, K)`. -/
theorem isIso_tensorWithComplexComplexes_adj_unit_app_rep :
    IsIso ((tensorWithComplexComplexes_adj_homWithComplex.{u, v, w, t, s} X K).unit.app
      ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj (liftComplex.{u, v, w, t, s} X K))) := by
  have h := isIso_tensorWithComplexDG_adjunction_unit_app_rep.{u, v, w, t, s} X K
  dsimp only [tensorWithComplexComplexes_adj_homWithComplex]
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  have h₂ : IsIso ((tensorWithComplexDG.{u, v, w, t, s, 0} X ℤ K).adjunction.unit.app
      ((compModulesEquivalence (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).symm.functor.obj
        ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj (liftComplex.{u, v, w, t, s} X K)))) := h
  simp only [Equivalence.toAdjunction_unit]
  refine IsIso.comp_isIso' (IsIso.comp_isIso' ?_ (Functor.map_isIso _ _))
    (Functor.map_isIso _ _)
  exact (inferInstance : IsIso ((compModulesEquivalence
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).symm.unitIso.hom.app _))

/-- The unit of the tensor-Hom adjunction on homotopy categories is invertible at `Hom(K, K)`. -/
theorem isIso_tensorWithComplexHomotopy_adj_unit_app_rep :
    IsIso ((tensorWithComplexHomotopy_adj_homWithComplexHomotopy.{u, v, w, t, s} X K).unit.app
      ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).obj
        ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj (liftComplex.{u, v, w, t, s} X K)))) := by
  have := isIso_tensorWithComplexComplexes_adj_unit_app_rep.{u, v, w, t, s} X K
  exact CategoryTheory.Quotient.isIso_adjunctionOfSquares_unit_app _ _ _ _ _ _

/-! ### The derived categories -/

/-- The comparison of derived Hom out of `K` with the underived one is invertible at a
K-injective complex. -/
theorem isIso_derivedHomWithComplexUnit_app_of_isKInjective
    (L : CochainComplex (TensorModO.{u, v, w, t, s} X) ℤ) [L.IsKInjective] :
    IsIso ((derivedHomWithComplexUnit.{u, v, w, t, s} X K).app
      ((HomotopyCategory.quotient _ _).obj L)) := by
  have := Functor.hasPointwiseRightDerivedFunctor_of_coresolutions
    (L := DerivedCategory.Qh)
    (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ))
    (homWithComplexToDerivedCategory.{u, v, w, t, s} X K)
    (exists_coresolution_map_bijective_sheaf.{u, v, w, t, s} X)
  exact (Functor.LeftExtension.mk _ (derivedHomWithComplexUnit.{u, v, w, t, s} X K)
    ).isIso_hom_app_of_bijective
    (Functor.isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor
      (derivedHomWithComplex.{u, v, w, t, s} X K)
      (derivedHomWithComplexUnit.{u, v, w, t, s} X K)
      (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)) _)
    (fun Z => CochainComplex.IsKInjective.Qh_map_bijective Z L)

/-- **The unit of the derived adjunction of Tag 09LY is invertible at the regular module** when
`K` is K-injective. This is `CategoryTheory.Adjunction.derivedη_fac_app`: the derived unit at
`Hom(K, K)`, followed by the comparison of the derived tensor product with the ordinary one, is
the unit on homotopy categories followed by the comparison of derived Hom with the ordinary one,
and the three other maps of that square are invertible. -/
theorem isIso_tensorWithComplexDerived_adj_unit_app_repRegularDerived
    [(liftComplex.{u, v, w, t, s} X K).IsKInjective] :
    IsIso ((tensorWithComplexDerived_adj_derivedHomWithComplex.{u, v, w, t, s} X K).unit.app
      (repRegularDerived.{u, v, w, t, s} X K)) := by
  let P := (toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).obj
    ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj (liftComplex.{u, v, w, t, s} X K))
  let eReg : (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.obj P ≅
      repRegularDerived.{u, v, w, t, s} X K :=
    (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.mapIso
      ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).mapIso
        DGCategory.representableSelfIsoRegular)
  suffices h : IsIso ((tensorWithComplexDerived_adj_derivedHomWithComplex.{u, v, w, t, s}
      X K).unit.app ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.obj P)) from
    NatTrans.isIso_app_of_iso_of_isIso _ eReg.symm
  let ε : (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q ⋙
        tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⟶
      tensorWithComplexHomotopy.{u, v, w, t, s, 0} X ℤ K ⋙ DerivedCategory.Qh :=
    tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K
  let η : homWithComplexHomotopy.{u, v, w, t, s} X K ⋙
        (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q ⟶
      DerivedCategory.Qh ⋙ derivedHomWithComplex.{u, v, w, t, s} X K :=
    derivedHomWithComplexUnit.{u, v, w, t, s} X K
  have hα : (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).IsLeftDerivedFunctor ε
      (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) :=
    tensorWithComplexDerived_isLeftDerivedFunctor.{u, v, w, t, s, 0} X ℤ K
  have hβ' : (derivedHomWithComplex.{u, v, w, t, s} X K).IsRightDerivedFunctor η
      (HomotopyCategory.quasiIso (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)) :=
    derivedHomWithComplex_isRightDerivedFunctor.{u, v, w, t, s} X K
  have hleft := Functor.isLeftDerivedFunctor_comp_of_resolutions
    (L := (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q)
    (W := quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) ε
    (derivedHomWithComplex.{u, v, w, t, s} X K)
    (exists_resolution_map_bijective_rep.{u, v, w, t, s} X K)
  have hfac := Adjunction.derivedη_fac_app
    (tensorWithComplexHomotopy_adj_homWithComplexHomotopy.{u, v, w, t, s} X K)
    (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) ε η P
  have hc : IsIso ((tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K).app P) :=
    isIso_tensorWithComplexDerivedCounit_app.{u, v, w, t, s} X K _
      (leftOrthogonal_acyclic_rep_self.{u, v, w, t, s} X K)
  have hη : IsIso ((tensorWithComplexHomotopy_adj_homWithComplexHomotopy.{u, v, w, t, s}
      X K).unit.app P) := isIso_tensorWithComplexHomotopy_adj_unit_app_rep.{u, v, w, t, s} X K
  have hβ : IsIso ((derivedHomWithComplexUnit.{u, v, w, t, s} X K).app
      ((tensorWithComplexHomotopy.{u, v, w, t, s, 0} X ℤ K).obj P)) := by
    have := isIso_derivedHomWithComplexUnit_app_of_isKInjective.{u, v, w, t, s} X K
      (liftComplex.{u, v, w, t, s} X K)
    exact NatTrans.isIso_app_of_iso_of_isIso _
      (tensorWithComplexHomotopyRegularIso.{u, v, w, t, s} X K)
  have hfac' : (tensorWithComplexDerived_adj_derivedHomWithComplex.{u, v, w, t, s}
      X K).unit.app ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.obj P) ≫
      (derivedHomWithComplex.{u, v, w, t, s} X K).map
        ((tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K).app P) =
      (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.map
        ((tensorWithComplexHomotopy_adj_homWithComplexHomotopy.{u, v, w, t, s} X K).unit.app P) ≫
      (derivedHomWithComplexUnit.{u, v, w, t, s} X K).app
        ((tensorWithComplexHomotopy.{u, v, w, t, s, 0} X ℤ K).obj P) := hfac
  have hcomp : IsIso ((tensorWithComplexDerived_adj_derivedHomWithComplex.{u, v, w, t, s}
      X K).unit.app ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.obj P) ≫
      (derivedHomWithComplex.{u, v, w, t, s} X K).map
        ((tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K).app P)) := by
    rw [hfac']
    exact IsIso.comp_isIso' (Functor.map_isIso _ _) hβ
  exact IsIso.of_isIso_comp_right _
    ((derivedHomWithComplex.{u, v, w, t, s} X K).map
      ((tensorWithComplexDerivedCounit.{u, v, w, t, s, 0} X ℤ K).app P))

/-- **`E` computes the ext groups of a K-injective `K`.** For every `n`, the derived tensor
product `- ⊗_E^𝐋 K` of Tag 09LX is bijective from `Hom_{D(E, d)}(E, E[n])` onto
`Hom_{D(O)}(E ⊗_E^𝐋 K, (E ⊗_E^𝐋 K)[n])`. This is hypothesis (2) of Tag 09LZ, discharged from the
K-injectivity of `K`, which is how the proof of Tag 09M5 uses it. -/
theorem tensorWithComplexDerived_map_bijective_of_isKInjective
    [(liftComplex.{u, v, w, t, s} X K).IsKInjective] (n : ℤ) :
    Function.Bijective
      (fun f : repRegularDerived.{u, v, w, t, s} X K ⟶
          (repRegularDerived.{u, v, w, t, s} X K)⟦n⟧ =>
        (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).map f) := by
  let adj := tensorWithComplexDerived_adj_derivedHomWithComplex.{u, v, w, t, s} X K
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have h₀ := isIso_tensorWithComplexDerived_adj_unit_app_repRegularDerived.{u, v, w, t, s} X K
  have : IsIso (adj.unit.app ((repRegularDerived.{u, v, w, t, s} X K)⟦n⟧)) :=
    IsIso.of_isIso_fac_right
      (NatTrans.shift_app_comm adj.unit n (repRegularDerived.{u, v, w, t, s} X K)).symm
  exact adj.map_bijective_of_isIso_unit_app _

end AlgebraicGeometry.RingedSite

end
