module

public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.GroupoidStructure
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveAlgebraicallyClosedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveGeometricTwoArrows
public import StacksFrontier.AlgebraicGeometry.Stacks.FieldValuedPointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineModuliTopology
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Restriction
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMoriEtaleLocal.CartesianCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMoriEtaleLocal.GeometricPoints

/-!
# Geometric points of the moduli spaces of a Keel–Mori cover (Stacks 0DUT)

Let `F : 𝒴 ⟶ N` be a universal homeomorphism from an algebraic stack to (the stack of) an object
`N` of the site, and let `k` be an algebraically closed field, with `V` an object of the site whose
underlying scheme is `Spec k`. Then the isomorphism classes of objects of `𝒴` over `V` map
bijectively to the `V`-points of `N` (Stacks 0CPN and 0DTM): this is the input "Mor(Spec k, 𝒳 i)
→ M i (k) is bijective on isomorphism classes" of the proof of Stacks 0DUT.

Combined with Stacks 0DUC it shows that, for a Keel–Mori cover, the map
`N i j (k) → M i (k) × M j (k)` given by `s i j` and `t i j` is injective, which is what makes
the relation `∐ N i j ⟶ ∐ M i × ∐ M i` a monomorphism.

## Main results

* `AlgebraicGeometry.Stack.bijective_pointsMap_of_universalHomeomorphism`
* `AlgebraicGeometry.Stack.exists_obj_of_universalHomeomorphism`: surjectivity.
* `AlgebraicGeometry.Stack.KeelMoriCover.eq_of_comp_s_eq_of_comp_t_eq`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A universal homeomorphism of algebraic stacks is bijective on points**: it is its own base
change along the identity. -/
theorem bijective_pointsMap_of_universalHomeomorphism {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒴} (hf : UniversalHomeomorphism B S hS f) :
    Function.Bijective (pointsMap B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids
      𝒴.val.isFiberedInGroupoids f.hom.hom) := by
  have h := hf 𝒴 (𝟙 𝒴) (Bicategory.trivialBaseChangeSquare f).swap
    (Bicategory.isTwoFibreProduct_swap (Bicategory.isTwoFibreProduct_trivialBaseChangeSquare f
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f (𝟙 𝒴))))
  exact @IsHomeomorph.bijective _ _ (pointTopology B S hS _) (pointTopology B S hS _) _ h

variable {B S hS}

section UniversalHomeomorphism

variable {𝒴 : AlgebraicStacks.{u, w} B S hS} {N : BigFppfOver B S hS}
  (F : 𝒴 ⟶ algebraicSpaceStack.{u, w} B S hS (yoneda.obj N) (isAlgebraicSpace_yoneda B S hS N))

/-- **Surjectivity over an algebraically closed field.** Every point of an object `N` of the site
with values in the spectrum of an algebraically closed field is the image of an object of `𝒴`
under a universal homeomorphism `𝒴 ⟶ N` (Stacks 0DTM). -/
theorem exists_obj_of_universalHomeomorphism (hF : UniversalHomeomorphism B S hS F)
    (k : Type u) [Field k] [IsAlgClosed k] (V : BigFppfOver B S hS)
    (hV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k)) (n : V ⟶ N) :
    ∃ (x : 𝒴.val.val.obj) (_ : 𝒴.val.val.p.obj x = V),
      F.hom.hom.obj x = (⟨V, Discrete.mk n⟩ : (fibredCategory B S hS (yoneda.obj N)).val.obj) := by
  let y : FieldValuedPoint B S hS
      (algebraicSpaceStack.{u, w} B S hS (yoneda.obj N)
        (isAlgebraicSpace_yoneda B S hS N)).val.val :=
    { carrier := k
      base := V
      isSpec := hV
      obj := ⟨V, Discrete.mk n⟩
      «over» := rfl }
  have : IsAlgClosed y.carrier := inferInstanceAs (IsAlgClosed k)
  obtain ⟨x, ⟨e⟩⟩ := exists_fiber_lift_of_universallyInjective B S hS F
    (universallyInjective_of_universalHomeomorphism B S hS hF) y
    ((bijective_pointsMap_of_universalHomeomorphism B S hS hF).2 _)
  refine ⟨x.1, x.2, ?_⟩
  exact fibredCategory_obj_eq_of_isHomLift_id B S hS
    ((Functor.congr_obj F.hom.hom.w x.1).trans x.2) rfl e.hom.1 e.hom.2

end UniversalHomeomorphism

/-- **Two objects of a fibre of a category fibred in groupoids joined by a morphism over the
identity have the same isomorphism class.** -/
theorem _root_.CategoryTheory.Functor.isoClassMk_eq_of_isHomLift_id {𝒞 𝒮 : Type*} [Category 𝒞]
    [Category 𝒮] (p : 𝒮 ⥤ 𝒞) (hp : p.IsFiberedInGroupoids) {U : 𝒞} (a b : p.Fiber U)
    (α : a.1 ⟶ b.1) (hα : p.IsHomLift (𝟙 U) α) :
    Functor.isoClassMk p a = Functor.isoClassMk p b := by
  have hg : IsGroupoid (p.Fiber U) := hp.fiber_isGroupoid U
  have := hα
  let φ : a ⟶ b := Functor.Fiber.homMk p U α
  have : IsIso φ := hg.all_isIso φ
  exact Functor.isoClassMk_eq_of_iso (asIso φ)

namespace KeelMoriCover

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} (C : KeelMoriCover B S hS 𝒳)

/-- `s i j`, as a 1-morphism of algebraic stacks. -/
noncomputable abbrev sStack (i j : C.ι) :
    algebraicSpaceStack.{u, w} B S hS (yoneda.obj (C.N i j)) (isAlgebraicSpace_yoneda B S hS _) ⟶
      algebraicSpaceStack.{u, w} B S hS (yoneda.obj (C.M i)) (isAlgebraicSpace_yoneda B S hS _) :=
  Bicategory.InducedBicategory.mkHom (associatedMap B S hS (yoneda.map (C.s i j))).1

/-- The moduli square of a pair, as a square of algebraic stacks. -/
noncomputable abbrev squareStack (i j : C.ι) : Bicategory.TwoCommSq (C.sStack i j) (C.f i) :=
  ⟨C.X i j, C.φ i j, C.pr₁ i j, Bicategory.InducedBicategory.isoMk (eqToIso (C.φ_comp_s i j))⟩

/-- The moduli square `squareStack i j` is a 2-fibre product of `sStack i j` and `f i`. -/
noncomputable def isTwoFibreProduct_squareStack (i j : C.ι) :
    Bicategory.IsTwoFibreProduct (C.squareStack i j) :=
  Bicategory.isTwoFibreProduct_of_underlying
    (isTwoFibreProduct_of_eq_of_discrete B S hS _ (C.isTwoFibreProduct_square i j) _)

/-- **The moduli morphism of a pair is a universal homeomorphism**, as a base change of `f i`. -/
theorem universalHomeomorphism_φ (i j : C.ι) : UniversalHomeomorphism B S hS (C.φ i j) :=
  universalHomeomorphism_baseChange B S hS (C.f i) (C.sStack i j)
    (C.chart i).universalHomeomorphism_moduliMap (C.squareStack i j)
    (C.isTwoFibreProduct_squareStack i j)

/-- If an object `x` of `X i j` maps under `φ i j` to the point `n` of `N i j`, then its image
under `pr₁ i j` maps under `f i` to the point `n ≫ s i j` of `M i`. -/
theorem obj_f_pr₁ {i j : C.ι} {V : BigFppfOver B S hS} (x : (C.X i j).val.val.obj)
    (n : V ⟶ C.N i j)
    (hx : (C.φ i j).hom.hom.obj x =
      (⟨V, Discrete.mk n⟩ : (fibredCategory B S hS (yoneda.obj (C.N i j))).val.obj)) :
    (C.f i).hom.hom.obj ((C.pr₁ i j).hom.hom.obj x) =
      (⟨V, Discrete.mk (n ≫ C.s i j)⟩ : (fibredCategory B S hS (yoneda.obj (C.M i))).val.obj) := by
  have c := congrArg (fun G => G.hom.obj x) (C.φ_comp_s i j)
  refine c.symm.trans ?_
  change (associatedMap B S hS (yoneda.map (C.s i j))).1.hom.obj ((C.φ i j).hom.hom.obj x) = _
  rw [hx]
  exact associatedMap_obj B S hS _ _

/-- If an object `x` of `X i j` maps under `φ i j` to the point `n` of `N i j`, then its image
under `pr₂ i j` maps under `f j` to the point `n ≫ t i j` of `M j`. -/
theorem obj_f_pr₂ {i j : C.ι} {V : BigFppfOver B S hS} (x : (C.X i j).val.val.obj)
    (n : V ⟶ C.N i j)
    (hx : (C.φ i j).hom.hom.obj x =
      (⟨V, Discrete.mk n⟩ : (fibredCategory B S hS (yoneda.obj (C.N i j))).val.obj)) :
    (C.f j).hom.hom.obj ((C.pr₂ i j).hom.hom.obj x) =
      (⟨V, Discrete.mk (n ≫ C.t i j)⟩ : (fibredCategory B S hS (yoneda.obj (C.M j))).val.obj) := by
  have c := congrArg (fun G => G.hom.obj x) (C.φ_comp_t i j)
  refine c.symm.trans ?_
  change (associatedMap B S hS (yoneda.map (C.t i j))).1.hom.obj ((C.φ i j).hom.hom.obj x) = _
  rw [hx]
  exact associatedMap_obj B S hS _ _

/-- **`N i j (k) ⟶ M i (k) × M j (k)` is injective** for an algebraically closed field `k`: two
geometric points of `N i j` with the same images under `s i j` and `t i j` come from geometric
points of `𝒳 i ×_𝒳 𝒳 j` with isomorphic components (Stacks 0CPN, 0DTM), which are isomorphic
because `𝒳 j ⟶ 𝒳` induces isomorphisms on automorphism groups (Stacks 0DUC). -/
theorem eq_of_comp_s_eq_of_comp_t_eq {a b : C.ι} (k : Type u) [Field k] [IsAlgClosed k]
    (V : BigFppfOver B S hS) (hV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k))
    (n₁ n₂ : V ⟶ C.N a b) (hs : n₁ ≫ C.s a b = n₂ ≫ C.s a b)
    (ht : n₁ ≫ C.t a b = n₂ ≫ C.t a b) : n₁ = n₂ := by
  obtain ⟨x₁, hx₁, e₁⟩ :=
    exists_obj_of_universalHomeomorphism (C.φ a b) (C.universalHomeomorphism_φ a b) k V hV n₁
  obtain ⟨x₂, hx₂, e₂⟩ :=
    exists_obj_of_universalHomeomorphism (C.φ a b) (C.universalHomeomorphism_φ a b) k V hV n₂
  obtain ⟨α₁, hα₁⟩ := exists_isHomLift_id_of_universalHomeomorphism_algebraicSpace
    (N := C.Msp a) (C.f a) (C.chart a).universalHomeomorphism_moduliMap k V hV _ _
    ((Functor.congr_obj (C.pr₁ a b).hom.hom.w x₁).trans hx₁)
    ((Functor.congr_obj (C.pr₁ a b).hom.hom.w x₂).trans hx₂)
    ((C.obj_f_pr₁ x₁ n₁ e₁).trans (by rw [hs, C.obj_f_pr₁ x₂ n₂ e₂]))
  obtain ⟨α₂, hα₂⟩ := exists_isHomLift_id_of_universalHomeomorphism_algebraicSpace
    (N := C.Msp b) (C.f b) (C.chart b).universalHomeomorphism_moduliMap k V hV _ _
    ((Functor.congr_obj (C.pr₂ a b).hom.hom.w x₁).trans hx₁)
    ((Functor.congr_obj (C.pr₂ a b).hom.hom.w x₂).trans hx₂)
    ((C.obj_f_pr₂ x₁ n₁ e₁).trans (by rw [ht, C.obj_f_pr₂ x₂ n₂ e₂]))
  have hcl := isoClassMk_eq_of_isoClassMk_eq_components B S hS (C.map b) (C.map a) (C.pairSq a b)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (C.map a) (C.map b))
    (C.inducesIso b) k V hV ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
    (Functor.isoClassMk_eq_of_isHomLift_id _ (C.obj a).val.isFiberedInGroupoids _ _ α₁ hα₁)
    (Functor.isoClassMk_eq_of_isHomLift_id _ (C.obj b).val.isFiberedInGroupoids _ _ α₂ hα₂)
  obtain ⟨γ⟩ := Functor.exists_iso_of_isoClassMk_eq hcl
  have hγ : (C.X a b).val.val.p.IsHomLift (𝟙 V) γ.hom.1 := γ.hom.2
  have key := fibredCategory_obj_eq_of_isHomLift_id B S hS
    ((Functor.congr_obj (C.φ a b).hom.hom.w x₁).trans hx₁)
    ((Functor.congr_obj (C.φ a b).hom.hom.w x₂).trans hx₂)
    ((C.φ a b).hom.hom.map γ.hom.1) inferInstance
  rw [e₁, e₂] at key
  injection key with _ h₂
  exact congrArg Discrete.as h₂

end KeelMoriCover

end AlgebraicGeometry.Stack

end
