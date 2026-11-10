module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeFunctoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategoryTriangulated

/-!
# The cone triangle of a morphism is distinguished

Let `X` be a ringed site, let `(A, d)` be a sheaf of differential graded algebras on it and let
`f : K ⟶ L` be a morphism of right differential graded `A`-modules. The cone `C(f)` of
[Stacks, Tag 0FS5] sits in a sequence `L ⟶ C(f) ⟶ K[1]` which is split in the underlying graded
category, and whose connecting arrow is `f[1]`; this file reads that sequence as a distinguished
triangle of the homotopy category `K(Mod(A, d))`.

It also identifies the translation of `K(Mod(A, d))` with the chosen degree-one shift of
tag 0FS5 *on morphisms*, which [Stacks, Tag 0FS7] states only on objects.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.coneRotatedTriangle`: the triangle
  `(L, C(f), K[1], i, p, f[1])` of the cone sequence, in `K(Mod(A, d))`.

## Main results

* `SheafOfModules.DifferentialGradedModule.coneRotatedTriangle_distinguished`: **that triangle is
  distinguished**, which is [Stacks, Tag 09QU] for the concrete cone of tag 0FS5.
* `SheafOfModules.DifferentialGradedModule.cocycleOfHom_coneShiftHom_heq`: the cocycle of the
  morphism of chosen shifts induced by `φ` is the degree-one differential graded shift of the
  cocycle of `φ`.
* `SheafOfModules.DifferentialGradedModule.quotient_map_coneShiftHom`: **the translation of
  `K(Mod(A, d))` agrees with the chosen shift on morphisms**, compatibly with the object-level
  agreement of [Stacks, Tag 0FS7].

## Implementation notes

*How distinguishedness is reached.* The only introduction rule for a distinguished triangle of
`K(Mod(A, d))` is `SheafOfModules.DifferentialGradedModule.HomotopyCategory.distinguished_iff`,
which asks for a `CategoryTheory.DGCategory.GradedSplitShortExact` in the differential graded
category of right differential graded modules together with an identification of the triangle's
third arrow with that sequence's connecting arrow. The sequence is
`SheafOfModules.DifferentialGradedModule.exists_coneSequence`, the degreewise direct-sum
decomposition of the mapping cone, which is the same datum that the proof of axiom (C)
(`SheafOfModules.DifferentialGradedModule.coneSituation`, tag 0FS6) uses — but axiom (C) only
asserts that *some* cone has such a sequence, and its cone is produced by `Classical.choose`, so
it does not identify that cone with the concrete `ConePackage.cone` of tag 0FS5.

*Why the identification of the arrows is heterogeneous.* The objects and the homogeneous
morphisms of the differential graded category are identified with right differential graded
modules and with action-linear cochains only up to equalities of types, and the chosen shift of
tag 0FS5 is identified with the degree-one shift of axiom (B) only up to an equality of objects
(`SheafOfModules.DifferentialGradedModule.shiftObject_eq`). Every heterogeneous equality below is
one of those transports; the lemmas that turn them back into equations of morphisms are the
`eqToHom` manipulations at the head of the file.

*The translation on morphisms.* The chosen shift of tag 0FS5 is not a functor, so the quotient
functor to `K(Mod(A, d))` carries no `CategoryTheory.Functor.CommShift` for it. What is used
instead is that the comparison functor
`SheafOfModules.DifferentialGradedModule.homotopyCategoryToDG` is fully faithful and *does*
commute with the translations by construction, its comparison isomorphism being a transport of
objects; the compatibility on morphisms is then the computation of the degree-one differential
graded shift of a closed degree-zero cocycle, which is the field `shifted_map` of
`SheafOfModules.DifferentialGradedModule.CanonicalShiftAxiomB`.

## References

* [Stacks Project, Tag 09QU](https://stacks.math.columbia.edu/tag/09QU)
* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
* [Stacks Project, Tag 0FS6](https://stacks.math.columbia.edu/tag/0FS6)
* [Stacks Project, Tag 0FS7](https://stacks.math.columbia.edu/tag/0FS7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated
open CochainComplex.HomComplex

universe u v w

namespace SheafOfModules.DifferentialGradedModule

/-! ### Transports of morphisms along equalities of objects -/

/-- Equal functors have heterogeneously equal values on a morphism. -/
private theorem heq_functor_map {B E : Type*} [Category B] [Category E] {F G : B ⥤ E}
    (h : F = G) {x y : B} (f : x ⟶ y) : HEq (F.map f) (G.map f) := by
  cases h
  rfl

/-- Two heterogeneously equal morphisms become equal after transporting the target of the one
and the source of the other through two steps each. -/
private theorem comp_eqToHom_eqToHom_eq_of_heq {B : Type*} [Category B]
    {x x₁ x₂ y y₁ y₂ : B} (hx₁ : x = x₁) (hx₂ : x₁ = x₂) (hy₁ : y = y₁) (hy₂ : y₁ = y₂)
    {f : x ⟶ y} {g : x₂ ⟶ y₂} (h : HEq f g) :
    f ≫ eqToHom hy₁ ≫ eqToHom hy₂ = eqToHom hx₁ ≫ eqToHom hx₂ ≫ g := by
  cases hx₁; cases hx₂; cases hy₁; cases hy₂
  rw [eq_of_heq h, eqToHom_refl, eqToHom_refl, Category.comp_id, Category.comp_id,
    Category.id_comp, Category.id_comp]

/-- The two-step form of `comp_eqToHom_eqToHom_eq_of_heq` with a single transport on the left. -/
private theorem comp_eqToHom_eq_eqToHom_eqToHom_comp_of_heq {B : Type*} [Category B]
    {x x₁ x₂ y y₂ : B} (hx₁ : x = x₁) (hx₂ : x₁ = x₂) (hy : y = y₂)
    {f : x ⟶ y} {g : x₂ ⟶ y₂} (h : HEq f g) :
    f ≫ eqToHom hy = eqToHom hx₁ ≫ eqToHom hx₂ ≫ g := by
  cases hx₁; cases hx₂; cases hy
  rw [eq_of_heq h]
  simp

/-- Conjugating a morphism by transports of its source and target leaves it heterogeneously
unchanged. -/
private theorem eqToHom_comp_comp_eqToHom_heq {B : Type*} [Category B] {x x' y y' : B}
    (hx : x = x') (hy : y' = y) (f : x' ⟶ y') :
    HEq (eqToHom hx ≫ f ≫ eqToHom hy) f := by
  cases hx; cases hy
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]

/-- Two cochains of heterogeneously equal complexes are heterogeneously equal as soon as all
their components are. -/
private theorem cochain_heq_ext {B : Type*} [Category B] [Preadditive B]
    {M N M' N' : CochainComplex B ℤ} {n : ℤ} (hM : M = M') (hN : N = N')
    (c : Cochain M N n) (c' : Cochain M' N' n)
    (h : ∀ p q (hpq : p + n = q), HEq (c.v p q hpq) (c'.v p q hpq)) : HEq c c' := by
  cases hM; cases hN
  exact heq_of_eq (Cochain.ext c c' fun p q hpq => eq_of_heq (h p q hpq))

/-! ### Transports in the differential graded category -/

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}

/-- Heterogeneously equal cocycles have heterogeneously equal homotopy classes. -/
private theorem quotientMk_heq {R : Type*} [CommRing R] {D : DGCategory R} {x y x' y' : D.Obj}
    (hx : x = x') (hy : y = y') {c : D.Cocycle x y} {c' : D.Cocycle x' y'}
    (h : HEq c c') :
    HEq (Quotient.mk (D.homotopySetoid x y) c) (Quotient.mk (D.homotopySetoid x' y') c') := by
  cases hx; cases hy; cases h
  rfl

/-- A homogeneous morphism of the differential graded category of right differential graded
modules is determined by its underlying cochain, heterogeneously. -/
private theorem hom_heq_of_asCochain_heq
    {x y x' y' : (dgCategoryData.{u, v, w} A).category.Obj}
    {n : ℤ} (hx : x = x') (hy : y = y')
    (g : (dgCategoryData.{u, v, w} A).category.Hom x y n)
    (g' : (dgCategoryData.{u, v, w} A).category.Hom x' y' n)
    (h : HEq (asCochain A g) (asCochain A g')) : HEq g g' := by
  cases hx; cases hy
  exact heq_of_eq (asCochain_injective (eq_of_heq h))

/-- The components of the cochain of the closed degree-zero homogeneous morphism attached to a
morphism of right differential graded modules are the components of that morphism. -/
private theorem asCochain_homogeneousOfHom_v {M N : DifferentialGradedModule.{u, v, w} A}
    (ψ : M ⟶ N) (p : ℤ) :
    HEq ((asCochain A (homogeneousOfHom A (dgCategoryData A) ψ)).v p p (add_zero p))
      (ψ.toHomologicalComplex.f p) :=
  (asCochain_v_heq _ p p (add_zero p)).trans
    (heq_of_eq (by rw [homogeneousOfHom_underlying]; rfl))

/-! ### The chosen shift of a morphism, as a differential graded shift -/

/-- In degree `p` the morphism of chosen shifts induced by `φ` is `φ` in degree `p + 1`. -/
private theorem coneShiftHom_f_heq {K K' : DifferentialGradedModule.{u, v, w} A} (φ : K ⟶ K')
    (p : ℤ) :
    HEq ((coneShiftHom φ).toHomologicalComplex.f p) (φ.toHomologicalComplex.f (p + 1)) := by
  rw [ShiftPackage.map_f]
  change HEq (((eqToHom (shiftPackage K).shifted_complex).f p) ≫
    φ.toHomologicalComplex.f (p + 1) ≫
    ((eqToHom (shiftPackage K').shifted_complex.symm).f p)) _
  rw [HomologicalComplex.eqToHom_f, HomologicalComplex.eqToHom_f]
  exact eqToHom_comp_comp_eqToHom_heq _ _ _

/-- **The morphism of chosen degree-one shifts induced by `φ` is the degree-one differential
graded shift of `φ`.** Both are closed homogeneous morphisms of degree zero whose components are
those of `φ` with the degree raised by one: for the chosen shift this is
`SheafOfModules.DifferentialGradedModule.ShiftPackage.map_f`, and for the differential graded
shift it is the field `shifted_map` of
`SheafOfModules.DifferentialGradedModule.CanonicalShiftAxiomB`, whose sign `(-1)^{k n}` is `+1`
in degree `n = 0`. -/
theorem cocycleOfHom_coneShiftHom_heq (SB : CanonicalShiftAxiomB.{u, v, w} A)
    {K K' : DifferentialGradedModule.{u, v, w} A} (φ : K ⟶ K') :
    HEq (cocycleOfHom A (dgCategoryData.{u, v, w} A) (coneShiftHom φ))
      ((SB.axiomB.shiftFunctor 1).mapCocycle
        (cocycleOfHom A (dgCategoryData.{u, v, w} A) φ)) := by
  refine DGCategory.cocycle_heq_of_val_heq _ _ (shiftObject_eq SB K) (shiftObject_eq SB K') ?_
  refine hom_heq_of_asCochain_heq (shiftObject_eq SB K) (shiftObject_eq SB K') _ _ ?_
  refine cochain_heq_ext
    (congrArg (fun x => (asModule A x).complex) (shiftObject_eq SB K))
    (congrArg (fun x => (asModule A x).complex) (shiftObject_eq SB K')) _ _ ?_
  intro p q hpq
  obtain rfl : p = q := by omega
  refine (asCochain_homogeneousOfHom_v (coneShiftHom φ) p).trans ?_
  refine (coneShiftHom_f_heq φ p).trans ?_
  refine HEq.symm ((SB.shifted_map 1 0 K K' (homogeneousOfHom A _ φ) p p hpq).trans ?_)
  simp only [mul_zero, Int.negOnePow_zero, Units.val_one, one_smul]
  exact asCochain_homogeneousOfHom_v φ (p + 1)

/-! ### The comparison with the differential graded homotopy category and the translations -/

/-- The isomorphism witnessing that the comparison functor commutes with the translations is the
transport along the equality of objects
`SheafOfModules.DifferentialGradedModule.homotopyCategoryToDG_obj_dgObjPreimage`: the
translations of the homotopy category of right differential graded modules are *defined* by
lifting the differential graded ones along the comparison functor. -/
theorem commShiftIso_hom_app_eq (n : ℤ) (M : HomotopyCategory.{u, v, w} A) :
    ((homotopyCategoryToDG A).commShiftIso n).hom.app M =
      eqToHom (homotopyCategoryToDG_obj_dgObjPreimage A
        ((shiftFunctor (dgCategoryData.{u, v, w} A).category.K n).obj
          ((homotopyCategoryToDG A).obj M))) := rfl

/-- The translation of a homotopy class of cocycles is the homotopy class of the differential
graded shift, for any axiom (B) data the chosen cone situation carries. -/
private theorem shiftFunctor_K_map_quotient_heq_aux
    (S : DGCategory.ShiftAxiomB (dgCategoryData.{u, v, w} A).category)
    (hS : (dgConeSituation.{u, v, w} A).shift = S)
    {x y : (dgCategoryData.{u, v, w} A).category.Obj}
    (c : (dgCategoryData.{u, v, w} A).category.Cocycle x y) :
    HEq ((shiftFunctor (dgCategoryData.{u, v, w} A).category.K (1 : ℤ)).map
        (Quotient.mk ((dgCategoryData.{u, v, w} A).category.homotopySetoid x y) c))
      (Quotient.mk ((dgCategoryData.{u, v, w} A).category.homotopySetoid _ _)
        ((S.shiftFunctor 1).mapCocycle c)) := by
  subst hS
  exact heq_functor_map ((dgConeSituation.{u, v, w} A).shift.kShift_functor 1) _

/-- **The degree-one translation of the differential graded homotopy category sends the homotopy
class of a cocycle to the homotopy class of its degree-one differential graded shift.** -/
theorem shiftFunctor_K_map_quotient_heq
    {x y : (dgCategoryData.{u, v, w} A).category.Obj}
    (c : (dgCategoryData.{u, v, w} A).category.Cocycle x y) :
    HEq ((shiftFunctor (dgCategoryData.{u, v, w} A).category.K (1 : ℤ)).map
        (Quotient.mk ((dgCategoryData.{u, v, w} A).category.homotopySetoid x y) c))
      (Quotient.mk ((dgCategoryData.{u, v, w} A).category.homotopySetoid _ _)
        (((shiftAxiomB.{u, v, w} A).axiomB.shiftFunctor 1).mapCocycle c)) :=
  shiftFunctor_K_map_quotient_heq_aux _ (dgConeSituation_shift A) c

/-- **The translation of `K(Mod(A, d))` agrees with the chosen degree-one shift of
[Stacks, Tag 0FS5] on morphisms**, compatibly with the agreement on objects that tag 0FS7
records (`SheafOfModules.DifferentialGradedModule.HomotopyCategory.shiftFunctor_obj`).

The comparison functor to the differential graded homotopy category is faithful, so it is enough
to check the square there, where the translation is the differential graded shift
(`SheafOfModules.DifferentialGradedModule.shiftFunctor_K_map_quotient_heq`) and the shift of the
cocycle of `φ` is the cocycle of `coneShiftHom φ`
(`SheafOfModules.DifferentialGradedModule.cocycleOfHom_coneShiftHom_heq`). -/
theorem quotient_map_coneShiftHom {K K' : DifferentialGradedModule.{u, v, w} A} (φ : K ⟶ K') :
    (HomotopyCategory.quotient A).map (coneShiftHom φ) ≫
        eqToHom (HomotopyCategory.shiftFunctor_obj A K').symm =
      eqToHom (HomotopyCategory.shiftFunctor_obj A K).symm ≫
        (shiftFunctor (HomotopyCategory.{u, v, w} A) (1 : ℤ)).map
          ((HomotopyCategory.quotient A).map φ) := by
  apply (homotopyCategoryToDGFullyFaithful A).map_injective
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map,
    ← cancel_mono (((homotopyCategoryToDG A).commShiftIso (1 : ℤ)).hom.app
      ((HomotopyCategory.quotient A).obj K'))]
  have hnat := ((homotopyCategoryToDG A).commShiftIso (1 : ℤ)).hom.naturality
    ((HomotopyCategory.quotient A).map φ)
  dsimp only [Functor.comp_map] at hnat
  rw [Category.assoc, Category.assoc, hnat, commShiftIso_hom_app_eq, commShiftIso_hom_app_eq]
  refine comp_eqToHom_eqToHom_eq_of_heq _ _ _ _ ?_
  refine HEq.symm ((shiftFunctor_K_map_quotient_heq
    (cocycleOfHom A (dgCategoryData.{u, v, w} A) φ)).trans ?_)
  exact HEq.symm (quotientMk_heq (shiftObject_eq (shiftAxiomB A) K)
    (shiftObject_eq (shiftAxiomB A) K')
    (cocycleOfHom_coneShiftHom_heq (shiftAxiomB A) φ))

/-! ### The cone sequence as a distinguished triangle -/

/-- **The triangle `(L, C(f), K[1], i, p, f[1])` of the cone sequence of a morphism of right
differential graded modules, in the homotopy category.** Its third arrow is the translate of `f`,
read out of the chosen shift of [Stacks, Tag 0FS5] through the object-level identification of
[Stacks, Tag 0FS7]. It is the rotation of the cone triangle
`SheafOfModules.DifferentialGradedModule.homotopyConeTriangle`. -/
def coneRotatedTriangle {K L : DifferentialGradedModule.{u, v, w} A} (f : K ⟶ L) :
    Triangle (HomotopyCategory.{u, v, w} A) :=
  Triangle.mk ((HomotopyCategory.quotient A).map (conePackage f).inclusion)
    ((HomotopyCategory.quotient A).map (conePackage f).projection)
    (eqToHom (HomotopyCategory.shiftFunctor_obj A K).symm ≫
      ((HomotopyCategory.quotient A).map f)⟦(1 : ℤ)⟧')

/-- **The triangle of the cone sequence is distinguished in `K(Mod(A, d))`**, which is
[Stacks, Tag 09QU] for the concrete cone of [Stacks, Tag 0FS5].

The cone sequence `L ⟶ C(f) ⟶ K[1]` is split in the underlying graded category and its
connecting arrow is `f[1]`, by
`SheafOfModules.DifferentialGradedModule.exists_coneSequence`; the criterion
`SheafOfModules.DifferentialGradedModule.HomotopyCategory.distinguished_iff` then applies with
the identity isomorphism on each vertex, the two cocycle conditions being the identification of
a morphism with its cocycle and the third square being the computation of the connecting
arrow. -/
theorem coneRotatedTriangle_distinguished {K L : DifferentialGradedModule.{u, v, w} A}
    (f : K ⟶ L) :
    coneRotatedTriangle f ∈ distTriang (HomotopyCategory.{u, v, w} A) := by
  set P := conePackage f with hP
  obtain ⟨E, ha, hb, hδ⟩ := exists_coneSequence (shiftAxiomB.{u, v, w} A) P
    (cocycleOfHom A (dgCategoryData.{u, v, w} A) f)
    (homogeneousOfHom_underlying A (dgCategoryData.{u, v, w} A) f).symm
  have ha' : cocycleOfHom A (dgCategoryData.{u, v, w} A) P.inclusion = E.a :=
    Subtype.ext (underlyingCochain_injective A _
      ((homogeneousOfHom_underlying A _ _).trans ha.symm))
  have hb' : cocycleOfHom A (dgCategoryData.{u, v, w} A) P.projection = E.b :=
    Subtype.ext (underlyingCochain_injective A _
      ((homogeneousOfHom_underlying A _ _).trans hb.symm))
  have hδ' : HEq (DGCategory.GradedSplitShortExact.connectingCocycle
        (dgConeSituation.{u, v, w} A).shift E)
      (((dgConeSituation.{u, v, w} A).shift.shiftFunctor 1).mapCocycle
        (cocycleOfHom A (dgCategoryData.{u, v, w} A) f)) := by
    rw [dgConeSituation_shift]
    exact hδ
  have hobj : moduleObject A (dgCategoryData.{u, v, w} A) (shift K) =
      ((dgConeSituation.{u, v, w} A).shift.shiftFunctor 1).obj
        (moduleObject A (dgCategoryData.{u, v, w} A) K) := by
    rw [dgConeSituation_shift]
    exact shiftObject_eq (shiftAxiomB A) K
  have hheq := (quotientMk_heq hobj rfl hδ').trans
    (shiftFunctor_K_map_quotient_heq_aux _ rfl
      (cocycleOfHom A (dgCategoryData.{u, v, w} A) f)).symm
  have hnat := ((homotopyCategoryToDG A).commShiftIso (1 : ℤ)).hom.naturality
    ((HomotopyCategory.quotient A).map f)
  dsimp only [Functor.comp_map] at hnat
  have h₃ : (homotopyCategoryToDG A).map
        (eqToHom (HomotopyCategory.shiftFunctor_obj A K).symm ≫
          ((HomotopyCategory.quotient A).map f)⟦(1 : ℤ)⟧') ≫
        ((homotopyCategoryToDG A).commShiftIso (1 : ℤ)).hom.app
          ((HomotopyCategory.quotient A).obj L) =
      (DGCategory.GradedSplitShortExact.associatedKTriangle
        (dgConeSituation.{u, v, w} A).shift E).mor₃ := by
    rw [Functor.map_comp, eqToHom_map, Category.assoc, hnat, commShiftIso_hom_app_eq]
    exact (comp_eqToHom_eq_eqToHom_eqToHom_comp_of_heq _ _ _ hheq).symm
  rw [HomotopyCategory.distinguished_iff]
  refine ⟨L, P.cone, shift K, P.inclusion, P.projection, _, E, ha', hb', ⟨Iso.refl _⟩, ⟨?_⟩⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    exact congrArg (Quotient.mk _) ha'
  · refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    exact congrArg (Quotient.mk _) hb'
  · exact (congrArg (fun m =>
        ((homotopyCategoryToDG A).mapTriangle.obj (coneRotatedTriangle f)).mor₃ ≫ m)
      ((shiftFunctor (dgCategoryData.{u, v, w} A).category.K (1 : ℤ)).map_id _)).trans
        ((Category.comp_id _).trans (h₃.trans (Category.id_comp _).symm))

end SheafOfModules.DifferentialGradedModule

end
