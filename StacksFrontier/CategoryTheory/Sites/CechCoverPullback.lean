module

public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.Topology.Sheaves.Presheaf
public import StacksFrontier.CategoryTheory.Sites.CechComplex

/-!
# The Čech complex of a cover pulled back along a continuous map

Let `f : X ⟶ Y` be a continuous map, `U : ι → Opens Y` a family of opens of the target and `P` a
presheaf of abelian groups — or of objects of any preadditive category with products — on `X`.
Pulling the family back gives the family `f⁻¹U : ι → Opens X`, and the two Čech complexes

  `Č(f⁻¹U, P)`   and   `Č(U, f_*P)`

are the same complex.  Indeed, taking inverse images commutes with the finite intersections
occurring in a Čech complex, so in degree `n` both are the product, over the tuples
`x : Fin (n + 1) → ι`, of the sections of `P` over `f⁻¹(U_{x 0} ∩ ⋯ ∩ U_{x n})`; and the two
differentials are built from the restriction maps between those opens, of which there is at most
one for each ordered pair, because `Opens X` is a partial order.

## Main results

* `Stacks.CategoryTheory.CechComplex.inter_map_opens`: **inverse images commute with the
  intersections occurring in a Čech complex**, `f⁻¹(⋂ₐ U_{x a}) = ⋂ₐ f⁻¹U_{x a}`, as an equality
  of opens.
* `Stacks.CategoryTheory.CechComplex.cechComplexPullbackIso`: **the Čech complex of the pulled
  back family with coefficients in `P` is the Čech complex of the original family with
  coefficients in `f_*P`.**
* `Stacks.CategoryTheory.CechComplex.cechComplexIsoOfIsoOnInter`: a morphism of presheaves which
  is invertible on every intersection occurring in the Čech complex of `U` induces an
  isomorphism of Čech complexes.

## Implementation notes

Both constructions are carried out through the product description of the degreewise terms,
`Stacks.CategoryTheory.CechComplex.π` and `Stacks.CategoryTheory.CechComplex.lift`, and the
componentwise description `Stacks.CategoryTheory.CechComplex.d_comp_π` of the differential.  The
comparison in degree `n` is the map whose component at `x` is the projection of the source
followed by the restriction map of `P` between the two spellings of the intersection.

The intersections are equal opens, and the comparison is written with the restriction map
`P.map (homOfLE _).op` along the inequality rather than with `eqToHom`. Every identity to be
proved is then an identity between two restriction maps of `P` along two morphisms of `Opens X`
with the same source and target, and morphisms of a partial order between a fixed pair of
objects form a subsingleton.

## References

* [Stacks Project, Tag 01FG](https://stacks.math.columbia.edu/tag/01FG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w v v' u' u

namespace Stacks.CategoryTheory.CechComplex

noncomputable section

/-! ### Inverse images of the intersections -/

section Opens

variable {X Y : TopCat.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Opens Y)

/-- **Inverse images commute with the intersections occurring in a Čech complex.**  The formal
intersection `inter U x` of the members of `U` selected by a tuple `x : Fin m → ι` is their
infimum, and taking inverse images commutes with a finite infimum of opens. -/
theorem inter_map_opens {m : ℕ} (x : Fin m → ι) :
    inter (fun t ↦ (Opens.map f).obj (U t)) x = (Opens.map f).obj (inter U x) := by
  apply Opens.ext
  rw [inter_eq_iInf, inter_eq_iInf]
  simp only [Opens.map_coe, Opens.coe_iInf, Set.preimage_iInter]

end Opens

/-! ### The Čech complex of a pulled back cover -/

section Pullback

variable {X Y : TopCat.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Opens Y)
  {A : Type u'} [Category.{v'} A] [HasProducts.{u} A] [Preadditive A]
  (P : (Opens ↥X)ᵒᵖ ⥤ A)

/-- The restriction map of `P` from the inverse image of `inter U x` to the intersection, taken
in `X`, of the inverse images.  The two opens are equal, so this is an isomorphism, with inverse
`interResInv`. -/
def interRes {m : ℕ} (x : Fin m → ι) :
    P.obj (op (inter (fun t ↦ (Opens.map f).obj (U t)) x)) ⟶
      P.obj (op ((Opens.map f).obj (inter U x))) :=
  P.map (homOfLE (le_of_eq (inter_map_opens f U x).symm)).op

/-- The restriction map of `P` in the other direction. -/
def interResInv {m : ℕ} (x : Fin m → ι) :
    P.obj (op ((Opens.map f).obj (inter U x))) ⟶
      P.obj (op (inter (fun t ↦ (Opens.map f).obj (U t)) x)) :=
  P.map (homOfLE (le_of_eq (inter_map_opens f U x))).op

omit [HasProducts.{u} A] [Preadditive A] in
/-- `interResInv` is a right inverse of `interRes`. -/
@[simp]
theorem interRes_comp_interResInv {m : ℕ} (x : Fin m → ι) :
    interRes f U P x ≫ interResInv f U P x = 𝟙 _ := by
  rw [interRes, interResInv, ← P.map_comp, ← op_comp,
    Subsingleton.elim (homOfLE (le_of_eq (inter_map_opens f U x)) ≫
      homOfLE (le_of_eq (inter_map_opens f U x).symm)) (𝟙 _), op_id, P.map_id]

omit [HasProducts.{u} A] [Preadditive A] in
/-- `interResInv` is a left inverse of `interRes`. -/
@[simp]
theorem interResInv_comp_interRes {m : ℕ} (x : Fin m → ι) :
    interResInv f U P x ≫ interRes f U P x = 𝟙 _ := by
  rw [interRes, interResInv, ← P.map_comp, ← op_comp,
    Subsingleton.elim (homOfLE (le_of_eq (inter_map_opens f U x).symm) ≫
      homOfLE (le_of_eq (inter_map_opens f U x))) (𝟙 _), op_id, P.map_id]

/-- The degree-`n` component of the comparison from the Čech complex of the pulled back family
with coefficients in `P` to the Čech complex of `U` with coefficients in `f_*P`:  its component
at the tuple `x` is the projection followed by `interRes`. -/
def pullbackF (n : ℕ) :
    ((cechComplexFunctor (fun t ↦ (Opens.map f).obj (U t))).obj P).X n ⟶
      ((cechComplexFunctor U).obj ((TopCat.Presheaf.pushforward A f).obj P)).X n :=
  lift U ((TopCat.Presheaf.pushforward A f).obj P) fun x ↦
    π (fun t ↦ (Opens.map f).obj (U t)) P n x ≫ interRes f U P x

/-- The degree-`n` component of the comparison in the other direction. -/
def pullbackFInv (n : ℕ) :
    ((cechComplexFunctor U).obj ((TopCat.Presheaf.pushforward A f).obj P)).X n ⟶
      ((cechComplexFunctor (fun t ↦ (Opens.map f).obj (U t))).obj P).X n :=
  lift (fun t ↦ (Opens.map f).obj (U t)) P fun x ↦
    π U ((TopCat.Presheaf.pushforward A f).obj P) n x ≫ interResInv f U P x

/-- The component of `pullbackF` at the tuple `x`. -/
@[reassoc (attr := simp)]
theorem pullbackF_comp_π (n : ℕ) (x : Fin (n + 1) → ι) :
    pullbackF f U P n ≫ π U ((TopCat.Presheaf.pushforward A f).obj P) n x =
      π (fun t ↦ (Opens.map f).obj (U t)) P n x ≫ interRes f U P x :=
  lift_comp_π U ((TopCat.Presheaf.pushforward A f).obj P) _ x

/-- The component of `pullbackFInv` at the tuple `x`. -/
@[reassoc (attr := simp)]
theorem pullbackFInv_comp_π (n : ℕ) (x : Fin (n + 1) → ι) :
    pullbackFInv f U P n ≫ π (fun t ↦ (Opens.map f).obj (U t)) P n x =
      π U ((TopCat.Presheaf.pushforward A f).obj P) n x ≫ interResInv f U P x :=
  lift_comp_π (fun t ↦ (Opens.map f).obj (U t)) P _ x

/-- `pullbackFInv` is a right inverse of `pullbackF`. -/
theorem pullbackF_comp_pullbackFInv (n : ℕ) :
    pullbackF f U P n ≫ pullbackFInv f U P n = 𝟙 _ := by
  refine hom_ext (fun t ↦ (Opens.map f).obj (U t)) P fun x ↦ ?_
  rw [Category.assoc, pullbackFInv_comp_π, pullbackF_comp_π_assoc,
    interRes_comp_interResInv]
  simp

/-- `pullbackFInv` is a left inverse of `pullbackF`. -/
theorem pullbackFInv_comp_pullbackF (n : ℕ) :
    pullbackFInv f U P n ≫ pullbackF f U P n = 𝟙 _ := by
  refine hom_ext U ((TopCat.Presheaf.pushforward A f).obj P) fun x ↦ ?_
  rw [Category.assoc, pullbackF_comp_π, pullbackFInv_comp_π_assoc,
    interResInv_comp_interRes]
  simp

/-- The comparison commutes with the Čech differentials.  Componentwise both sides are the
alternating sum of the restriction maps of `P` along the two composites

  `f⁻¹(inter U y) ⟶ f⁻¹(inter U (y ∘ σ)) ⟶ inter f⁻¹U (y ∘ σ)`   and
  `f⁻¹(inter U y) ⟶ inter f⁻¹U y ⟶ inter f⁻¹U (y ∘ σ)`,

which are morphisms of `Opens X` with the same source and the same target, hence equal. -/
theorem pullbackF_comm (n : ℕ) :
    pullbackF f U P n ≫
        ((cechComplexFunctor U).obj ((TopCat.Presheaf.pushforward A f).obj P)).d n (n + 1) =
      ((cechComplexFunctor (fun t ↦ (Opens.map f).obj (U t))).obj P).d n (n + 1) ≫
        pullbackF f U P (n + 1) := by
  refine hom_ext U ((TopCat.Presheaf.pushforward A f).obj P) (n := n + 1) fun y ↦ ?_
  have key : ∀ i : Fin (n + 2),
      (π (fun t ↦ (Opens.map f).obj (U t)) P n (y ∘ i.succAbove) ≫
          interRes f U P (y ∘ i.succAbove)) ≫
        P.map ((Opens.map f).map (interMap U y i.succAbove)).op =
      (π (fun t ↦ (Opens.map f).obj (U t)) P n (y ∘ i.succAbove) ≫
          P.map (interMap (fun t ↦ (Opens.map f).obj (U t)) y i.succAbove).op) ≫
        interRes f U P y := by
    intro i
    rw [Category.assoc, Category.assoc]
    refine congrArg
      (fun z ↦ π (fun t ↦ (Opens.map f).obj (U t)) P n (y ∘ i.succAbove) ≫ z) ?_
    rw [interRes, interRes, ← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp]
    exact congrArg (fun m ↦ P.map (Opposite.op m)) (Subsingleton.elim _ _)
  conv_lhs => rw [Category.assoc, d_comp_π, Preadditive.comp_sum]
  conv_rhs => rw [Category.assoc, pullbackF_comp_π, ← Category.assoc, d_comp_π,
    Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, ← Category.assoc, pullbackF_comp_π]
  exact congrArg (fun z ↦ (-1 : ℤ) ^ (i : ℕ) • z) (key i)

/-- The degree-`n` comparison is an isomorphism, the two restriction maps `interRes` and
`interResInv` being mutually inverse. -/
def pullbackIsoX (n : ℕ) :
    ((cechComplexFunctor (fun t ↦ (Opens.map f).obj (U t))).obj P).X n ≅
      ((cechComplexFunctor U).obj ((TopCat.Presheaf.pushforward A f).obj P)).X n where
  hom := pullbackF f U P n
  inv := pullbackFInv f U P n
  hom_inv_id := pullbackF_comp_pullbackFInv f U P n
  inv_hom_id := pullbackFInv_comp_pullbackF f U P n

/-- **The Čech complex of a pulled back cover.**  For a continuous map `f : X ⟶ Y`, a family
`U : ι → Opens Y` and a presheaf `P` on `X`, the Čech complex of the family of inverse images
`f⁻¹U` with coefficients in `P` is the Čech complex of `U` with coefficients in the pushforward
`f_*P`. -/
def cechComplexPullbackIso :
    (cechComplexFunctor (fun t ↦ (Opens.map f).obj (U t))).obj P ≅
      (cechComplexFunctor U).obj ((TopCat.Presheaf.pushforward A f).obj P) :=
  HomologicalComplex.Hom.isoOfComponents (pullbackIsoX f U P) (by
    intro m n h
    obtain rfl : m + 1 = n := h
    exact pullbackF_comm f U P m)

end Pullback

/-! ### A morphism invertible on the intersections -/

section Map

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A] [HasProducts.{w} A]
  [HasFiniteProducts C] [Preadditive A] {ι : Type w} (U : ι → C) {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q)
  (hα : ∀ (n : ℕ) (x : Fin (n + 1) → ι), IsIso (α.app (op (inter U x))))

/-- The degree-`n` component of the map of Čech complexes induced by `α`: its component at the
tuple `x` is the projection followed by the value of `α` on `inter U x`. -/
def mapF (n : ℕ) : ((cechComplexFunctor U).obj P).X n ⟶ ((cechComplexFunctor U).obj Q).X n :=
  lift U Q fun x ↦ π U P n x ≫ α.app (op (inter U x))

/-- The degree-`n` component of the inverse map, using that `α` is invertible on the
intersections. -/
def mapFInv (n : ℕ) : ((cechComplexFunctor U).obj Q).X n ⟶ ((cechComplexFunctor U).obj P).X n :=
  lift U P fun x ↦ π U Q n x ≫ @inv _ _ _ _ (α.app (op (inter U x))) (hα n x)

/-- The component of `mapF` at the tuple `x`. -/
@[reassoc (attr := simp)]
theorem mapF_comp_π (n : ℕ) (x : Fin (n + 1) → ι) :
    mapF U α n ≫ π U Q n x = π U P n x ≫ α.app (op (inter U x)) :=
  lift_comp_π U Q _ x

/-- The component of `mapFInv` at the tuple `x`. -/
@[reassoc (attr := simp)]
theorem mapFInv_comp_π (n : ℕ) (x : Fin (n + 1) → ι) :
    mapFInv U α hα n ≫ π U P n x =
      π U Q n x ≫ @inv _ _ _ _ (α.app (op (inter U x))) (hα n x) :=
  lift_comp_π U P _ x

/-- `mapFInv` is a right inverse of `mapF`. -/
theorem mapF_comp_mapFInv (n : ℕ) : mapF U α n ≫ mapFInv U α hα n = 𝟙 _ := by
  refine hom_ext U P fun x ↦ ?_
  rw [Category.assoc, mapFInv_comp_π, mapF_comp_π_assoc,
    @IsIso.hom_inv_id _ _ _ _ _ (hα n x)]
  simp

/-- `mapFInv` is a left inverse of `mapF`. -/
theorem mapFInv_comp_mapF (n : ℕ) : mapFInv U α hα n ≫ mapF U α n = 𝟙 _ := by
  refine hom_ext U Q fun x ↦ ?_
  rw [Category.assoc, mapF_comp_π, mapFInv_comp_π_assoc,
    @IsIso.inv_hom_id _ _ _ _ _ (hα n x)]
  simp

/-- The map of Čech complexes induced by `α` commutes with the differentials: componentwise this
is the naturality of `α` along the restriction maps `interMap`. -/
theorem mapF_comm (n : ℕ) :
    mapF U α n ≫ ((cechComplexFunctor U).obj Q).d n (n + 1) =
      ((cechComplexFunctor U).obj P).d n (n + 1) ≫ mapF U α (n + 1) := by
  refine hom_ext U Q (n := n + 1) fun y ↦ ?_
  conv_lhs => rw [Category.assoc, d_comp_π, Preadditive.comp_sum]
  conv_rhs => rw [Category.assoc, mapF_comp_π, ← Category.assoc, d_comp_π,
    Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, ← Category.assoc, mapF_comp_π,
    Category.assoc, Category.assoc]
  exact congrArg (fun z ↦ (-1 : ℤ) ^ (i : ℕ) • (π U P n (y ∘ i.succAbove) ≫ z))
    (α.naturality (interMap U y i.succAbove).op).symm

/-- The degree-`n` component of the induced map is an isomorphism. -/
def mapIsoX (n : ℕ) :
    ((cechComplexFunctor U).obj P).X n ≅ ((cechComplexFunctor U).obj Q).X n where
  hom := mapF U α n
  inv := mapFInv U α hα n
  hom_inv_id := mapF_comp_mapFInv U α hα n
  inv_hom_id := mapFInv_comp_mapF U α hα n

/-- **A morphism of presheaves invertible on the intersections induces an isomorphism of Čech
complexes.**  Only the values of `α` on the objects `inter U x` occur in the two complexes, so
nothing is required of it elsewhere.  This applies, for instance, to a comparison map of
presheaves on a space that is invertible on the quasi-compact opens (the form in which
Stacks 009F describes the sections of a filtered colimit of sheaves) when every intersection
`inter U x` is quasi-compact. -/
def cechComplexIsoOfIsoOnInter :
    (cechComplexFunctor U).obj P ≅ (cechComplexFunctor U).obj Q :=
  HomologicalComplex.Hom.isoOfComponents (mapIsoX U α hα) (by
    intro m n h
    obtain rfl : m + 1 = n := h
    exact mapF_comm U α m)

end Map

end

end Stacks.CategoryTheory.CechComplex

end
