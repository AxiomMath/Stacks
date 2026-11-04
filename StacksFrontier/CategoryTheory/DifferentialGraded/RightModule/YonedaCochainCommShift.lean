module

public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexShiftCoherence
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexTriangulated
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.RestrictionExact
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.YonedaShiftIso

/-!
# The Yoneda comparison of the differential graded category of complexes is coherent

`DGCategory.commShiftBIso_yonedaDGFunctor` is the canonical comparison
`h_{X[n]} ≅ (h_X)[n]` of the differential graded Yoneda functor, available for any differential
graded category carrying the isomorphism-valued axiom (B); it is the inverse of the
identification `toShift n` of axiom (B), read degreewise, and its components are computed by
`DGCategory.app_yonedaShiftHom`. What `DGCategory.DGFunctor.CommShiftKIso` asks for beyond it is
the agreement of the induced family `kIso` with the `ℤ`-action data of the two translations, and
`DGCategory.isTriangulated_yonedaOnK_of_commShiftKIso` explains why that agreement cannot follow
from axiom (B) alone.

At `C = CochainComplex.dgCategory A` it holds, and this file proves it, in degree `0` and for a
sum of degrees. Nothing here strictifies anything: the comparisons `X⟦0⟧ ≅ X` and
`X⟦a + b⟧ ≅ X⟦a⟧⟦b⟧` used throughout are `CochainComplex.dgZeroIso` and
`CochainComplex.dgAddIso`, the ones `CochainComplex.dgShiftAxiomBIso` carries. So
`CochainComplex.commShiftKIso_yonedaDGFunctor` exists, and with it the functor
`K(h) : K(Comp^dg(A)) ⥤ K(Mod^dg(Comp^dg(A)))` commutes with the translations and is exact.

## Main definitions

* `CochainComplex.commShiftKIso_yonedaDGFunctor`: **the hypothesis of Tag 0FQF together with
  both of its coherences**, for the differential graded Yoneda functor of the differential
  graded category of complexes.

## Main results

* `CochainComplex.dgToShift_zero_symm` and `CochainComplex.dgToShift_add_symm`: the inverse of
  the identification of axiom (B) in degree `0` is composition with `CochainComplex.dgZeroIso`,
  and in a degree `a + b` it is composition with `CochainComplex.dgAddIso` followed by the two
  inverse identifications in degrees `b` and `a`.
* `CochainComplex.heq_yonedaShiftHom_zero` and `CochainComplex.heq_dgToShift_add_symm`:
  therefore the comparison `h_{X⟦0⟧} ⟶ (h_X)⟦0⟧` in degree `0` *is* the Yoneda image of
  `CochainComplex.dgZeroIso`, and the degree-`a + b` comparison is the composite of the
  degree-`b` and degree-`a` ones with the Yoneda image of `CochainComplex.dgAddIso`.
* `CochainComplex.kIso_zero_yoneda` and `CochainComplex.kIso_add_yoneda`: **the comparison
  isomorphisms of functors are the canonical ones**,
  `CategoryTheory.Functor.CommShift.isoZero` and `CategoryTheory.Functor.CommShift.isoAdd`.
* `CochainComplex.yonedaOnK_commShift` and `CochainComplex.yonedaOnK_isTriangulated`: `K(h)`
  commutes with the translations, and is an exact functor of triangulated categories.
* `DGCategory.heq_yonedaShiftHom_add`: the degree-`a + b` comparison of the Yoneda functor of
  any differential graded category with the isomorphism-valued axiom (B) is that composite, as
  soon as the corresponding identity holds for the inverse identifications.

## Implementation notes

The target of the comparison in degree `0` is `(h_X)⟦0⟧` and not `h_X`, and in degree `a + b` it
is `(h_X)⟦a + b⟧` and not `((h_X)⟦a⟧)⟦b⟧`; each pair is equal as right differential graded
modules, by `DGCategory.RightModule.shift_zero` and `DGCategory.rightModuleShift_obj_add`, but
not definitionally so, and neither equality has a side that is a variable, so neither can be
substituted. The comparison of the two morphisms is therefore made heterogeneously, by
`DGCategory.RightModule.homogeneousMap_heq`, which substitutes the equality internally; it is
turned back into an equation of morphisms of `K(Mod^dg(C))` by
`DGCategory.DGFunctor.CommShiftB.comp_eqCocycle_eq_of_heq` and
`DGCategory.DGFunctor.CommShiftB.mk_eqCocycle`. This is the same device
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.ShiftFunctorStrict` uses for the
strict coherences of the shift of a module.

On the source side the `ℤ`-action data of the translation of `K(Comp^dg(A))` are
`CochainComplex.shiftFunctorZero_dgCategoryK_hom_app` and
`CochainComplex.shiftFunctorAdd_dgCategoryK_hom_app`; on the target side the translation of
`K(Mod^dg(C))` is strict, so its own data are `eqToIso`s, by
`DGCategory.isStrictKShift_rightModuleShiftAxiomB`.

Both coherences are equations between composites in which the comparisons of the two
translations with the differential graded shift functors appear as `eqToHom`s between
definitionally equal objects. Such a composite cannot be rewritten: a goal in which an object of
the differential graded category has to be read as an object of its homotopy category is not
type-correct at the transparency `rw` and `simp` use, and they refuse to fire. Both are therefore
collapsed by one `exact` of an auxiliary identity stated with identities in place of those
`eqToHom`s, which works at default transparency; and the four-factor composite of the additivity
coherence is identified with a single homotopy class by `DGCategory.mk_eq_comp_four`, whose
cocycles are hypotheses, rather than by unfolding the composite.

## References

* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF);
  [Tag 09P6](https://stacks.math.columbia.edu/tag/09P6), axiom (B);
  [Tag 09LK](https://stacks.math.columbia.edu/tag/09LK).
-/

@[expose] public section

open CategoryTheory

namespace DGCategory

universe w v u r

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

/-- A value of a right differential graded module transported to an equal degree is that value.
This is the heterogeneous form of `DGCategory.RightModule.objCast_rfl`. -/
theorem RightModule.objCast_heq (M : RightModule.{w} C) (x : C.Obj) {i j : ℤ} (h : i = j)
    (a : M.obj x i) : HEq (M.objCast x h a) a := by
  subst h
  rfl

/-- Composition of two homotopy classes is the class of the composite cocycle. -/
theorem mk_comp_mk {X Y Z : C.K} (f : C.Cocycle (X : C.Obj) (Y : C.Obj))
    (g : C.Cocycle (Y : C.Obj) (Z : C.Obj)) :
    @Eq (X ⟶ Z) ((Quotient.mk _ f : X ⟶ Y) ≫ (Quotient.mk _ g : Y ⟶ Z))
      (Quotient.mk _ (C.compCocycle g f)) :=
  rfl

/-- **A four-factor composite of homotopy classes, identified by cocycles.** The four morphisms
and the one they compose to are variables, each with its representing cocycle supplied as a
hypothesis, so that the composite of the homotopy category never has to be unfolded in a goal
where the four factors are produced by functors and by `eqToHom`s. -/
private theorem mk_eq_comp_four {X Y Z W V : C.K}
    (u : X ⟶ Y) (v : Y ⟶ Z) (w : Z ⟶ W) (e : W ⟶ V) (L : X ⟶ V)
    (cu : C.Cocycle (X : C.Obj) (Y : C.Obj)) (cv : C.Cocycle (Y : C.Obj) (Z : C.Obj))
    (cw : C.Cocycle (Z : C.Obj) (W : C.Obj)) (ce : C.Cocycle (W : C.Obj) (V : C.Obj))
    (cL : C.Cocycle (X : C.Obj) (V : C.Obj))
    (hu : u = Quotient.mk _ cu) (hv : v = Quotient.mk _ cv) (hw : w = Quotient.mk _ cw)
    (he : e = Quotient.mk _ ce) (hL : L = Quotient.mk _ cL)
    (hc : cL = C.compCocycle ce (C.compCocycle cw (C.compCocycle cv cu))) :
    L = u ≫ v ≫ w ≫ e := by
  subst hu
  subst hv
  subst hw
  subst he
  subst hL
  rw [← Category.assoc, ← Category.assoc, mk_comp_mk, mk_comp_mk, mk_comp_mk]
  exact congrArg (Quotient.mk _) hc

/-- **The degree-`a + b` Yoneda comparison is the composite of the degree-`b` and degree-`a`
ones with the Yoneda image of the comparison `X[a + b] ≅ X[a][b]`**, over the equality of modules
`DGCategory.rightModuleShift_obj_add`.

The hypothesis is exactly that statement for the inverse identifications of axiom (B), which is
where the particular differential graded category enters; everything else is the degree
bookkeeping of the two shifts, and the sign the shift of a homogeneous morphism carries is
trivial because the comparison has degree `0`. -/
theorem heq_yonedaShiftHom_add (S : ShiftAxiomBIso C) (a b : ℤ) (X : C.Obj)
    (hsymm : ∀ (z : C.Obj) (i i' : ℤ) (hi : (0 : ℤ) + i = i')
      (α : C.Hom z ((S.shiftFunctor (a + b)).obj X) i),
      HEq ((S.toShift a z X (i' + b)).symm
            ((S.toShift b z ((S.shiftFunctor a).obj X) i').symm
              (C.comp hi (S.addIso a b X).hom.1 α)))
          ((S.toShift (a + b) z X i).symm α)) :
    HEq (RightModule.homComp (add_zero (0 : ℤ))
          (RightModule.shiftMap (yonedaShiftHom S a X) b)
          (RightModule.homComp (add_zero (0 : ℤ))
            (yonedaShiftHom S b ((S.shiftFunctor a).obj X))
            (yonedaPostcomp C (S.addIso a b X).hom.1)))
      (yonedaShiftHom S (a + b) X) := by
  refine RightModule.homogeneousMap_heq rfl
    (rightModuleShift_obj_add C a b (yonedaRightModule C X)).symm ?_
  intro z i j e u v huv
  obtain rfl := eq_of_heq huv
  subst e
  simp only [RightModule.app_homComp, RightModule.app_shiftMap, app_yonedaShiftHom,
    app_yonedaPostcomp, RightModule.objCast_rfl, mul_zero, Int.natAbs_zero, pow_zero, one_smul]
  refine HEq.trans (hsymm z i (i + 0) (by omega) u) ?_
  exact (RightModule.objCast_heq (yonedaRightModule C X) z
    (show i + (a + b) = i + 0 + (a + b) by omega)
    ((S.toShift (a + b) z X i).symm u)).symm

end DGCategory

namespace CochainComplex

open CochainComplex.HomComplex

universe v u

variable (A : Type u) [Category.{v} A] [Preadditive A]

/-! ### The comparison in degree zero -/

/-- **The inverse of the identification of axiom (B) in degree `0` is composition with the
comparison `X⟦0⟧ ≅ X`.** This is `CochainComplex.rightShift_zero_comp`, read through
`CochainComplex.dgShiftComparisonData`. -/
theorem dgToShift_zero_symm (x y : CochainComplex A ℤ) (i : ℤ)
    (a : (dgCategory A).Hom y ((dgShiftFunctor A 0).obj x) i) :
    ((dgShiftAxiomBIso A).toShift 0 y x i).symm a =
      (dgCategory A).comp (show (0 : ℤ) + i = i + 0 by omega) (dgZeroIso A x).hom.1 a := by
  refine ((dgShiftAxiomBIso A).toShift 0 y x i).symm_apply_eq.mpr ?_
  exact (rightShift_zero_comp x y i (i + 0) (by omega) a).symm

/-- **In degree `0` the Yoneda comparison is the Yoneda image of `CochainComplex.dgZeroIso`.**
The two morphisms have different targets, `h_X` and `(h_X)⟦0⟧`, which are equal by
`DGCategory.RightModule.shift_zero`; the comparison is therefore heterogeneous. -/
theorem heq_yonedaShiftHom_zero (x : CochainComplex A ℤ) :
    HEq (DGCategory.yonedaPostcomp (dgCategory A) (dgZeroIso A x).hom.1)
      (DGCategory.yonedaShiftHom (dgShiftAxiomBIso A) 0 x) := by
  refine DGCategory.RightModule.homogeneousMap_heq rfl
    (DGCategory.RightModule.shift_zero
      (DGCategory.yonedaRightModule (dgCategory A) x)).symm ?_
  intro y i j e a b hab
  obtain rfl := eq_of_heq hab
  subst e
  refine HEq.trans ?_ (DGCategory.RightModule.objCast_heq _ _ _ _).symm
  exact heq_of_eq (dgToShift_zero_symm A x y i a).symm

/-- The shape of the two sides of `CochainComplex.kIso_zero_yoneda` once the comparisons of the
two translations with the differential graded shift functors — both of which hold by reflexivity
— have been read as identities. Stated separately so that it can be applied by `exact`, at
default transparency. -/
private theorem id_comp_id {E : Type*} [Category E] {X Y : E} (f : X ⟶ Y) :
    𝟙 X ≫ f ≫ 𝟙 Y = f := by simp

/-- **The Yoneda comparison isomorphism of functors in degree `0` is the canonical one.** This is
the field `kIso_zero` of `DGCategory.DGFunctor.CommShiftKIso` for the differential graded Yoneda
functor of the differential graded category of complexes, and it is proved with the
isomorphism-valued axiom (B) of `CochainComplex.dgShiftAxiomBIso`: no strict identity
`X⟦0⟧ = X` is used or available. -/
theorem kIso_zero_yoneda :
    (DGCategory.commShiftBIso_yonedaDGFunctor (dgShiftAxiomBIso A)).kIso 0 =
      Functor.CommShift.isoZero (DGCategory.yonedaDGFunctor (dgCategory A)).onK ℤ := by
  refine Iso.ext (NatTrans.ext (funext fun x => ?_))
  obtain ⟨h0, hB0⟩ :=
    (DGCategory.isStrictKShift_rightModuleShiftAxiomB (dgCategory A)).1
  rw [DGCategory.DGFunctor.CommShiftBIso.kIso_hom_app,
    Functor.CommShift.isoZero_hom_app, hB0, shiftFunctorZero_dgCategoryK_hom_app,
    eqToIso.inv, eqToHom_app, eqToHom_map,
    ← DGCategory.DGFunctor.CommShiftB.mk_eqCocycle
      (Functor.congr_obj h0.symm ((dgCategory A).yonedaDGFunctor.onK.obj x))]
  refine (id_comp_id ((DGCategory.commShiftBIso_yonedaDGFunctor
    (dgShiftAxiomBIso A)).kHom 0 x)).trans ?_
  exact congrArg (Quotient.mk _) (Subtype.ext
    (DGCategory.DGFunctor.CommShiftB.comp_eqCocycle_eq_of_heq _ _ _
      (heq_yonedaShiftHom_zero A x)).symm)

/-! ### The comparison in a sum of degrees -/

/-- **The inverse of the identification of axiom (B) in a degree `a + b` is composition with the
comparison `X⟦a + b⟧ ≅ X⟦a⟧⟦b⟧` followed by the inverse identifications in degrees `b` and
`a`.** This is `CochainComplex.rightUnshift_comp_add_eq`, read through
`CochainComplex.dgShiftComparisonData`; the target degree is `(i' + b) + a` and not
`i + (a + b)`, so the value is written as the reindexing
`CochainComplex.HomComplex.Cochain.rightUnshift` with that degree prescribed. -/
theorem dgToShift_add_symm (a b : ℤ) (x z : CochainComplex A ℤ) (i i' : ℤ)
    (hi : (0 : ℤ) + i = i')
    (α : (dgCategory A).Hom z ((dgShiftFunctor A (a + b)).obj x) i) :
    ((dgShiftAxiomBIso A).toShift a z x (i' + b)).symm
        (((dgShiftAxiomBIso A).toShift b z ((dgShiftFunctor A a).obj x) i').symm
          ((dgCategory A).comp hi (dgAddIso A a b x).hom.1 α)) =
      Cochain.rightUnshift α (i' + b + a) (by omega) := by
  refine ((dgShiftAxiomBIso A).toShift a z x (i' + b)).symm_apply_eq.mpr ?_
  refine ((dgShiftAxiomBIso A).toShift b z ((dgShiftFunctor A a).obj x) i').symm_apply_eq.mpr ?_
  exact rightUnshift_comp_add_eq x z a b i i' (i' + b) (i' + b + a) (by omega) (by omega)
    (by omega) (by omega) α

/-- Two reindexings of one cochain to two spellings of the same degree agree. -/
private theorem heq_rightUnshift (x z : CochainComplex A ℤ) (n i d d' : ℤ)
    (β : Cochain z (x⟦n⟧ : CochainComplex A ℤ) i) (hd : i + n = d) (hd' : i + n = d') :
    HEq (β.rightUnshift d hd) (β.rightUnshift d' hd') := by
  obtain rfl : d = d' := by omega
  rfl

/-- **`CochainComplex.dgToShift_add_symm` with both sides read in the degree the identification
of axiom (B) produces.** The left-hand side lands in degree `(i' + b) + a` and the right-hand
side in degree `i + (a + b)`; the two are equal, so the comparison is heterogeneous. This is the
hypothesis `DGCategory.heq_yonedaShiftHom_add` asks for. -/
theorem heq_dgToShift_add_symm (a b : ℤ) (x z : CochainComplex A ℤ) (i i' : ℤ)
    (hi : (0 : ℤ) + i = i')
    (α : (dgCategory A).Hom z (((dgShiftAxiomBIso A).shiftFunctor (a + b)).obj x) i) :
    HEq (((dgShiftAxiomBIso A).toShift a z x (i' + b)).symm
          (((dgShiftAxiomBIso A).toShift b z
              (((dgShiftAxiomBIso A).shiftFunctor a).obj x) i').symm
            ((dgCategory A).comp hi ((dgShiftAxiomBIso A).addIso a b x).hom.1 α)))
      (((dgShiftAxiomBIso A).toShift (a + b) z x i).symm α) := by
  refine HEq.trans (heq_of_eq (dgToShift_add_symm A a b x z i i' hi α)) ?_
  exact heq_rightUnshift A x z (a + b) i (i' + b + a) (i + (a + b)) α (by omega) (by omega)

/-- The shape of the two sides of `CochainComplex.kIso_add_yoneda` once the comparisons of the
two translations with the differential graded shift functors — all of which hold by reflexivity
— have been read as identities. The first factor is a variable with its value a hypothesis,
because the one the goal produces is the `ℤ`-action datum of the translation of
`K(Comp^dg(A))`, whose `HasShift` instance is the field of
`CochainComplex.dgShiftAxiomBIso` rather than the registered
`CochainComplex.dgCategoryKShift`: the two are definitionally equal, so `exact` identifies them,
while `rw` does not. -/
private theorem id_comp_four {D D' : Type*} [Category D] [Category D'] (S : D ⥤ D')
    {X Y V : D'} {U W : D} (L : X ⟶ V) (u u' : X ⟶ Y) (kb : Y ⟶ S.obj U) (ka : U ⟶ W)
    (e : S.obj W ⟶ V) (hu : u = u') (h : L = u' ≫ kb ≫ S.map ka ≫ e) :
    𝟙 X ≫ L ≫ 𝟙 V =
      u ≫ (𝟙 Y ≫ kb ≫ 𝟙 (S.obj U)) ≫ S.map (𝟙 U ≫ ka ≫ 𝟙 W) ≫ e := by
  subst hu
  rw [h]
  simp

/-- **The Yoneda comparison isomorphisms of functors are additive in the degree.** This is the
field `kIso_add` of `DGCategory.DGFunctor.CommShiftKIso` for the differential graded Yoneda
functor of the differential graded category of complexes, and it is proved with the
isomorphism-valued axiom (B) of `CochainComplex.dgShiftAxiomBIso`: no strict identity
`X⟦a + b⟧ = X⟦a⟧⟦b⟧` is used or available. -/
theorem kIso_add_yoneda (a b : ℤ) :
    (DGCategory.commShiftBIso_yonedaDGFunctor (dgShiftAxiomBIso A)).kIso (a + b) =
      Functor.CommShift.isoAdd
        ((DGCategory.commShiftBIso_yonedaDGFunctor (dgShiftAxiomBIso A)).kIso a)
        ((DGCategory.commShiftBIso_yonedaDGFunctor (dgShiftAxiomBIso A)).kIso b) := by
  refine Iso.ext (NatTrans.ext (funext fun x => ?_))
  obtain ⟨hBab, hBeq⟩ := (DGCategory.isStrictKShift_rightModuleShiftAxiomB (dgCategory A)).2 a b
  rw [DGCategory.DGFunctor.CommShiftBIso.kIso_hom_app,
    Functor.CommShift.isoAdd_hom_app, hBeq, eqToIso.inv, eqToHom_app,
    DGCategory.DGFunctor.CommShiftBIso.kIso_hom_app,
    DGCategory.DGFunctor.CommShiftBIso.kIso_hom_app,
    ← DGCategory.DGFunctor.CommShiftB.mk_eqCocycle
      (Functor.congr_obj hBab ((dgCategory A).yonedaDGFunctor.onK.obj x)).symm]
  simp only [eqToHom_map]
  refine id_comp_four _ _ _ _ _ _ _
    (congrArg (fun m => (dgCategory A).yonedaDGFunctor.onK.map m)
      (shiftFunctorAdd_dgCategoryK_hom_app A a b x)) ?_
  refine DGCategory.mk_eq_comp_four _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl ?_
  exact Subtype.ext
    (DGCategory.DGFunctor.CommShiftB.comp_eqCocycle_eq_of_heq _ _ _
      (DGCategory.heq_yonedaShiftHom_add (dgShiftAxiomBIso A) a b x
        (fun z i i' hi α => heq_dgToShift_add_symm A a b x z i i' hi α))).symm

/-! ### The hypothesis of Tag 0FQF with both of its coherences -/

/-- **The differential graded Yoneda functor of the differential graded category of complexes
commutes with the shift, coherently.** The comparison is
`DGCategory.commShiftBIso_yonedaDGFunctor`, which axiom (B) supplies for free, and the two
coherences `DGCategory.DGFunctor.CommShiftKIso` adds to it are
`CochainComplex.kIso_zero_yoneda` and `CochainComplex.kIso_add_yoneda`. -/
noncomputable def commShiftKIso_yonedaDGFunctor :
    (DGCategory.yonedaDGFunctor (dgCategory A)).CommShiftKIso (dgShiftAxiomBIso A)
      (DGCategory.rightModuleShiftAxiomB.{v} (dgCategory A)).toShiftAxiomBIso :=
  ⟨DGCategory.commShiftBIso_yonedaDGFunctor (dgShiftAxiomBIso A), kIso_zero_yoneda A,
    kIso_add_yoneda A⟩

/-- **`K(h) : K(Comp^dg(A)) ⥤ K(Mod^dg(Comp^dg(A)))` commutes with the translations**, with the
comparison isomorphisms of axiom (B). -/
noncomputable instance yonedaOnK_commShift :
    (DGCategory.yonedaDGFunctor (dgCategory A)).onK.CommShift ℤ :=
  (commShiftKIso_yonedaDGFunctor A).commShift

variable [Limits.HasZeroObject A] [Limits.HasBinaryBiproducts A]

/-- **`K(h) : K(Comp^dg(A)) ⥤ K(Mod^dg(Comp^dg(A)))` is an exact functor of triangulated
categories.** This is Tag 0FQF for the `C` of Tag 09LK, with no strictness hypothesis anywhere:
the axiom (B) of `CochainComplex.dgConeSituationIso` is additive on objects only up to
isomorphism, and the two coherences its comparison isomorphisms need are
`CochainComplex.kIso_zero_yoneda` and `CochainComplex.kIso_add_yoneda`. -/
instance yonedaOnK_isTriangulated :
    (DGCategory.yonedaDGFunctor (dgCategory A)).onK.IsTriangulated :=
  DGCategory.isTriangulated_yonedaOnK_of_commShiftKIso (dgConeSituationIso A)
    (dgShiftAxiomBIso_roundTripCoherent A) (commShiftKIso_yonedaDGFunctor A)

end CochainComplex

end
