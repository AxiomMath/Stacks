module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Lower shriek of presheaves of modules along a functor with invertible slices

Let `F : C ⥤ D` be a functor and `R` a presheaf of rings on `D`. Restriction of modules along
`F`, from presheaves of `R`-modules to presheaves of `F.op ⋙ R`-modules, has a left adjoint
*lower shriek*, and one may ask whether its underlying presheaf of abelian groups is the left
Kan extension along `F.op` of the underlying presheaf of abelian groups. In general it is not:
the canonical comparison is not an isomorphism, as
`Stacks.SheafOfModules.lowerShriekForget_not_isomorphic` shows. This file proves that it *is*
an isomorphism whenever every slice functor `Over x ⥤ Over (F.obj x)` of `F` is an equivalence.

The reason is cofinality. The left Kan extension at `y` is the colimit of `M` over the
costructured-arrow category of `F.op` above `y`, whose objects are the pairs `(x, F x ⟶ y)`. The
slice hypothesis makes the pairs whose arrow is *invertible* final in that category, so the
colimit may be taken over them alone — and on such a pair a section of `R` over `y` can be
transported to `F x` along the inverse of the arrow, which is what defines the scalar action on
the colimit. Over a general `F` there is no such transport, and the comparison fails.

## Main definitions

* `Stacks.ModuleLowerShriek.invertibleArrows`: the invertible costructured arrows above `y`.
* `Stacks.ModuleLowerShriek.lanScalar`: the action of `R y` on the value at `y` of the left Kan
  extension of the underlying abelian presheaf.
* `Stacks.ModuleLowerShriek.moduleLan`: lower shriek of a presheaf of modules, namely that left
  Kan extension carrying that action.
* `Stacks.ModuleLowerShriek.presheafSmul`: multiplication by a section of the ring presheaf, as
  an endomorphism of the underlying abelian presheaf at an object.

## Main results

* `Stacks.ModuleLowerShriek.invertibleArrows_final`: the invertible arrows are final.
* `Stacks.ModuleLowerShriek.moduleLanAdjunction`: `moduleLan` is left adjoint to restriction.
* `Stacks.ModuleLowerShriek.pullbackCompToPresheafIso`: the underlying abelian presheaf of
  `PresheafOfModules.pullback (𝟙 (F.op ⋙ R))` is the left Kan extension along `F.op`.

## Implementation notes

The scalar action is obtained by descending `scalarDiagramEnd`, an endomorphism of the diagram
of invertible arrows, through the colimit. Its ring-homomorphism axioms are proved on the legs
of that colimit, and `presheafSmul` states `ModuleCat.smul` at the type it has in the diagram:
`ModuleCat.smul` has the type of an endomorphism of `(forget₂ _ AddCommGrpCat).obj (M.obj X)`,
which is the sections group only after unfolding `PresheafOfModules.presheaf`. `invertibleLeg`
does the same for the legs of the cocone, whose codomain is otherwise `(invertibleCocone _).pt`;
`invertibleLeg_eq` is the corresponding definitional identification.

Lower shriek is built by hand rather than taken as `PresheafOfModules.pullback`, whose existence
is an `IsRightAdjoint` hypothesis; `pullbackCompToPresheafIso` then compares the two by
uniqueness of left adjoints, so the final statement carries that hypothesis while the construction
does not.

## References

* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
* [Stacks Project, Tag 06X2](https://stacks.math.columbia.edu/tag/06X2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe a u u₁ u₂ u₃ v₁ v₂ v₃

namespace Stacks.ModuleLowerShriek

section Smul

variable {E : Type u₃} [Category.{v₃} E] {T : Eᵒᵖ ⥤ RingCat.{u}}

/-- Multiplication by a section of the ring presheaf, as an endomorphism of the underlying
abelian presheaf at that object: `ModuleCat.smul`, as an endomorphism of `N.presheaf.obj X`. -/
noncomputable def presheafSmul (N : PresheafOfModules.{a} T) (X : Eᵒᵖ) (r : T.obj X) :
    N.presheaf.obj X ⟶ N.presheaf.obj X :=
  ((N.obj X).smul r).asHom

variable (N : PresheafOfModules.{a} T) (X : Eᵒᵖ)

/-- Multiplication by the zero scalar is the zero endomorphism. -/
@[simp]
theorem presheafSmul_zero : presheafSmul N X 0 = 0 := by
  ext m
  exact zero_smul _ _

/-- Multiplication by the unit scalar is the identity. -/
@[simp]
theorem presheafSmul_one : presheafSmul N X 1 = 𝟙 _ := by
  ext m
  exact one_smul _ _

/-- Multiplication by a sum of scalars is the sum of the multiplications. -/
theorem presheafSmul_add (r s : T.obj X) :
    presheafSmul N X (r + s) = presheafSmul N X r + presheafSmul N X s := by
  ext m
  exact add_smul _ _ _

/-- Multiplication by `r * s` is multiplication by `s` followed by multiplication by `r`. -/
theorem presheafSmul_mul (r s : T.obj X) :
    presheafSmul N X (r * s) = presheafSmul N X s ≫ presheafSmul N X r := by
  ext m
  exact mul_smul r s m

/-- Scalar multiplication commutes with the restriction maps of a presheaf of modules. -/
theorem presheafSmul_comp_map {X Y : Eᵒᵖ} (f : X ⟶ Y) (r : T.obj X) :
    presheafSmul N X r ≫ N.presheaf.map f =
      N.presheaf.map f ≫ presheafSmul N Y (T.map f r) := by
  ext m
  exact (N.map f).hom.map_smul r m

/-- Scalar multiplication commutes with a morphism of presheaves of modules. -/
theorem presheafSmul_comp_app {N' : PresheafOfModules.{a} T} (α : N ⟶ N') (r : T.obj X) :
    presheafSmul N X r ≫ ((PresheafOfModules.toPresheaf T).map α).app X =
      ((PresheafOfModules.toPresheaf T).map α).app X ≫ presheafSmul N' X r := by
  ext m
  exact (α.app X).hom.map_smul r m

end Smul

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

/-- The invertible objects of the costructured-arrow category of `F.op` over `y`: those
`(x, F x ⟶ y)` whose structural arrow is an isomorphism. -/
abbrev invertibleArrows (y : Dᵒᵖ) : ObjectProperty (CostructuredArrow F.op y) :=
  fun k => IsIso k.hom

/-- If every slice functor `Over x ⥤ Over (F.obj x)` of `F` is an equivalence, then the
invertible costructured arrows over `y` are final among all of them. -/
theorem invertibleArrows_final [∀ x : C, (Over.post (X := x) F).IsEquivalence] (y : Dᵒᵖ) :
    (invertibleArrows F y).ι.Final := by
  constructor
  intro k
  let P := Over.post (X := k.left.unop) F
  let z := P.objPreimage (Over.mk k.hom.unop)
  let e := P.objObjPreimageIso (Over.mk k.hom.unop)
  let i : F.obj z.left ≅ y.unop := (Over.forget _).mapIso e
  let s : (invertibleArrows F y).FullSubcategory :=
    ⟨CostructuredArrow.mk (Y := op z.left) i.inv.op, inferInstanceAs (IsIso i.inv.op)⟩
  have hi : F.map z.hom = i.hom ≫ k.hom.unop := e.hom.w.symm
  let a : k ⟶ s.obj := CostructuredArrow.homMk z.hom.op (by
    apply Quiver.Hom.unop_inj
    change i.inv ≫ F.map z.hom = k.hom.unop
    rw [hi, Iso.inv_hom_id_assoc])
  let t : StructuredArrow k (invertibleArrows F y).ι := StructuredArrow.mk (Y := s) a
  have ht (b : StructuredArrow k (invertibleArrows F y).ι) : Nonempty (t ⟶ b) := by
    have hb : IsIso b.right.obj.hom := b.right.property
    have hbu : IsIso b.right.obj.hom.unop := isIso_unop _
    let jb : y.unop ≅ F.obj b.right.obj.left.unop := asIso b.right.obj.hom.unop
    have hw : jb.hom ≫ F.map b.hom.left.unop = k.hom.unop :=
      congrArg Quiver.Hom.unop (CostructuredArrow.w b.hom)
    let w : P.obj (Over.mk b.hom.left.unop) ⟶ P.obj z :=
      Over.homMk (jb.inv ≫ i.inv) (by
        change (jb.inv ≫ i.inv) ≫ F.map z.hom = F.map b.hom.left.unop
        rw [hi]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [← hw, Iso.inv_hom_id_assoc])
    have hf : F.map (P.preimage w).left = jb.inv ≫ i.inv :=
      congrArg CommaMorphism.left (P.map_preimage w)
    let c : s ⟶ b.right := ObjectProperty.homMk
      (CostructuredArrow.homMk (P.preimage w).left.op (by
        apply Quiver.Hom.unop_inj
        change jb.hom ≫ F.map (P.preimage w).left = i.inv
        rw [hf, Iso.hom_inv_id_assoc]))
    exact ⟨StructuredArrow.homMk c (by
      ext
      exact (P.preimage w).w)⟩
  have : Nonempty (StructuredArrow k (invertibleArrows F y).ι) := ⟨t⟩
  exact zigzag_isConnected (fun b c => Zigzag.of_inv_hom (ht b).some (ht c).some)

variable (R : Dᵒᵖ ⥤ RingCat.{u}) (M : PresheafOfModules.{a} (F.op ⋙ R))

/-- Along a morphism of invertible costructured arrows, transporting a scalar from `y` to the
source and then along the morphism is transporting it to the target. -/
theorem inv_hom_comp_map {y : Dᵒᵖ} {k l : (invertibleArrows F y).FullSubcategory} (f : k ⟶ l) :
    haveI : IsIso k.obj.hom := k.property
    haveI : IsIso l.obj.hom := l.property
    inv k.obj.hom ≫ F.op.map f.hom.left = inv l.obj.hom := by
  have hk : IsIso k.obj.hom := k.property
  have hl : IsIso l.obj.hom := l.property
  rw [← cancel_mono l.obj.hom, Category.assoc, CostructuredArrow.w,
    IsIso.inv_hom_id, IsIso.inv_hom_id]

/-- The scalar transported to the index `k` from `y` along the inverse of the structural
isomorphism of `k`. -/
noncomputable def transportScalar {y : Dᵒᵖ} (k : (invertibleArrows F y).FullSubcategory)
    (r : R.obj y) : (F.op ⋙ R).obj k.obj.left :=
  haveI : IsIso k.obj.hom := k.property
  R.map (inv k.obj.hom) r

/-- Transporting a scalar to `k` and then along a morphism `k ⟶ l` is transporting it to `l`. -/
theorem transportScalar_naturality {y : Dᵒᵖ} {k l : (invertibleArrows F y).FullSubcategory}
    (f : k ⟶ l) (r : R.obj y) :
    (F.op ⋙ R).map f.hom.left (transportScalar F R k r) = transportScalar F R l r := by
  have hk : IsIso k.obj.hom := k.property
  have hl : IsIso l.obj.hom := l.property
  exact ConcreteCategory.congr_hom (by
    rw [← R.map_comp, inv_hom_comp_map] :
      R.map (inv k.obj.hom) ≫ R.map (F.op.map f.hom.left) = R.map (inv l.obj.hom)) r

/-- Transport of scalars sends `0` to `0`. -/
@[simp]
theorem transportScalar_zero {y : Dᵒᵖ} (k : (invertibleArrows F y).FullSubcategory) :
    transportScalar F R k (0 : R.obj y) = 0 :=
  map_zero _

/-- Transport of scalars sends `1` to `1`. -/
@[simp]
theorem transportScalar_one {y : Dᵒᵖ} (k : (invertibleArrows F y).FullSubcategory) :
    transportScalar F R k (1 : R.obj y) = 1 :=
  map_one _

/-- Transport of scalars is additive. -/
theorem transportScalar_add {y : Dᵒᵖ} (k : (invertibleArrows F y).FullSubcategory)
    (r s : R.obj y) :
    transportScalar F R k (r + s) = transportScalar F R k r + transportScalar F R k s :=
  map_add _ _ _

/-- Transport of scalars is multiplicative. -/
theorem transportScalar_mul {y : Dᵒᵖ} (k : (invertibleArrows F y).FullSubcategory)
    (r s : R.obj y) :
    transportScalar F R k (r * s) = transportScalar F R k r * transportScalar F R k s :=
  map_mul _ _ _

/-- Multiplication by a scalar of `R y` on the diagram of invertible costructured arrows over
`y`: at the index `(x, φ : F x ≅ y)` it is multiplication by the scalar transported along
`φ⁻¹`. The transport rule of `R` makes this an endomorphism of the whole diagram. -/
noncomputable def scalarDiagramEnd (y : Dᵒᵖ) (r : R.obj y) :
    ((invertibleArrows F y).ι ⋙ CostructuredArrow.proj F.op y ⋙ M.presheaf) ⟶
      ((invertibleArrows F y).ι ⋙ CostructuredArrow.proj F.op y ⋙ M.presheaf) where
  app k := presheafSmul M k.obj.left (transportScalar F R k r)
  naturality k l f := by
    change M.presheaf.map f.hom.left ≫ presheafSmul M l.obj.left (transportScalar F R l r) =
      presheafSmul M k.obj.left (transportScalar F R k r) ≫ M.presheaf.map f.hom.left
    rw [presheafSmul_comp_map, transportScalar_naturality]

/-- At the index `k`, `scalarDiagramEnd` is multiplication by the scalar transported to `k`. -/
@[simp]
theorem scalarDiagramEnd_app (y : Dᵒᵖ) (r : R.obj y)
    (k : (invertibleArrows F y).FullSubcategory) :
    (scalarDiagramEnd F R M y r).app k = presheafSmul M k.obj.left (transportScalar F R k r) :=
  rfl

variable [∀ x : C, (Over.post (X := x) F).IsEquivalence]
variable [F.op.HasPointwiseLeftKanExtension M.presheaf]

/-- The left Kan extension along `F.op` of the abelian presheaf underlying `M`. -/
noncomputable abbrev abLan := F.op.leftKanExtension M.presheaf

/-- The unit of the left Kan extension along `F.op` of the abelian presheaf underlying `M`. -/
noncomputable abbrev abLanUnit := F.op.leftKanExtensionUnit M.presheaf

/-- The colimit cocone computing the left Kan extension at `y`, restricted to the invertible
costructured arrows over `y`. -/
noncomputable def invertibleCocone (y : Dᵒᵖ) :=
  (Functor.LeftExtension.mk _ (abLanUnit F R M)).coconeAt y |>.whisker (invertibleArrows F y).ι

/-- Restricting the pointwise colimit cocone of the left Kan extension to the invertible
costructured arrows over `y` leaves it a colimit cocone. -/
noncomputable def isColimitInvertibleCocone (y : Dᵒᵖ) :
    IsColimit (invertibleCocone F R M y) :=
  haveI := invertibleArrows_final F y
  (Functor.Final.isColimitWhiskerEquiv (invertibleArrows F y).ι _).symm
    (F.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit M.presheaf y)

/-- The leg of the colimit cocone at an invertible costructured arrow `k`, with the value of the
left Kan extension at `y` as its codomain. -/
noncomputable def invertibleLeg (y : Dᵒᵖ) (k : (invertibleArrows F y).FullSubcategory) :
    M.presheaf.obj k.obj.left ⟶ (abLan F R M).obj y :=
  (invertibleCocone F R M y).ι.app k

omit [∀ x : C, (Over.post (X := x) F).IsEquivalence] in
/-- The leg at `k` is the Kan-extension unit followed by the transition map of `k`. -/
theorem invertibleLeg_eq (y : Dᵒᵖ) (k : (invertibleArrows F y).FullSubcategory) :
    invertibleLeg F R M y k =
      (abLanUnit F R M).app k.obj.left ≫ (abLan F R M).map k.obj.hom :=
  rfl

/-- The legs at the invertible costructured arrows over `y` are jointly epimorphic. -/
theorem hom_ext_of_invertibleLeg {y : Dᵒᵖ} {W : AddCommGrpCat.{a}}
    {f g : (abLan F R M).obj y ⟶ W}
    (h : ∀ k, invertibleLeg F R M y k ≫ f = invertibleLeg F R M y k ≫ g) : f = g :=
  (isColimitInvertibleCocone F R M y).hom_ext h

/-- Multiplication by a scalar of `R y` on the value at `y` of the left Kan extension of the
abelian presheaf underlying `M`: the scalar acts on each invertible leg of the colimit by
transport along the inverse of its structural isomorphism, and those actions are compatible, so
they descend to the colimit. -/
noncomputable def lanSmul (y : Dᵒᵖ) (r : R.obj y) :
    (abLan F R M).obj y ⟶ (abLan F R M).obj y :=
  (isColimitInvertibleCocone F R M y).desc
    ⟨_, scalarDiagramEnd F R M y r ≫ (invertibleCocone F R M y).ι⟩

/-- The defining property of `lanSmul`: on the leg indexed by `k` it is the action of the
transported scalar on `M`. -/
theorem invertibleLeg_comp_lanSmul (y : Dᵒᵖ) (r : R.obj y)
    (k : (invertibleArrows F y).FullSubcategory) :
    invertibleLeg F R M y k ≫ lanSmul F R M y r =
      presheafSmul M k.obj.left (transportScalar F R k r) ≫ invertibleLeg F R M y k :=
  (isColimitInvertibleCocone F R M y).fac _ k

/-- Multiplication by the zero scalar on the left Kan extension is zero. -/
theorem lanSmul_zero (y : Dᵒᵖ) : lanSmul F R M y 0 = 0 := by
  refine hom_ext_of_invertibleLeg F R M (fun k => ?_)
  rw [invertibleLeg_comp_lanSmul, transportScalar_zero, presheafSmul_zero, zero_comp,
    comp_zero]

/-- Multiplication by the unit scalar on the left Kan extension is the identity. -/
theorem lanSmul_one (y : Dᵒᵖ) : lanSmul F R M y 1 = 𝟙 _ := by
  refine hom_ext_of_invertibleLeg F R M (fun k => ?_)
  rw [invertibleLeg_comp_lanSmul, transportScalar_one, presheafSmul_one, Category.id_comp,
    Category.comp_id]

/-- Multiplication on the left Kan extension is additive in the scalar. -/
theorem lanSmul_add (y : Dᵒᵖ) (r s : R.obj y) :
    lanSmul F R M y (r + s) = lanSmul F R M y r + lanSmul F R M y s := by
  refine hom_ext_of_invertibleLeg F R M (fun k => ?_)
  rw [invertibleLeg_comp_lanSmul, transportScalar_add, presheafSmul_add,
    Preadditive.add_comp, Preadditive.comp_add, invertibleLeg_comp_lanSmul,
    invertibleLeg_comp_lanSmul]

/-- Multiplication by `r * s` on the left Kan extension is multiplication by `s` followed by
multiplication by `r`. -/
theorem lanSmul_mul (y : Dᵒᵖ) (r s : R.obj y) :
    lanSmul F R M y (r * s) = lanSmul F R M y s ≫ lanSmul F R M y r := by
  refine hom_ext_of_invertibleLeg F R M (fun k => ?_)
  rw [invertibleLeg_comp_lanSmul, transportScalar_mul, presheafSmul_mul, Category.assoc,
    ← invertibleLeg_comp_lanSmul, ← Category.assoc, ← invertibleLeg_comp_lanSmul,
    Category.assoc]

/-- The action of `R y` on the value at `y` of the left Kan extension of the abelian presheaf
underlying `M`, as a ring homomorphism into its endomorphisms. -/
noncomputable def lanScalar (y : Dᵒᵖ) : R.obj y →+* End ((abLan F R M).obj y) where
  toFun r := End.of (lanSmul F R M y r)
  map_zero' := End.ext (lanSmul_zero F R M y)
  map_one' := End.ext (lanSmul_one F R M y)
  map_add' r s := End.ext (lanSmul_add F R M y r s)
  map_mul' r s := End.ext (lanSmul_mul F R M y r s)

/-- The value at `y` of the left Kan extension, as an `R y`-module. -/
noncomputable def lanModule (y : Dᵒᵖ) := ModuleCat.mkOfSMul (lanScalar F R M y)

/-- Semilinearity of the Kan-extension unit followed by an invertible transition map. -/
theorem lanSmul_leg_of_isIso {x : Cᵒᵖ} {y : Dᵒᵖ} (f : F.op.obj x ⟶ y) [IsIso f]
    (r : R.obj (F.op.obj x)) :
    presheafSmul M x r ≫ (abLanUnit F R M).app x ≫ (abLan F R M).map f =
      (abLanUnit F R M).app x ≫ (abLan F R M).map f ≫ lanSmul F R M y (R.map f r) := by
  have hr : transportScalar F R
      (⟨CostructuredArrow.mk f, show IsIso f from inferInstance⟩ :
        (invertibleArrows F y).FullSubcategory) (R.map f r) = r := by
    change R.map (inv f) (R.map f r) = r
    simp
  have h := invertibleLeg_comp_lanSmul F R M y (R.map f r)
    ⟨CostructuredArrow.mk f, show IsIso f from inferInstance⟩
  rw [hr, invertibleLeg_eq] at h
  simpa only [CostructuredArrow.mk_left, CostructuredArrow.mk_hom_eq_self,
    Category.assoc] using h.symm

/-- Semilinearity of the Kan-extension unit followed by an arbitrary transition map. -/
theorem lanSmul_leg {x : Cᵒᵖ} {y : Dᵒᵖ} (f : F.op.obj x ⟶ y) (r : R.obj (F.op.obj x)) :
    presheafSmul M x r ≫ (abLanUnit F R M).app x ≫ (abLan F R M).map f =
      (abLanUnit F R M).app x ≫ (abLan F R M).map f ≫ lanSmul F R M y (R.map f r) := by
  have := invertibleArrows_final F y
  let k : CostructuredArrow F.op y := CostructuredArrow.mk f
  let s := Functor.Final.lift (invertibleArrows F y).ι k
  let a := Functor.Final.homToLift (invertibleArrows F y).ι k
  have : IsIso s.obj.hom := s.property
  have ha : F.op.map a.left ≫ s.obj.hom = f := CostructuredArrow.w a
  have hn : M.presheaf.map a.left ≫ (abLanUnit F R M).app s.obj.left =
      (abLanUnit F R M).app x ≫ (abLan F R M).map (F.op.map a.left) :=
    (abLanUnit F R M).naturality a.left
  have he : (abLanUnit F R M).app x ≫ (abLan F R M).map f =
      M.presheaf.map a.left ≫ (abLanUnit F R M).app s.obj.left ≫
        (abLan F R M).map s.obj.hom := by
    rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, ha]
  have hr : R.map s.obj.hom (R.map (F.op.map a.left) r) = R.map f r := by
    change (R.map (F.op.map a.left) ≫ R.map s.obj.hom) r = _
    rw [← R.map_comp, ha]
  calc
    _ = presheafSmul M x r ≫ M.presheaf.map a.left ≫
        (abLanUnit F R M).app s.obj.left ≫ (abLan F R M).map s.obj.hom := by rw [he]
    _ = M.presheaf.map a.left ≫ presheafSmul M s.obj.left (R.map (F.op.map a.left) r) ≫
        (abLanUnit F R M).app s.obj.left ≫ (abLan F R M).map s.obj.hom := by
      rw [← Category.assoc, presheafSmul_comp_map, Category.assoc]
      rfl
    _ = M.presheaf.map a.left ≫ (abLanUnit F R M).app s.obj.left ≫
        (abLan F R M).map s.obj.hom ≫ lanSmul F R M y (R.map f r) := by
      simpa only [hr] using congrArg (fun t => M.presheaf.map a.left ≫ t)
        (lanSmul_leg_of_isIso F R M s.obj.hom (R.map (F.op.map a.left) r))
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun t => t ≫ lanSmul F R M y (R.map f r)) he.symm

/-- The scalar actions on the values of the left Kan extension are compatible with its
restriction maps. -/
theorem lanSmul_naturality {y z : Dᵒᵖ} (f : y ⟶ z) (r : R.obj y) :
    lanSmul F R M y r ≫ (abLan F R M).map f =
      (abLan F R M).map f ≫ lanSmul F R M z (R.map f r) := by
  refine hom_ext_of_invertibleLeg F R M (fun k => ?_)
  have hk : IsIso k.obj.hom := k.property
  have hr : R.map (k.obj.hom ≫ f) (transportScalar F R k r) = R.map f r := by
    simp [transportScalar]
  have h := lanSmul_leg F R M (k.obj.hom ≫ f) (transportScalar F R k r)
  rw [hr, (abLan F R M).map_comp] at h
  rw [← Category.assoc, invertibleLeg_comp_lanSmul, Category.assoc, invertibleLeg_eq]
  simpa only [Category.assoc] using h

/-- **Lower shriek of a presheaf of modules.** The left Kan extension of the underlying abelian
presheaf, with the scalar action of `lanScalar`, is a presheaf of `R`-modules. -/
noncomputable def moduleLan : PresheafOfModules.{a} R where
  obj y := lanModule F R M y
  map f := ModuleCat.homMk ((abLan F R M).map f)
    (fun r => (lanSmul_naturality F R M f r).symm)
  map_id y := (forget₂ _ AddCommGrpCat).map_injective ((abLan F R M).map_id y)
  map_comp f g := (forget₂ _ AddCommGrpCat).map_injective ((abLan F R M).map_comp f g)

/-- The unit of lower shriek on presheaves of modules: the Kan-extension unit. -/
noncomputable def moduleLanUnit :
    M ⟶ (PresheafOfModules.pushforward (F := F) (𝟙 (F.op ⋙ R))).obj (moduleLan F R M) :=
  PresheafOfModules.homMk (abLanUnit F R M) (fun x r m => by
    have h := ConcreteCategory.congr_hom (lanSmul_leg F R M (𝟙 (F.op.obj x)) r) m
    simp only [(abLan F R M).map_id, R.map_id, RingCat.id_apply] at h
    exact h)

/-- A morphism from `M` to the restriction of a presheaf of `R`-modules `N`, read at an object
`x` as a map into the sections of `N` over `F x`. -/
noncomputable def restrictionApp (N : PresheafOfModules.{a} R)
    (α : M ⟶ (PresheafOfModules.pushforward (F := F) (𝟙 (F.op ⋙ R))).obj N) (x : Cᵒᵖ) :
    M.presheaf.obj x ⟶ N.presheaf.obj (F.op.obj x) :=
  ((PresheafOfModules.toPresheaf _).map α).app x

omit [∀ x : C, (Over.post (X := x) F).IsEquivalence]
  [F.op.HasPointwiseLeftKanExtension M.presheaf] in
/-- `restrictionApp` is semilinear over the scalars of `F x`. -/
theorem presheafSmul_comp_restrictionApp (N : PresheafOfModules.{a} R)
    (α : M ⟶ (PresheafOfModules.pushforward (F := F) (𝟙 (F.op ⋙ R))).obj N) (x : Cᵒᵖ)
    (r : R.obj (F.op.obj x)) :
    presheafSmul M x r ≫ restrictionApp F R M N α x =
      restrictionApp F R M N α x ≫ presheafSmul N (F.op.obj x) r := by
  ext m
  exact (α.app x).hom.map_smul r m

/-- The universal property of lower shriek on presheaves of modules: a morphism from `M` to the
restriction of `N` descends to a morphism `moduleLan M ⟶ N`. -/
noncomputable def moduleLanDesc (N : PresheafOfModules.{a} R)
    (α : M ⟶ (PresheafOfModules.pushforward (F := F) (𝟙 (F.op ⋙ R))).obj N) :
    moduleLan F R M ⟶ N := by
  let β := (abLan F R M).descOfIsLeftKanExtension (abLanUnit F R M) N.presheaf
    ((PresheafOfModules.toPresheaf _).map α)
  have hb {x : Cᵒᵖ} {y : Dᵒᵖ} (f : F.op.obj x ⟶ y) :
      (abLanUnit F R M).app x ≫ (abLan F R M).map f ≫ β.app y =
        restrictionApp F R M N α x ≫ N.presheaf.map f := by
    rw [β.naturality, ← Category.assoc]
    exact congrArg (fun t => t ≫ N.presheaf.map f)
      ((abLan F R M).descOfIsLeftKanExtension_fac_app (abLanUnit F R M)
        N.presheaf ((PresheafOfModules.toPresheaf _).map α) x)
  refine PresheafOfModules.homMk β (fun y r m => ?_)
  have h : lanSmul F R M y r ≫ β.app y = β.app y ≫ presheafSmul N y r := by
    refine hom_ext_of_invertibleLeg F R M (fun k => ?_)
    have hk : IsIso k.obj.hom := k.property
    have hr : R.map k.obj.hom (transportScalar F R k r) = r := by
      change (R.map (inv k.obj.hom) ≫ R.map k.obj.hom) r = _
      rw [← R.map_comp, IsIso.inv_hom_id, R.map_id]
      rfl
    have key : invertibleLeg F R M y k ≫ β.app y =
        restrictionApp F R M N α k.obj.left ≫ N.presheaf.map k.obj.hom := by
      rw [invertibleLeg_eq, Category.assoc]
      exact hb k.obj.hom
    have hsmul' : presheafSmul M k.obj.left (transportScalar F R k r) ≫
          restrictionApp F R M N α k.obj.left ≫ N.presheaf.map k.obj.hom =
        restrictionApp F R M N α k.obj.left ≫
          presheafSmul N (F.op.obj k.obj.left) (transportScalar F R k r) ≫
            N.presheaf.map k.obj.hom := by
      rw [← Category.assoc, presheafSmul_comp_restrictionApp, Category.assoc]
    calc invertibleLeg F R M y k ≫ lanSmul F R M y r ≫ β.app y
        = presheafSmul M k.obj.left (transportScalar F R k r) ≫
            invertibleLeg F R M y k ≫ β.app y := by
          rw [← Category.assoc, invertibleLeg_comp_lanSmul, Category.assoc]
      _ = restrictionApp F R M N α k.obj.left ≫
            presheafSmul N (F.op.obj k.obj.left) (transportScalar F R k r) ≫
              N.presheaf.map k.obj.hom := by
          rw [key, hsmul']
      _ = invertibleLeg F R M y k ≫ β.app y ≫ presheafSmul N y r := by
          rw [presheafSmul_comp_map, hr, ← Category.assoc, ← key, Category.assoc]
  exact ConcreteCategory.congr_hom h m

/-- Lower shriek on presheaves of modules is left adjoint to restriction, objectwise. -/
noncomputable def moduleLanHomEquiv (N : PresheafOfModules.{a} R) :
    (moduleLan F R M ⟶ N) ≃
      (M ⟶ (PresheafOfModules.pushforward (F := F) (𝟙 (F.op ⋙ R))).obj N) where
  toFun g := moduleLanUnit F R M ≫ (PresheafOfModules.pushforward _).map g
  invFun := moduleLanDesc F R M N
  left_inv g := by
    apply (PresheafOfModules.toPresheaf _).map_injective
    apply (abLan F R M).hom_ext_of_isLeftKanExtension (abLanUnit F R M)
    change (abLanUnit F R M) ≫ Functor.whiskerLeft F.op
      ((abLan F R M).descOfIsLeftKanExtension (abLanUnit F R M) N.presheaf
        ((abLanUnit F R M) ≫ Functor.whiskerLeft F.op
          ((PresheafOfModules.toPresheaf _).map g))) = _
    exact (abLan F R M).descOfIsLeftKanExtension_fac _ _ _
  right_inv α :=
    (PresheafOfModules.toPresheaf _).map_injective
      ((abLan F R M).descOfIsLeftKanExtension_fac _ _ _)

/-- The objectwise adjunction of `moduleLanHomEquiv` is natural in the target. -/
theorem moduleLanHomEquiv_naturality (N N' : PresheafOfModules.{a} R)
    (g : N ⟶ N') (h : moduleLan F R M ⟶ N) :
    moduleLanHomEquiv F R M N' (h ≫ g) =
      moduleLanHomEquiv F R M N h ≫ (PresheafOfModules.pushforward _).map g := by
  change moduleLanUnit F R M ≫ (PresheafOfModules.pushforward _).map (h ≫ g) =
    (moduleLanUnit F R M ≫ (PresheafOfModules.pushforward _).map h) ≫
      (PresheafOfModules.pushforward _).map g
  rw [Functor.map_comp, Category.assoc]

variable [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{a}, F.op.HasPointwiseLeftKanExtension G]

/-- **Lower shriek on presheaves of modules is left adjoint to restriction.** -/
noncomputable def moduleLanAdjunction :
    Adjunction.leftAdjointOfEquiv
      (fun M N => moduleLanHomEquiv F R M N)
      (fun M N N' g h => moduleLanHomEquiv_naturality F R M N N' g h) ⊣
        PresheafOfModules.pushforward (F := F) (𝟙 (F.op ⋙ R)) :=
  Adjunction.adjunctionOfEquivLeft _ _

/-- **Lower shriek of presheaves of modules has the left Kan extension of the underlying
abelian presheaf as its underlying abelian presheaf**, when every slice functor of `F` is an
equivalence. -/
noncomputable def pullbackCompToPresheafIso
    [(PresheafOfModules.pushforward.{a} (F := F) (𝟙 (F.op ⋙ R))).IsRightAdjoint] :
    PresheafOfModules.pullback.{a} (F := F) (𝟙 (F.op ⋙ R)) ⋙
        PresheafOfModules.toPresheaf R ≅
      PresheafOfModules.toPresheaf (F.op ⋙ R) ⋙ F.op.lan :=
  Functor.isoWhiskerRight
    (Adjunction.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction _)
      (moduleLanAdjunction F R)) _ ≪≫
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by rfl)

end Stacks.ModuleLowerShriek

end
