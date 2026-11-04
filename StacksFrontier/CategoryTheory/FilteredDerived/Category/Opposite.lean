module

public import Mathlib.CategoryTheory.Abelian.Opposite
public import StacksCore.CategoryTheory.Abelian.Basic
public import StacksCore.CategoryTheory.Filtration.GradedExact
public import StacksFrontier.CategoryTheory.FilteredDerived.Category.Projective

/-!
# Finite filtered objects of the opposite category

Let `A` be an abelian category. A finite filtration `F^• X` of an object of `A` becomes, read
in `Aᵒᵖ`, the filtration of `op X` whose `p`-th step is `op (X / F^{-p} X)`: the quotient maps
of the original filtration are monomorphisms after passing to the opposite category, and
reversing the index turns the resulting increasing family into a decreasing one. This
construction and the inverse one, which takes the kernels of the inclusions of a filtration of
`Aᵒᵖ`, are mutually inverse and exhibit `Fil^f(A)ᵒᵖ` as `Fil^f(Aᵒᵖ)`. Under this
identification the `p`-th graded piece becomes the `(-p-1)`-st graded piece of the original
object, so filtered projective objects become filtered injective ones.

## Main definitions

* `CategoryTheory.FilteredDerived.dualFilteredObject`: the quotient filtration of `op X`.
* `CategoryTheory.FilteredDerived.dualBackFilteredObject`: the kernel filtration recovering a
  filtered object of `A` from a filtered object of `Aᵒᵖ`.
* `CategoryTheory.FilteredDerived.dualFiniteFunctor`: the contravariant functor
  `Fil^f(A)ᵒᵖ ⥤ Fil^f(Aᵒᵖ)`.
* `CategoryTheory.FilteredDerived.dualFiniteEquivalence`: the equivalence
  `Fil^f(A)ᵒᵖ ≌ Fil^f(Aᵒᵖ)`.

## Main results

* `CategoryTheory.FilteredDerived.dualGrIso`: the `p`-th graded piece of the quotient
  filtration is the opposite of the `(-p-1)`-st graded piece.
* `CategoryTheory.FilteredDerived.dualGrNatIso`: the same statement, naturally in the finite
  filtered object.
* `CategoryTheory.FilteredDerived.dualFinite_filteredInjective`: a filtered projective object
  becomes filtered injective in the opposite category.

## Implementation notes

`CategoryTheory.Abelian.cokernelKernelSubobjectIso` below is a general fact about abelian
categories: an epimorphism identifies its target with the quotient by its kernel subobject.
It is what makes the kernel filtration of `Aᵒᵖ` inverse to the quotient filtration of `A`,
since the steps of a filtration are recorded as subobjects.

Reindexing by `p ↦ -p` is carried out with `CategoryTheory.eqToIso` on the index category
`ℤᵒᵖ`, whose morphisms form a subsingleton; the resulting index comparisons are therefore
settled by `Subsingleton.elim` rather than by a computation.

## References

* [Stacks Project, Tag 03TB](https://stacks.math.columbia.edu/tag/03TB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject Opposite

universe v u

namespace CategoryTheory.Abelian

/-- For an epimorphism `f : X ⟶ Y` in an abelian category, the quotient of `X` by the kernel
subobject of `f` is `Y`. -/
noncomputable def cokernelKernelSubobjectIso {B : Type u} [Category.{v} B]
    [Abelian B] {X Y : B} (f : X ⟶ Y) [Epi f] :
    cokernel (kernelSubobject f).arrow ≅ Y :=
  cokernel.mapIso _ _ (kernelSubobjectIso f) (Iso.refl _) (by simp) ≪≫
    (Abelian.isoCokernelKernel f).symm

/-- An epimorphism, read through `CategoryTheory.Abelian.cokernelKernelSubobjectIso`, is the
projection to the quotient by its kernel subobject. -/
theorem cokernelKernelSubobjectIso_inv_comp {B : Type u} [Category.{v} B]
    [Abelian B] {X Y : B} (f : X ⟶ Y) [Epi f] :
    f ≫ (cokernelKernelSubobjectIso f).inv = cokernel.π (kernelSubobject f).arrow := by
  dsimp [cokernelKernelSubobjectIso]
  rw [← Category.assoc, Abelian.comp_isoCokernelKernel_hom]
  simp [cokernel.mapIso, cokernel.map]

end CategoryTheory.Abelian

namespace CategoryTheory.FilteredDerived

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- The filtration on the opposite of a finite filtered object, formed from the
successive quotient maps.  At index `p`, its step is `op (X / F^{-p} X)`. -/
noncomputable def dualFiltration (X : FilteredObject A ℤᵒᵖ) :
    Filtration (Opposite.op X.X) ℤᵒᵖ where
  toMonoOver :=
    { obj i := ⟨Over.mk (FilteredObject.quotπ (op (-i.unop)) X).op, op_mono_of_epi _⟩
      map {i j} f :=
        let f' : op (-(j.unop : ℤ)) ⟶ op (-(i.unop : ℤ)) :=
          opHomOfLE (Int.neg_le_neg (leOfHom f.unop))
        MonoOver.homMk (FilteredObject.quotStep f' X).op
          (Quiver.Hom.unop_inj (FilteredObject.quotπ_quotStep f' X))
      map_id _ := Subsingleton.elim _ _
      map_comp _ _ := Subsingleton.elim _ _ }

/-- The quotient filtration associated to `X`, considered as a filtered object
in the opposite abelian category. -/
noncomputable def dualFilteredObject (X : FilteredObject A ℤᵒᵖ) :
    FilteredObject Aᵒᵖ ℤᵒᵖ where
  X := op X.X
  filtration := dualFiltration A X

/-- The index map that occurs in the graded step of the quotient filtration. -/
def dualSuccHom (p : ℤ) : op (-p) ⟶ op (-(p + 1)) :=
  opHomOfLE (x := op (-(p + 1))) (y := op (-p))
    (show -(p + 1) ≤ -p by omega)

/-- A dual graded piece is the opposite of the kernel of a quotient transition. -/
noncomputable def dualGrMapIso (X : FilteredObject A ℤᵒᵖ) (p : ℤ) :
    (FilteredObject.gr p).obj (dualFilteredObject A X) ≅
      op ((FilteredObject.grMap (dualSuccHom p)).obj X) := by
  let u := FilteredObject.quotStep (dualSuccHom p) X
  let e : (FilteredObject.grMap (dualSuccHom p)).obj X ≅ kernel u :=
    IsLimit.conePointUniqueUpToIso
      (FilteredObject.quotStepShortComplex_shortExact (dualSuccHom p) X).fIsKernel
      (limit.isLimit (parallelPair u 0))
  change cokernel u.op ≅ _
  exact cokernelOpOp u ≪≫ e.op

/-- The consecutive index map in the quotient filtration agrees, up to the canonical
index isomorphisms, with the ordinary graded-piece map at `-p - 1`. -/
noncomputable def dualGrIso (X : FilteredObject A ℤᵒᵖ) (p : ℤ) :
    (FilteredObject.gr p).obj (dualFilteredObject A X) ≅
      op ((FilteredObject.gr (-p - 1)).obj X) := by
  have h₁ : op (-p) = op ((-p - 1) + 1) := congrArg op (by omega)
  have h₂ : op (-(p + 1)) = op (-p - 1) := congrArg op (by omega)
  let e₁ := X.filtration.diagram.mapIso (eqToIso h₁)
  let e₂ := X.filtration.diagram.mapIso (eqToIso h₂)
  have hs : X.filtration.step (dualSuccHom p) ≫ e₂.hom =
      e₁.hom ≫ X.filtration.step (FilteredObject.succHom (-p - 1)) := by
    change X.filtration.diagram.map (dualSuccHom p) ≫
        X.filtration.diagram.map (eqToHom h₂) =
      X.filtration.diagram.map (eqToHom h₁) ≫
        X.filtration.diagram.map (FilteredObject.succHom (-p - 1))
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  exact dualGrMapIso A X p ≪≫
    (cokernel.mapIso _ _ e₁ e₂ hs).symm.op

/-- The morphism part of the contravariant quotient-filtration construction. -/
noncomputable def dualHom {X Y : FilteredObject A ℤᵒᵖ} (u : Y ⟶ X) :
    dualFilteredObject A X ⟶ dualFilteredObject A Y :=
  FilteredObject.homMk u.hom.op
    (fun (i : ℤᵒᵖ) => ((FilteredObject.quot (op (-i.unop))).map u).op)
    (fun i => Quiver.Hom.unop_inj (FilteredObject.quotπ_map (op (-i.unop)) u))

/-- Dualizing a finite filtration reverses its top and bottom steps. -/
theorem dualFilteredObject_finite (X : FilteredObject A ℤᵒᵖ)
    (hX : X.filtration.IsFinite) : (dualFilteredObject A X).filtration.IsFinite := by
  obtain ⟨a, ha⟩ := hX.exists_isIso_ι
  obtain ⟨b, hb⟩ := hX.exists_isZero_obj
  have hzero : X.filtration.ι.app (op b) = 0 := hb.eq_of_src _ _
  have htop : IsIso ((dualFilteredObject A X).filtration.ι.app (op (-b))) := by
    have he : IsIso (FilteredObject.quotπ (op b) X) := by
      change IsIso (cokernel.π (X.filtration.ι.app (op b)))
      rw [hzero]
      infer_instance
    dsimp [dualFilteredObject, dualFiltration, Filtration.ι]
    rw [Int.neg_neg]
    infer_instance
  have hbot : IsZero ((dualFilteredObject A X).filtration.obj (op (-a))) := by
    simpa [dualFilteredObject, dualFiltration] using
      (FilteredObject.isZero_quot_obj_of_isIso_ι_app (op a) X).op
  exact .of_exists ⟨-b, htop⟩ ⟨-a, hbot⟩

/-- Dualization is contravariant on finite filtered objects. -/
noncomputable def dualFiniteFunctor :
    (FiniteFilteredObject A)ᵒᵖ ⥤ FiniteFilteredObject Aᵒᵖ where
  obj X := ⟨dualFilteredObject A X.unop.obj,
    dualFilteredObject_finite A X.unop.obj X.unop.property⟩
  map f := ObjectProperty.homMk (dualHom A f.unop.hom)
  map_id X := by
    apply ObjectProperty.hom_ext
    apply FilteredObject.hom_ext
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply FilteredObject.hom_ext
    rfl

/-- Dualization is an additive functor. -/
instance dualFiniteFunctor_additive : (dualFiniteFunctor A).Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    apply FilteredObject.hom_ext
    rfl

/-- The isomorphism of `CategoryTheory.FilteredDerived.dualGrMapIso` is compatible with the
projection to the graded piece and the inclusion of the kernel. -/
lemma dualGrMapIso_hom_unop_comp (X : FilteredObject A ℤᵒᵖ) (p : ℤ) :
    (dualGrMapIso A X p).hom.unop ≫
        (FilteredObject.grMapπ (FilteredObject.succHom p) (dualFilteredObject A X)).unop =
      FilteredObject.grMapι (dualSuccHom p) X := by
  let u := FilteredObject.quotStep (dualSuccHom p) X
  let hs := FilteredObject.quotStepShortComplex_shortExact (dualSuccHom p) X
  let e := hs.fIsKernel.conePointUniqueUpToIso (limit.isLimit (parallelPair u 0))
  change (e.hom ≫ (cokernelOpOp u).hom.unop) ≫ (cokernel.π u.op).unop = _
  rw [Category.assoc, cokernel.π_op]
  simp only [cokernelOpOp, eqToHom_refl, Category.comp_id]
  change e.hom ≫ (cokernelOpUnop u).inv ≫ (cokernelOpUnop u).hom ≫ kernel.ι u = _
  rw [Iso.inv_hom_id_assoc]
  exact hs.fIsKernel.conePointUniqueUpToIso_hom_comp
    (limit.isLimit (parallelPair u 0)) WalkingParallelPair.zero

/-- The graded pieces of the quotient filtration, naturally in the finite filtered object and
expressed through the kernels of the quotient transitions. -/
noncomputable def dualGrMapNatIso (p : ℤ) :
    dualFiniteFunctor A ⋙ FiniteFilteredObject.grP (𝒜 := Aᵒᵖ) p ≅
      ((show ObjectProperty (FilteredObject A ℤᵒᵖ) from fun X => X.filtration.IsFinite).ι ⋙
        FilteredObject.grMap (dualSuccHom p)).op :=
  NatIso.ofComponents (fun X => dualGrMapIso A X.unop.obj p) (by
    intro X Y f
    apply Quiver.Hom.unop_inj
    apply (cancel_mono
      (FilteredObject.grMapπ (FilteredObject.succHom p) (dualFilteredObject A X.unop.obj)).unop).1
    change ((dualGrMapIso A Y.unop.obj p).hom.unop ≫
        ((FilteredObject.grMap (FilteredObject.succHom p)).map (dualHom A f.unop.hom)).unop) ≫
        (FilteredObject.grMapπ (FilteredObject.succHom p) (dualFilteredObject A X.unop.obj)).unop =
      ((FilteredObject.grMap (dualSuccHom p)).map f.unop.hom ≫
        (dualGrMapIso A X.unop.obj p).hom.unop) ≫
        (FilteredObject.grMapπ (FilteredObject.succHom p) (dualFilteredObject A X.unop.obj)).unop
    have hn := congrArg Quiver.Hom.unop
      (FilteredObject.grMapπ_map (FilteredObject.succHom p) (dualHom A f.unop.hom))
    dsimp only [unop_comp] at hn
    rw [Category.assoc, hn, ← Category.assoc, dualGrMapIso_hom_unop_comp,
      Category.assoc, dualGrMapIso_hom_unop_comp]
    exact FilteredObject.grMapι_map _ _)

/-- The `p`-th graded piece of the quotient filtration is the opposite of the `(-p-1)`-st
graded piece of the original filtration, naturally in the finite filtered object. -/
noncomputable def dualGrNatIso (p : ℤ) :
    dualFiniteFunctor A ⋙ FiniteFilteredObject.grP (𝒜 := Aᵒᵖ) p ≅
      (FiniteFilteredObject.grP (𝒜 := A) (-p - 1)).op := by
  have h₁ : op (-p) = op ((-p - 1) + 1) := congrArg op (by omega)
  have h₂ : op (-(p + 1)) = op (-p - 1) := congrArg op (by omega)
  let e : ((show ObjectProperty (FilteredObject A ℤᵒᵖ) from fun X => X.filtration.IsFinite).ι ⋙
      FilteredObject.grMap (dualSuccHom p)) ≅
      FiniteFilteredObject.grP (𝒜 := A) (-p - 1) :=
    NatIso.ofComponents (fun X => cokernel.mapIso _ _
      (X.obj.filtration.diagram.mapIso (eqToIso h₁))
      (X.obj.filtration.diagram.mapIso (eqToIso h₂)) (by
        change X.obj.filtration.diagram.map _ ≫ X.obj.filtration.diagram.map _ =
          X.obj.filtration.diagram.map _ ≫ X.obj.filtration.diagram.map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1)) (by
      intro X Y f
      apply FilteredObject.grMap_hom_ext
      dsimp [FilteredObject.grMapπ]
      simp [cokernel.mapIso, cokernel.map, FilteredObject.grMap])
  exact dualGrMapNatIso A p ≪≫ NatIso.op e.symm

/-- The morphism in `A` opposite to the inclusion of the step at `op (-p)` of the filtration
of `Y`. -/
noncomputable def dualBackEpi (Y : FilteredObject Aᵒᵖ ℤᵒᵖ) (p : ℤ) :
    Y.X.unop ⟶ (Y.filtration.obj (op (-p))).unop :=
  (Y.filtration.ι.app (op (-p))).unop

/-- The morphism `dualBackEpi A Y p` is an epimorphism. -/
instance epi_dualBackEpi (Y : FilteredObject Aᵒᵖ ℤᵒᵖ) (p : ℤ) : Epi (dualBackEpi A Y p) := by
  dsimp [dualBackEpi]
  infer_instance

/-- The kernels of opposite filtration inclusions form an antitone family. -/
theorem dualBackFiltration_antitone (Y : FilteredObject Aᵒᵖ ℤᵒᵖ) :
    Antitone (fun p => kernelSubobject (dualBackEpi A Y p)) := by
  intro p q hpq
  let f : op (-p) ⟶ op (-q) := opHomOfLE (show -q ≤ -p by omega)
  have he : dualBackEpi A Y p = dualBackEpi A Y q ≫ (Y.filtration.step f).unop :=
    (congrArg Quiver.Hom.unop (Y.filtration.step_comp_ι_app f)).symm
  change kernelSubobject (dualBackEpi A Y q) ≤ kernelSubobject (dualBackEpi A Y p)
  rw [he]
  exact kernelSubobject_comp_le _ _

/-- Recover a finite filtration from the kernels of the opposite filtration's inclusions. -/
noncomputable def dualBackFiltration (Y : FilteredObject Aᵒᵖ ℤᵒᵖ) :
    Filtration Y.X.unop ℤᵒᵖ :=
  Filtration.ofAntitone (fun p => kernelSubobject (dualBackEpi A Y p))
    (dualBackFiltration_antitone A Y)

/-- The inverse quotient-kernel construction on filtered objects before asserting its
finiteness. -/
noncomputable def dualBackFilteredObject (Y : FilteredObject Aᵒᵖ ℤᵒᵖ) :
    FilteredObject A ℤᵒᵖ where
  X := Y.X.unop
  filtration := dualBackFiltration A Y

/-- The reconstructed filtration is finite when the opposite filtration is finite. -/
theorem dualBackFilteredObject_finite (Y : FilteredObject Aᵒᵖ ℤᵒᵖ)
    (hY : Y.filtration.IsFinite) : (dualBackFilteredObject A Y).filtration.IsFinite := by
  obtain ⟨a, ha⟩ := hY.exists_isIso_ι
  obtain ⟨b, hb⟩ := hY.exists_isZero_obj
  have htop : IsIso ((dualBackFilteredObject A Y).filtration.ι.app (op (-b))) := by
    have hzero : dualBackEpi A Y (-b) = 0 := by
      change (Y.filtration.ι.app (op (-(-b)))).unop = 0
      rw [show -(-b) = b by omega]
      simpa using congrArg Quiver.Hom.unop (hb.eq_of_src (Y.filtration.ι.app (op b)) 0)
    change IsIso (kernelSubobject (dualBackEpi A Y (-b))).arrow
    rw [hzero]
    infer_instance
  have hbot : IsZero ((dualBackFilteredObject A Y).filtration.obj (op (-a))) := by
    have : IsIso (dualBackEpi A Y (-a)) := by
      dsimp [dualBackEpi]
      rw [show -(-a) = a by omega]
      exact (isIso_unop_iff (Y.filtration.ι.app (op a))).2 ha
    exact (isZero_kernel_of_mono (dualBackEpi A Y (-a))).of_iso (kernelSubobjectIso _)
  exact .of_exists ⟨-b, htop⟩ ⟨-a, hbot⟩

/-- A filtered morphism in the opposite category restricts to the kernel filtrations. -/
noncomputable def dualBackHom {X Y : FilteredObject Aᵒᵖ ℤᵒᵖ} (f : Y ⟶ X) :
    dualBackFilteredObject A X ⟶ dualBackFilteredObject A Y :=
  FilteredObject.homMk' f.hom.unop (fun i => by
    cases i with
    | op p =>
      let m : (dualBackFilteredObject A X).X ⟶ (dualBackFilteredObject A Y).X := f.hom.unop
      let eX : (dualBackFilteredObject A X).X ⟶
          (X.filtration.obj (op (-p))).unop := dualBackEpi A X p
      let eY : (dualBackFilteredObject A Y).X ⟶
          (Y.filtration.obj (op (-p))).unop := dualBackEpi A Y p
      have hsubY : (dualBackFilteredObject A Y).subobject (op p) =
          kernelSubobject (dualBackEpi A Y p) :=
        Filtration.subobject_ofAntitone _ _ p
      rw [hsubY]
      change (kernelSubobject eY).Factors
        ((dualBackFilteredObject A X).filtration.ι.app (op p) ≫ m)
      apply (kernelSubobject_factors_iff eY _).2
      have hcomp :
          (dualBackFilteredObject A X).filtration.ι.app (op p) ≫ eX = 0 :=
        kernelSubobject_arrow_comp eX
      have hs : m ≫ eY = eX ≫
          (f.natTrans.app (op (-p))).unop := by
        have h := congrArg Quiver.Hom.unop (f.comm (op (-p)))
        simpa only [m, eX, eY, unop_comp, dualBackEpi, dualBackFilteredObject] using h.symm
      rw [Category.assoc, hs, ← Category.assoc, hcomp, zero_comp])

/-- The quotient-kernel reconstruction recovers each original filtration step. -/
theorem dualBack_dual_subobject (X : FilteredObject A ℤᵒᵖ) (p : ℤ) :
    (dualBackFilteredObject A (dualFilteredObject A X)).subobject (op p) =
      X.subobject (op p) := by
  dsimp only [dualBackFilteredObject]
  change Subobject.mk (kernelSubobject (dualBackEpi A (dualFilteredObject A X) p)).arrow = _
  rw [Subobject.mk_arrow]
  change kernelSubobject (FilteredObject.quotπ (op (-(-p))) X) = _
  rw [show -(-p) = p by omega]
  exact FilteredObject.kernelSubobject_quotπ (op p) X

/-- The quotient-kernel reconstruction recovers each original filtration step, as an equality
of the subobjects given by the inclusions. -/
theorem dualBack_dual_mk_eq (X : FilteredObject A ℤᵒᵖ) (i : ℤᵒᵖ) :
    Subobject.mk ((dualBackFilteredObject A (dualFilteredObject A X)).filtration.ι.app i) =
      Subobject.mk (X.filtration.ι.app i) := by
  simpa [FilteredObject.subobject] using dualBack_dual_subobject A X i.unop

/-- The induced isomorphism between corresponding levels of a quotient-kernel double dual. -/
noncomputable def dualBack_dual_step_iso (X : FilteredObject A ℤᵒᵖ) (i : ℤᵒᵖ) :
    (dualBackFilteredObject A (dualFilteredObject A X)).filtration.obj i ≅
      X.filtration.obj i := by
  let f := (dualBackFilteredObject A (dualFilteredObject A X)).filtration.ι.app i
  let g := X.filtration.ι.app i
  have hmk : Subobject.mk f = Subobject.mk g := dualBack_dual_mk_eq A X i
  exact @Subobject.isoOfMkEqMk A _ _ _ _ f g (inferInstance : Mono f)
    (inferInstance : Mono g) hmk

/-- Double quotient-kernel duality is the identity on finite filtered objects. -/
noncomputable def dualBack_dual_iso (X : FilteredObject A ℤᵒᵖ) :
    dualBackFilteredObject A (dualFilteredObject A X) ≅ X :=
  FilteredObject.isoMk (Iso.refl _) (dualBack_dual_step_iso A X) (by
    intro i
    dsimp only [dualBack_dual_step_iso, Subobject.isoOfMkEqMk]
    let f := (dualBackFilteredObject A (dualFilteredObject A X)).filtration.ι.app i
    let g := X.filtration.ι.app i
    have hf : Mono f := inferInstance
    have hg : Mono g := inferInstance
    have hmk : Subobject.mk f = Subobject.mk g := dualBack_dual_mk_eq A X i
    change @Subobject.ofMkLEMk A _ _ _ _ f g hf hg hmk.le ≫ g =
      f ≫ (Iso.refl _).hom
    exact (@Subobject.ofMkLEMk_comp A _ _ _ _ f g hf hg hmk.le).trans (by simp))

/-- The quotient used by the reconstructed filtration is the cokernel of its kernel step. -/
noncomputable def dualBackQuotientCokernelIso
    (Y : FilteredObject Aᵒᵖ ℤᵒᵖ) (p : ℤ) :
    ((FilteredObject.quot (op (-p))).obj (dualBackFilteredObject A Y)) ≅
      cokernel (kernelSubobject (dualBackEpi A Y (-p))).arrow := by
  dsimp [FilteredObject.quot, dualBackFilteredObject, dualBackFiltration]
  rfl

/-- The induced isomorphism between corresponding levels of a kernel-quotient double dual. -/
noncomputable def dual_dualBack_step_iso
    (Y : FilteredObject Aᵒᵖ ℤᵒᵖ) (p : ℤ) :
    (dualFilteredObject A (dualBackFilteredObject A Y)).filtration.obj (op p) ≅
      Y.filtration.obj (op p) := by
  let etop : Y.filtration.obj (op (-(-p))) ≅ Y.filtration.obj (op p) :=
    eqToIso (congrArg (fun q : ℤ => Y.filtration.obj (op q)) (by omega))
  exact Iso.refl _ ≪≫ (dualBackQuotientCokernelIso A Y p ≪≫
      Abelian.cokernelKernelSubobjectIso (dualBackEpi A Y (-p))).symm.op ≪≫ etop

/-- Kernel reconstruction followed by the opposite quotient filtration is the identity. -/
noncomputable def dual_dualBack_iso (Y : FilteredObject Aᵒᵖ ℤᵒᵖ) :
    dualFilteredObject A (dualBackFilteredObject A Y) ≅ Y :=
  FilteredObject.isoMk (Iso.refl _)
    (fun i => dual_dualBack_step_iso A Y i.unop) (by
      intro i
      cases i with
      | op p =>
        apply Quiver.Hom.unop_inj
        dsimp only [dual_dualBack_step_iso]
        simp only [Iso.trans_hom, unop_comp]
        have he : dualBackEpi A Y (-p) =
            (Y.filtration.ι.app (op (-(-p)))).unop := rfl
        have hc : (Y.filtration.ι.app (op (-(-p)))).unop ≫
            (Abelian.cokernelKernelSubobjectIso (dualBackEpi A Y (-p))).inv =
              FilteredObject.quotπ (op (-p)) (dualBackFilteredObject A Y) := by
          rw [← he, Abelian.cokernelKernelSubobjectIso_inv_comp]
          rfl
        simp only [Functor.const_obj_obj, dualBackFilteredObject, dualBackFiltration,
          Functor.comp_obj, ObjectProperty.ι_obj, Over.forget_obj, dualFilteredObject, op_unop,
          dualFiltration, Lean.Elab.WF.paramLet, Over.mk_left, dualBackQuotientCokernelIso,
          id_eq, Iso.trans_symm, Iso.op_trans, Iso.op_symm, Iso.trans_assoc, Iso.trans_hom,
          Iso.symm_hom, Iso.op_inv, Iso.refl_inv, op_id, eqToIso.hom, unop_comp, eqToHom_unop,
          Quiver.Hom.unop_op, unop_id_op, Category.comp_id, Iso.refl_hom, unop_id,
          Category.id_comp]
        rw [eqToHom_naturality_assoc (fun q : ℤ => (Y.filtration.ι.app (op q)).unop)
          (show p = -(-p) by omega), hc]
        simp only [eqToHom_refl, Category.id_comp, Filtration.ι,
          dualBackFilteredObject, dualBackFiltration, dualBackEpi]
        rfl)

/-- The quotient and kernel constructions are inverse equivalences on finite filtered
objects. -/
noncomputable def dualFiniteEquivalence :
    (FiniteFilteredObject A)ᵒᵖ ≌ FiniteFilteredObject Aᵒᵖ := by
  let F := dualFiniteFunctor A
  let G : FiniteFilteredObject Aᵒᵖ ⥤ (FiniteFilteredObject A)ᵒᵖ := {
    obj Y := op ⟨dualBackFilteredObject A Y.obj,
      dualBackFilteredObject_finite A Y.obj Y.property⟩
    map f := (ObjectProperty.homMk (dualBackHom A f.hom)).op
    map_id Y := by
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      apply FilteredObject.hom_ext
      rfl
    map_comp f g := by
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      apply FilteredObject.hom_ext
      rfl }
  let η : 𝟭 (FiniteFilteredObject A)ᵒᵖ ≅ F ⋙ G := NatIso.ofComponents
    (fun X => (ObjectProperty.isoMk
      (fun Z : FilteredObject A ℤᵒᵖ => Z.filtration.IsFinite)
      (dualBack_dual_iso A X.unop.obj)).op) (by
      intro X Y f
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      apply FilteredObject.hom_ext
      change 𝟙 _ ≫ f.unop.hom.hom = f.unop.hom.hom.op.unop ≫ 𝟙 _
      simp)
  let ε : G ⋙ F ≅ 𝟭 (FiniteFilteredObject Aᵒᵖ) := NatIso.ofComponents
    (fun Y => ObjectProperty.isoMk
      (fun Z : FilteredObject Aᵒᵖ ℤᵒᵖ => Z.filtration.IsFinite)
      (dual_dualBack_iso A Y.obj)) (by
      intro X Y f
      apply ObjectProperty.hom_ext
      apply FilteredObject.hom_ext
      change f.hom.hom.unop.op ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.hom
      simp)
  exact CategoryTheory.Equivalence.mk F G η ε

/-- Finite filtered projectives become finite filtered injectives after passing to the
opposite category. -/
theorem dualFinite_filteredInjective (X : FiniteFilteredObject A)
    (hX : IsFilteredProjective X) :
    (dualFilteredObject A X.obj).IsFilteredInjective := by
  refine ⟨dualFilteredObject_finite A X.obj X.property, fun p => ?_⟩
  have : Projective ((FilteredObject.gr (-p - 1)).obj X.obj) := hX (-p - 1)
  exact Injective.of_iso (dualGrIso A X.obj p).symm inferInstance

end CategoryTheory.FilteredDerived

end
