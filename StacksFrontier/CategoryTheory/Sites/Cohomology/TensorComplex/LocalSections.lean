module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingOnASlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationMorphism
import StacksCore.Tactic.StacksAttribute

/-! # Local sections of the total tensor complex, and the Leibniz rule

Let `(C, O)` be a ringed site and let `K` and `L` be complexes of `O`-modules. The degree-`c`
term of the total tensor complex `Tot(K ⊗_O L)` of Stacks 06YM is the coproduct over the pairs
`t + r = c` of the sheaf tensor products `K^t ⊗_O L^r`, each of which is the sheafification of
the objectwise tensor product. This file records the resulting *local pure tensors*: the local
section `k ⊗ l` of `Tot(K ⊗_O L)^c` over an object `W` determined by a section `k` of `K^t` and
a section `l` of `L^r` over `W`, its bilinearity, its compatibility with restriction, and the
Koszul Leibniz rule

`d(k ⊗ l) = (dk) ⊗ l + (-1)^t k ⊗ (dl)`.

The restricted pure tensors `AlgebraicGeometry.RingedSite.tensorComplexOverSection` of
`StacksDraft.Ch21.Sec34.TensorComplexOnASlice`, which by
`AlgebraicGeometry.RingedSite.tensorComplexOverSection_hom_ext` generate the restriction of the
total tensor complex to a slice site, are these same sections read on the slice; the
identification is definitional and is recorded as
`AlgebraicGeometry.RingedSite.tensorComplexOverSection_eq`.

Together with the Leibniz rule
`AlgebraicGeometry.RingedSite.applyHomSectionOver_differential` of the internal Hom complex,
the Leibniz rule proved here is the last ingredient of the currying isomorphism of Stacks 0A90.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorComplexTmulMap`: the morphism of presheaves of `O`-modules
  from the objectwise tensor product `K^t ⊗ L^r` to the degree-`c` term of `Tot(K ⊗_O L)`.
* `AlgebraicGeometry.RingedSite.tensorComplexSection`: the local pure tensor `k ⊗ l`.

## Main results

* `AlgebraicGeometry.RingedSite.tensorComplexSection_add_left`, `_add_right`, `_smul_left`,
  `_smul_right`, `_restrict`: bilinearity and compatibility with restriction.
* `AlgebraicGeometry.RingedSite.ι_tensorComplex_d`: the differential of the total tensor complex
  restricted to the `(t, r)` summand, as a morphism of sheaves of `O`-modules.
* `AlgebraicGeometry.RingedSite.tensorComplexOverSection_d`: the Leibniz rule on the restricted
  pure tensors.

## Implementation notes

The two halves of the Leibniz rule live at different spellings. The categorical half is the
bicomplex computation of `CategoryTheory.HomologicalComplex.mapBifunctor.d_eq` together with
`ι_D₁`/`ι_D₂` and `d₁_eq`/`d₂_eq`, whose Koszul signs are `ε₁ = 1` and `ε₂ = (-1)^t`; it is
stated at the `HomologicalComplex.mapBifunctor` spelling of the total complex, since that is the
spelling in which those lemmas are indexed — the `Stacks.SheafOfModules.Tensor.tensorComplex`
  spelling is
`rfl`-equal but is not seen through by the rewriting. The elementwise half evaluates it on a
local pure tensor and then transports to the slice, which is a definitional step: restriction to
the site over `U` is precomposition with `(Over.forget U).op`, so a morphism obtained by
restriction acts on a section over `Over.mk g` by the action of the original morphism on the
section over the source of `g`. That transport is left to a single `exact` rather than to a
rewrite, because the restricted module of sections is a restriction of scalars of the original
one and a rewrite across it leaves the goal ill-typed at the `implicit` transparency level.

For the same reason the local pure tensors are introduced on the ambient site rather than on the
slice: every bilinearity statement then has the scalars and the modules at one spelling, which
is what makes `map_add`/`map_smul` applicable. The bilinearity of the objectwise tensor product
is likewise stated over an abstract commutative ring, since
`TensorProduct.add_tmul`/`tmul_smul` do not fire at the ring spelling `O(W)` carries here.

The passage from the sheafified tensor product to the presheaf-level one is unit naturality,
`AlgebraicGeometry.RingedSite.sheafification_map_unit_apply`, applied to the whiskerings
`dK ▷ L^r` and `K^t ◁ dL` of the monoidal structure on presheaves of modules — the two
morphisms whose sheafifications are the actions of `⊗_O` on the differentials.

## References

* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  ringSheafOverSectionsCommRing

variable (X : RingedSite.{u, u, u})

/-- A sum of morphisms of sheaves of `O`-modules acts on sections by addition. -/
private lemma add_val_app_apply₀
    {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f g : A ⟶ B)
    (W : X.Cᵒᵖ) (x : A.val.obj W) :
    (f + g).val.app W x = f.val.app W x + g.val.app W x := by
  with_unfolding_all rfl

/-- An integer multiple of a morphism of sheaves of `O`-modules acts on sections by scaling. -/
private lemma zsmul_val_app_apply₀
    {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : A ⟶ B)
    (n : ℤ) (W : X.Cᵒᵖ) (x : A.val.obj W) :
    ModuleCat.Hom.hom ((n • f).val.app W) x = n • ModuleCat.Hom.hom (f.val.app W) x := by
  have hv : (n • f).val = n • f.val := by with_unfolding_all rfl
  rw [hv, PresheafOfModules.zsmul_app, ModuleCat.hom_zsmul, LinearMap.smul_apply]

/-- A unit multiple of a morphism of sheaves of `O`-modules acts on sections by scaling. -/
private lemma units_zsmul_val_app_apply₀
    {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (f : A ⟶ B)
    (n : ℤˣ) (W : X.Cᵒᵖ) (x : A.val.obj W) :
    (n • f).val.app W x = n • (f.val.app W) x :=
  zsmul_val_app_apply₀ X f (n : ℤ) W x

/-- Applying a composite of morphisms of sheaves of `O`-modules to a local section. -/
lemma val_app_comp_apply
    {P Q R : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : P ⟶ Q)
    (ψ : Q ⟶ R) (W : X.Cᵒᵖ) (x : P.val.obj W) :
    ((φ ≫ ψ).val.app W) x = (ψ.val.app W) ((φ.val.app W) x) := rfl

/-- The identity morphism of complexes of `O`-modules acts on local sections as the identity. -/
lemma id_f_val_app_apply
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (d : ℤ)
    (W : X.C) (x : (A.X d).val.obj (op W)) :
    (HomologicalComplex.Hom.f (𝟙 A) d).val.app (op W) x = x := rfl

/-- An isomorphism of sheaves of `O`-modules is bijective on the sections over every object. -/
lemma bijective_val_app_of_iso
    {P Q : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : P ≅ Q)
    (W : X.Cᵒᵖ) : Function.Bijective (φ.hom.val.app W) := by
  have hiso : IsIso (φ.hom.val.app W) :=
    ((PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj W).mapIso
      ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapIso φ)).isIso_hom
  exact (ConcreteCategory.isIso_iff_bijective _).1 hiso

variable [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-! ## Local pure tensors -/

/-- The morphism of presheaves of `O`-modules sending a pure tensor of local sections of `K^t`
and `L^r` to the corresponding local section of the degree-`c` term of the total tensor complex:
the sheafification unit followed by the inclusion of the `(t, r)` summand. -/
def tensorComplexTmulMap (t r c : ℤ) (htr : t + r = c) :
    (K.X t).val ⊗ (L.X r).val ⟶
      ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L).X c).val :=
  (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
      ((K.X t).val ⊗ (L.X r).val) ≫
    (HomologicalComplex.ιMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ) t r c (by simpa using htr)).val

variable {K L}

/-- The local pure tensor of a section of `K^t` and a section of `L^r` over an object `W`, as a
section over `W` of the degree-`c` term of the total tensor complex. -/
def tensorComplexSection (t r c : ℤ) (htr : t + r = c) {W : X.C}
    (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L).X c).val.obj (op W) :=
  (tensorComplexTmulMap X K L t r c htr).app (op W)
    (k ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] l)

/-- The restricted pure tensor of `StacksDraft.Ch21.Sec34.TensorComplexOnASlice` is the local
pure tensor of the ambient site: restriction to the site over `U` only reindexes the sections. -/
lemma tensorComplexOverSection_eq (U : X.C) (t r c : ℤ) (htr : t + r = c) {W : X.C} (g : W ⟶ U)
    (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    tensorComplexOverSection t r c htr g k l = tensorComplexSection X t r c htr k l := rfl

/-- The local pure tensor is additive in the section of `K`. -/
lemma tensorComplexSection_add_left (t r c : ℤ) (htr : t + r = c) {W : X.C}
    (k k' : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    tensorComplexSection X t r c htr (k + k') l =
      tensorComplexSection X t r c htr k l + tensorComplexSection X t r c htr k' l := by
  have h :=
    TensorProduct.add_tmul (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)) k k' l
  exact (congrArg _ h).trans (map_add _ _ _)

/-- The local pure tensor is additive in the section of `L`. -/
lemma tensorComplexSection_add_right (t r c : ℤ) (htr : t + r = c) {W : X.C}
    (k : (K.X t).val.obj (op W)) (l l' : (L.X r).val.obj (op W)) :
    tensorComplexSection X t r c htr k (l + l') =
      tensorComplexSection X t r c htr k l + tensorComplexSection X t r c htr k l' := by
  have h :=
    TensorProduct.tmul_add (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)) k l l'
  exact (congrArg _ h).trans (map_add _ _ _)

/-- The local pure tensor is linear in the section of `K`. -/
lemma tensorComplexSection_smul_left (t r c : ℤ) (htr : t + r = c) {W : X.C}
    (s : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)) (k : (K.X t).val.obj (op W))
    (l : (L.X r).val.obj (op W)) :
    tensorComplexSection X t r c htr (s • k) l = s • tensorComplexSection X t r c htr k l := by
  have h :=
    TensorProduct.smul_tmul'
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)) s k l
  exact (congrArg _ h.symm).trans (map_smul _ _ _)

/-- The local pure tensor is linear in the section of `L`. -/
lemma tensorComplexSection_smul_right (t r c : ℤ) (htr : t + r = c) {W : X.C}
    (s : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)) (k : (K.X t).val.obj (op W))
    (l : (L.X r).val.obj (op W)) :
    tensorComplexSection X t r c htr k (s • l) = s • tensorComplexSection X t r c htr k l := by
  have h :=
    TensorProduct.tmul_smul (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)) s k l
  exact (congrArg _ h).trans (map_smul _ _ _)

/-- The local pure tensor is compatible with restriction along an arrow of the site. -/
lemma tensorComplexSection_restrict (t r c : ℤ) (htr : t + r = c) {W V : X.C} (h : V ⟶ W)
    (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    tensorComplexSection X (K := K) (L := L) (W := V) t r c htr ((K.X t).val.map h.op k)
        ((L.X r).val.map h.op l) =
      ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L).X c).val.map h.op
        (tensorComplexSection X t r c htr k l) :=
  (congrArg (fun y ↦ (tensorComplexTmulMap X K L t r c htr).app (op V) y)
      (PresheafOfModules.Monoidal.tensorObj_map_tmul h.op k l).symm).trans
    (PresheafOfModules.naturality_apply (tensorComplexTmulMap X K L t r c htr) h.op
      (k ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] l))

/-! ## The Leibniz rule -/

variable (K L)

/-- **The differential of the total tensor complex on a summand.** On the `(t, r)` summand of
the degree-`c` term of `Tot(K ⊗_O L)` the differential is `dK ⊗ 1` into the `(t + 1, r)` summand
plus `(-1)^t` times `1 ⊗ dL` into the `(t, r + 1)` summand. The two Koszul signs are the
`ε₁ = 1` and `ε₂ = (-1)^t` of the total complex of a bicomplex. -/
lemma ι_tensorComplex_d (t r c : ℤ) (htr : t + r = c) :
    HomologicalComplex.ιMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)
        t r c (by simpa using htr) ≫
      (HomologicalComplex.mapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ)).d c (c + 1) =
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (K.d t (t + 1))).app (L.X r) ≫
        HomologicalComplex.ιMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) (t + 1) r (c + 1) (by simp; omega) +
      t.negOnePow • (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (K.X t)).map (L.d r (r +
        1)) ≫
        HomologicalComplex.ιMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) t (r + 1) (c + 1) (by simp; omega)) := by
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (ComplexShape.up_mk t (t + 1) rfl) r (c + 1)
      (show ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (t + 1, r) = c + 1 by simp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ t (ComplexShape.up_mk r (r + 1) rfl) (c + 1)
      (show ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (t, r + 1) = c + 1 by simp; omega)]
  have hε₁ : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (t, r) = 1 := rfl
  have hε₂ : ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (t, r) = t.negOnePow := rfl
  rw [hε₁, hε₂, one_smul]

/-- The right-hand side of `AlgebraicGeometry.RingedSite.ι_tensorComplex_d`, evaluated on the
image of a pure tensor of local sections under the sheafification unit. -/
private lemma ι_tensorComplex_d_rhs_apply (t r c : ℤ) {W : X.C}
    (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W))
    (h₁ : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (t + 1, r) = c + 1)
    (h₂ : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (t, r + 1) = c + 1) :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (K.d t (t + 1))).app (L.X r) ≫
          HomologicalComplex.ιMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
            (ComplexShape.up ℤ) (t + 1) r (c + 1) h₁ +
        t.negOnePow • (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (K.X t)).map (L.d r (r +
          1)) ≫
          HomologicalComplex.ιMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
            (ComplexShape.up ℤ) t (r + 1) (c + 1) h₂)).val.app (op W))
        (((PresheafOfModules.sheafificationAdjunction
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          ((K.X t).val ⊗ (L.X r).val)).app (op W)
            (k ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] l)) =
      (HomologicalComplex.ιMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) (t + 1) r (c + 1) h₁).val.app (op W)
          (((PresheafOfModules.sheafificationAdjunction
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
            ((K.X (t + 1)).val ⊗ (L.X r).val)).app (op W)
              ((K.d t (t + 1)).val.app (op W)
                k ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] l)) +
        t.negOnePow • (HomologicalComplex.ιMapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ) t (r + 1) (c + 1) h₂).val.app (op W)
          (((PresheafOfModules.sheafificationAdjunction
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
            ((K.X t).val ⊗ (L.X (r + 1)).val)).app (op W)
              (k ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)]
                (L.d r (r + 1)).val.app (op W) l)) := by
  have hA := sheafification_map_unit_apply X ((K.d t (t + 1)).val ▷ (L.X r).val) (op W)
    (k ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] l)
  have hB := sheafification_map_unit_apply X ((K.X t).val ◁ (L.d r (r + 1)).val) (op W)
    (k ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] l)
  refine (add_val_app_apply₀ X _ _ (op W) _).trans ?_
  refine congrArg₂ (· + ·) ?_ ?_
  · exact congrArg (fun y ↦ (HomologicalComplex.ιMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) (t + 1) r (c + 1)
        h₁).val.app
        (op W) y) hA
  · refine (units_zsmul_val_app_apply₀ X _ t.negOnePow (op W) _).trans ?_
    exact congrArg (fun y ↦ t.negOnePow • (HomologicalComplex.ιMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) t (r + 1) (c + 1)
        h₂).val.app
        (op W) y) hB

variable {K L}

/-- **The Koszul Leibniz rule for the restricted total tensor complex.** The differential of
`Tot(K ⊗_O L)|_U` takes the restricted pure tensor of a section `k` of `K^t` and a section `l`
of `L^r` to `(dk) ⊗ l + (-1)^t k ⊗ (dl)`. Together with
`AlgebraicGeometry.RingedSite.tensorComplexOverSection_hom_ext` this determines the
differential. -/
lemma tensorComplexOverSection_d (U : X.C) (t r c c' : ℤ) (htr : t + r = c) (hc : c + 1 = c')
    {W : X.C} (g : W ⟶ U) (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    ((restrictComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj L) U).d c
      c').val.app
        (op (Over.mk g)) (tensorComplexOverSection t r c htr g k l) =
      tensorComplexOverSection (t + 1) r c' (by omega) g
          ((K.d t (t + 1)).val.app (op W) k) l +
        t.negOnePow • tensorComplexOverSection t (r + 1) c' (by omega) g k
          ((L.d r (r + 1)).val.app (op W) l) := by
  subst hc
  exact (congrArg (fun φ : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (K.X t)).obj (L.X r)
    ⟶
      (HomologicalComplex.mapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ)).X (c + 1) ↦ φ.val.app (op W)
        (((PresheafOfModules.sheafificationAdjunction
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          ((K.X t).val ⊗ (L.X r).val)).app (op W)
            (k ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] l)))
    (ι_tensorComplex_d X K L t r c htr)).trans
      (ι_tensorComplex_d_rhs_apply X K L t r c k l _ _)

end AlgebraicGeometry.RingedSite

end
