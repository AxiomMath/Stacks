module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue

/-!
# The comparison of direct images along a composite is monoidal

Let `φ : (Sh(C), O_C) ⟶ (Sh(D), O_D)`, `ψ : (Sh(D), O_D) ⟶ (Sh(E), O_E)` and
`χ : (Sh(C), O_C) ⟶ (Sh(E), O_E)` be morphisms of ringed topoi, `χ` playing the role of the
composite through a comparison `τ : ψ_* ∘ φ_* ≅ χ_*` of the geometric direct images compatible
with the structure maps. The direct image of sheaves of modules along each of them is lax
monoidal (`Stacks.SheafOfModules.RingedToposPullback.pushforwardModulesLaxMonoidal`, the right
adjoint of the monoidal pullback of Tag 03EL), and `τ` induces the comparison
`Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso : φ_* ⋙ ψ_* ≅ χ_*` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso`. This file proves that
this comparison is a **monoidal** natural isomorphism, the composite carrying the composite lax
structure of `CategoryTheory.Functor.LaxMonoidal.comp`. This is what transports a sheaf of
(differential graded) algebras along a composite.

## The engine

The tensorator of a direct image is the mate of the comparison of Tag 03EL, which is defined by
a chain of six bijections and has no description on sections; but its effect on the canonical
bilinear pairing does. Writing `m ⊗ n` for the canonical pairing `M × N ⟶ M ⊗ N`, the
tensorator `μ : f_*M ⊗ f_*N ⟶ f_*(M ⊗ N)` satisfies `μ(m ⊗ n) = m ⊗ n`, read through the product
comparison of the geometric direct image (`prodComparison_comp_tensorPairing_comp_μ`). The proof
runs the chain of Tag 03EL backwards on `δ ≫ (ε ⊗ ε)`: steps 1 and 2 turn the tensorator into
its bilinear pairing, and steps 4 to 6 turn `ε ⊗ ε` into the counits of the adjunction of topoi
followed by the canonical pairing (`invChainPairing_counit_tensorHom_counit`), after which step 3
transposes back along the same adjunction and the unit cancels the counits. The unit of the lax
structure is, on underlying sheaves of sets, the structure map `f♯` (`moduleSheafFunctor_map_ε`).

With these two formulas the monoidality of the comparison is a short extensionality argument:
maps out of a tensor product are determined by their composite with the canonical pairing
(`hom_ext_tensorPairing`), and on the canonical pairing both sides become `τ` followed by the
direct image of the canonical pairing, `τ` being natural and so compatible with the product
comparisons.

## Main results

* `Stacks.Sheaves.RingedToposModules.prodComparison_comp_tensorPairing_comp_μ`: the tensorator
  of the direct image on the canonical pairing.
* `Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_ε`: the unit of the direct image is
  the structure map.
* `Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso_μ` and
  `Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso_ε`: the comparison of direct images
  along a composite is compatible with the tensorators and with the units.
* `Stacks.Sheaves.RingedToposModules.isMonoidal_pushforwardModulesCompIso_hom`: the comparison is
  a monoidal natural transformation.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry CategoryTheory.Sheaf
open scoped TensorProduct
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w w' w'' v u v' u' v'' u''

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf

namespace CategoryTheory.Adjunction

variable {C : Type*} [Category C] {D : Type*} [Category D] [HasBinaryProducts C]
  [HasBinaryProducts D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- The transpose of the product of two counits, read through the product comparison of the
left adjoint, is the inverse of the product comparison of the right adjoint. -/
theorem prodComparison_comp_unit_comp_map_prodMap_counit (a b : D) :
    prodComparison R a b ≫ adj.unit.app (R.obj a ⨯ R.obj b) ≫
        R.map (prodComparison L (R.obj a) (R.obj b) ≫
          prod.map (adj.counit.app a) (adj.counit.app b)) = 𝟙 _ := by
  have := adj.rightAdjoint_preservesLimits
  have hT : (adj.unit.app (R.obj a ⨯ R.obj b) ≫ R.map (prodComparison L (R.obj a) (R.obj b) ≫
      prod.map (adj.counit.app a) (adj.counit.app b))) ≫ prodComparison R a b = 𝟙 _ := by
    ext <;>
    · simp only [Category.assoc, prodComparison_fst, prodComparison_snd, ← Functor.map_comp,
        prod.map_fst, prod.map_snd, prodComparison_fst_assoc, prodComparison_snd_assoc,
        Category.id_comp, Functor.id_obj]
      rw [Functor.map_comp, ← Category.assoc, Adjunction.unit_naturality, Category.assoc,
        Adjunction.right_triangle_components, Category.comp_id]
  rw [← cancel_mono (prodComparison R a b), Category.assoc, hT]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

omit [HasBinaryProducts C] [HasBinaryProducts D] in
/-- For a composite adjunction `L₁ ⋙ L₂ ⊣ R₂ ⋙ R₁`, the unit of the second adjunction followed
by the second right adjoint of the composite counit is the counit of the first adjunction. -/
theorem unit_app_comp_map_comp_counit_app {E : Type*} [Category E] {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : D ⥤ E} {R₂ : E ⥤ D} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (M : E) :
    adj₂.unit.app (L₁.obj (R₁.obj (R₂.obj M))) ≫ R₂.map ((adj₁.comp adj₂).counit.app M) =
      adj₁.counit.app (R₂.obj M) := by
  simp [Adjunction.comp_counit_app]

end CategoryTheory.Adjunction

namespace Stacks.Sheaves.RingedToposModules

/-- Reassociation of a composite ending in the image of a triple composite, stated with every
object a variable. -/
theorem comp_comp_map_comp_comp {C : Type*} [Category C] {D : Type*} [Category D] (R : D ⥤ C)
    {P Q : C} {S T V W : D} (a : P ⟶ Q) (b : Q ⟶ R.obj S) (c : S ⟶ T) (d : T ⟶ V)
    (e : V ⟶ W) :
    a ≫ b ≫ R.map (c ≫ d ≫ e) = (a ≫ b ≫ R.map (c ≫ d)) ≫ R.map e := by
  simp

/-- The reduction of the tensorator half of the monoidality of a comparison of composite direct
images, stated with every object a variable: a composite through a tensorator of `Ψ` and
`Ψ` of a tensorator is `Ψ` of a canonical pairing. -/
theorem comp_comp_comp_map_comp_eq {C : Type*} [Category C] {D : Type*} [Category D] (Ψ : C ⥤ D)
    {P₀ P₁ S S' : C} {Q T W : D} (a₀ : P₀ ⟶ P₁) (b : Ψ.obj P₁ ⟶ Q) (c : Q ⟶ T)
    (d : T ⟶ Ψ.obj S) (g : P₁ ⟶ S) (e : S ⟶ S') (h : P₀ ⟶ S') (t : Ψ.obj S' ⟶ W)
    (hb : b ≫ c ≫ d = Ψ.map g) (he : a₀ ≫ g ≫ e = h) :
    (Ψ.map a₀ ≫ b) ≫ c ≫ d ≫ Ψ.map e ≫ t = Ψ.map h ≫ t := by
  rw [← he, Category.assoc, reassoc_of% hb]
  simp

/-- The reduction of the other side of the tensorator half, stated with every object a
variable. -/
theorem comp_comp_comp_eq_of_eq {C : Type*} [Category C] {P P' Q Q' T T₂ R : C}
    (x : P ⟶ Q) (tp : Q ⟶ T) (m : T ⟶ T₂) (pm : Q ⟶ Q') (c' : Q' ⟶ T₂) (a : P ⟶ P')
    (pcG : P' ⟶ Q') {d' : T₂ ⟶ R} {k : P' ⟶ R}
    (hn : tp ≫ m = pm ≫ c') (hpc : x ≫ pm = a ≫ pcG) (hμ : pcG ≫ c' ≫ d' = k) :
    x ≫ tp ≫ m ≫ d' = a ≫ k := by
  rw [reassoc_of% hn, reassoc_of% hpc, hμ]

end Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.RingedToposModules

section Pairing

variable {X : RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

open Stacks.SheafOfModules.RingedToposPullback in
/-- **The canonical bilinear pairing `M × N ⟶ M ⊗ N`** of two sheaves of modules on a ringed
topos into their tensor product of Tag 01CA, with its source and target spelled through the
structure sheaf of the ringed topos. On local sections it is the local pure tensor
(`tensorPairing_apply`). -/
def tensorPairing (M N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M ⨯
        Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N ⟶
      Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (M ⊗ N) :=
  canonicalPairing (A := X.O.obj) (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property M N

open Stacks.SheafOfModules.RingedToposPullback Stacks.SheafOfModules in
/-- **Morphisms out of a tensor product are determined by their bilinear composites**: two
morphisms out of `P ⊗ Q` agree as soon as they agree after the canonical pairing. This is the
injectivity of the universal property of the tensor product sheaf. -/
theorem hom_ext_tensorPairing
    {P Q N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {k k' : P ⊗ Q ⟶ N}
    (h : tensorPairing P Q ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map k =
      tensorPairing P Q ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map k') :
    k = k' := by
  have H (k : P ⊗ Q ⟶ N) := (congrArg (bilinearEquivTensorSheafHom (A := X.O.obj)
      (hA := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) (F := P) (G := Q) (N := N)).symm
      (Category.id_comp k).symm).trans
    (bilinearEquivTensorSheafHom_symm_naturality
      (hA := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) (𝟙 _) k)
  refine (bilinearEquivTensorSheafHom (A := X.O.obj)
    (hA := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)
    (F := P) (G := Q) (N := N)).symm.injective ((H k).trans (Eq.trans ?_ (H k').symm))
  exact Subtype.ext h

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Two morphisms out of a binary product of sheaves of sets agree as soon as they agree on all
pairs of local sections. -/
theorem prod_hom_ext_sections {P Q W : Sheaf X.J (Type w)} {m m' : P ⨯ Q ⟶ W}
    (h : ∀ (U : X.Cᵒᵖ) (a : (Sheaf.sectionsFunctor X.J U).obj P)
      (b : (Sheaf.sectionsFunctor X.J U).obj Q),
      (Sheaf.sectionsFunctor X.J U).map m (Functor.prodObjMk a b) =
        (Sheaf.sectionsFunctor X.J U).map m' (Functor.prodObjMk a b)) : m = m' := by
  refine Sheaf.hom_ext_sections fun U s ↦ ?_
  rw [← Functor.prodObjMk_map_fst_map_snd (P := Sheaf.sectionsFunctor X.J U) s]
  exact h U _ _

omit [X.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
open Stacks.SheafOfModules in
/-- The tensor product of two morphisms of sheaves of `O_C`-modules on the sheafification unit
of a local pure tensor. -/
theorem tensorHom_val_app_toSheafify
    {A A' B B' : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (a : A ⟶ A') (b : B ⟶ B')
    (U : X.Cᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) :
    (a ⊗ₘ b).val.app U
        ((TensorSheafification.toSheafify X.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property (A.val ⊗ B.val)).app U (x ⊗ₜ y)) =
      (TensorSheafification.toSheafify X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property (A'.val ⊗ B'.val)).app U
          (a.val.app U x ⊗ₜ b.val.app U y) :=
  (congrArg (fun m : A ⊗ B ⟶ A' ⊗ B' ↦ m.val.app U
        ((TensorSheafification.toSheafify X.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property (A.val ⊗ B.val)).app U (x ⊗ₜ y)))
      (tensorHom_def a b)).trans
    ((congrArg ((A' ◁ b).val.app U)
        (Stacks.SheafOfModules.RingedToposPullback.whiskerRight_val_app_toSheafify a U x y)).trans
      (Stacks.SheafOfModules.RingedToposPullback.whiskerLeft_val_app_toSheafify b U _ y))

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- A product of two morphisms of sheaves of sets followed by a third, on a pair of local
sections. -/
theorem sectionsFunctor_map_prodMap_comp_apply {P P' Q Q' W : Sheaf X.J (Type w)}
    (g : P ⟶ P') (h : Q ⟶ Q') (q : P' ⨯ Q' ⟶ W) (U : X.Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor X.J U).obj P) (b : (Sheaf.sectionsFunctor X.J U).obj Q) :
    (Sheaf.sectionsFunctor X.J U).map (prod.map g h ≫ q) (Functor.prodObjMk a b) =
      (Sheaf.sectionsFunctor X.J U).map q (Functor.prodObjMk
        ((Sheaf.sectionsFunctor X.J U).map g a) ((Sheaf.sectionsFunctor X.J U).map h b)) := by
  rw [Functor.map_comp_apply, Functor.map_prodMap_apply, Functor.map_fst_prodObjMk,
    Functor.map_snd_prodObjMk]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
open Stacks.SheafOfModules in
/-- The sheafification unit of a local pure tensor depends only on the two factors. -/
theorem toSheafify_tmul_congr
    {A B : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (U : X.Cᵒᵖ) {x x' : A.val.obj U} {y y' : B.val.obj U} (hx : x = x') (hy : y = y') :
    (TensorSheafification.toSheafify X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property (A.val ⊗ B.val)).app U (x ⊗ₜ y) =
      (TensorSheafification.toSheafify X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property (A.val ⊗ B.val)).app U
          (x' ⊗ₜ y') := by
  subst hx hy
  rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
open Stacks.SheafOfModules.RingedToposPullback Stacks.SheafOfModules in
/-- The canonical pairing of two sheaves of `O_C`-modules on a pair of local sections is the
sheafification unit of their local pure tensor. -/
theorem canonicalPairing_apply
    (M N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.Cᵒᵖ)
    (a : (Sheaf.sectionsFunctor X.J U).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))
    (b : (Sheaf.sectionsFunctor X.J U).obj
      (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) :
    (Sheaf.sectionsFunctor X.J U).map (canonicalPairing (A := X.O.obj)
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property M N) (Functor.prodObjMk a b) =
      (TensorSheafification.toSheafify X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property (M.val ⊗ N.val)).app U (a ⊗ₜ b) :=
  pairingApp_canonicalPairing (A := X.O.obj) (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
    M N U a b

/-- **Naturality of the canonical pairing**: the canonical pairing followed by a tensor product
of two morphisms is the product of the two morphisms followed by the canonical pairing. -/
theorem tensorPairing_comp_tensorHom
    {A A' B B' : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (a : A ⟶ A') (b : B ⟶ B') :
    tensorPairing A B ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map (a ⊗ₘ b) =
      prod.map ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map a)
          ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map b) ≫
        tensorPairing A' B' := by
  refine prod_hom_ext_sections fun U x y ↦ ?_
  have e1 := canonicalPairing_apply A B U x y
  have e2 := tensorHom_val_app_toSheafify a b U x y
  have e3 := canonicalPairing_apply A' B' U (a.val.app U x) (b.val.app U y)
  have e4 := sectionsFunctor_map_prodMap_comp_apply
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map a)
    ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map b)
    (tensorPairing A' B') U x y
  refine Eq.trans ?_ e4.symm
  refine Eq.trans ?_ e3.symm
  refine Eq.trans ?_ e2
  exact congrArg ((a ⊗ₘ b).val.app U) e1

end Pairing

section Tensorator

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The unit of the extension-restriction adjunction followed by the restriction of the counit of
Tag 03D7 is the counit of the adjunction of Tag 03D3. -/
theorem structureAdjunction_unit_comp_restrictScalars_map_counit
    (M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Stacks.SheafOfModules.RingedToposPullback.structureAdjunction f).unit.app
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
          ((pushforwardModules f).obj M)) ≫
      (_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).map
        ((pullbackAdjPushforwardModules f).counit.app M) =
    (inverseImageAdjDirectImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).counit.app
      ((_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).obj M) :=
  Adjunction.unit_app_comp_map_comp_counit_app
    (inverseImageAdjDirectImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (Stacks.SheafOfModules.RingedToposPullback.structureAdjunction f) M

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The counit of the adjunction of Tag 03D3 on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_inverseImageAdjDirectImageModules_counit
    (F : _root_.SheafOfModules.{w}
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (Sheaf.moduleSheafFunctor
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
        ((inverseImageAdjDirectImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).counit.app F) =
      f.toToposHom.adj.counit.app
        (Sheaf.moduleSheaf
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          F) := by
  change (Sheaf.moduleSheafFunctor _).map
      ((toposModulesHomEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) _ F).symm
        (𝟙 _)) = _
  rw [moduleSheafFunctor_map_toposModulesHomEquiv_symm]
  exact f.toToposHom.adj.homEquiv_symm_id _

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
open Stacks.SheafOfModules.RingedToposPullback Stacks.SheafOfModules in
/-- **Steps 4 to 6 of the chain of Tag 03EL, inverted, at the tensor product of the two counits
of Tag 03D7**: the pairing of `f⁻¹f_*M` and `f⁻¹f_*N` they produce is the product of the two
counits of the adjunction of topoi followed by the canonical pairing of `M` and `N`. -/
theorem invChainPairing_counit_tensorHom_counit
    (M N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (invChainPairing f ((pushforwardModules f).obj M) ((pushforwardModules f).obj N) (M ⊗ N)
        ((pullbackAdjPushforwardModules f).counit.app M ⊗ₘ
          (pullbackAdjPushforwardModules f).counit.app N)).1 =
      prod.map (f.toToposHom.adj.counit.app
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))
          (f.toToposHom.adj.counit.app
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) ≫
        canonicalPairing (A := X.O.obj) (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
          M N := by
  refine prod_hom_ext_sections fun U a b ↦ ?_
  have h1 := pairingApp_invChainPairing f ((pushforwardModules f).obj M)
    ((pushforwardModules f).obj N) (M ⊗ N)
    ((pullbackAdjPushforwardModules f).counit.app M ⊗ₘ
      (pullbackAdjPushforwardModules f).counit.app N) U a b
  unfold pairingApp at h1
  rw [h1]
  have hc : ∀ (P : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (c : (Sheaf.sectionsFunctor X.J U).obj (Sheaf.moduleSheaf
        (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
          ((pushforwardModules f).obj P)))),
      ((pullbackAdjPushforwardModules f).counit.app P).val.app U
          (((structureAdjunction f).unit.app
            ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
              ((pushforwardModules f).obj P))).val.app U c) =
        (Sheaf.sectionsFunctor X.J U).map
          (f.toToposHom.adj.counit.app
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P)) c :=
    fun P c ↦ (congrArg (fun φ ↦ φ.val.app U c)
      (structureAdjunction_unit_comp_restrictScalars_map_counit f P)).trans
      (congrArg (fun φ ↦ (Sheaf.sectionsFunctor X.J U).map φ c)
        (moduleSheafFunctor_map_inverseImageAdjDirectImageModules_counit f
          ((_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).obj P)))
  have e1 := tensorHom_val_app_toSheafify ((pullbackAdjPushforwardModules f).counit.app M)
    ((pullbackAdjPushforwardModules f).counit.app N) U
    (((structureAdjunction f).unit.app ((inverseImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj ((pushforwardModules f).obj M))).val.app
        U a)
    (((structureAdjunction f).unit.app ((inverseImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj ((pushforwardModules f).obj N))).val.app
        U b)
  have e2 := toSheafify_tmul_congr (A := M) (B := N) U (hc M a) (hc N b)
  refine (e1.trans e2).trans ?_
  have e4 := sectionsFunctor_map_prodMap_comp_apply
    (f.toToposHom.adj.counit.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))
    (f.toToposHom.adj.counit.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N))
    (canonicalPairing (A := X.O.obj) (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property M N)
    U a b
  exact (canonicalPairing_apply M N U _ _).symm.trans e4.symm

open Stacks.SheafOfModules.RingedToposPullback Stacks.SheafOfModules in
/-- **The tensorator of the direct image on canonical pairings.** The canonical pairing of `f_*M`
and `f_*N` into their tensor product, followed by the tensorator `μ : f_*M ⊗ f_*N ⟶ f_*(M ⊗ N)`,
is the direct image of the canonical pairing of `M` and `N`, read through the product
comparison of the direct image: informally `μ(m ⊗ n) = m ⊗ n`. -/
theorem prodComparison_comp_tensorPairing_comp_μ
    (M N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    prodComparison f.toToposHom.pushforward
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N) ≫
      tensorPairing ((pushforwardModules f).obj M) ((pushforwardModules f).obj N) ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          (Functor.LaxMonoidal.μ (pushforwardModules f) M N) =
      f.toToposHom.pushforward.map (tensorPairing M N) := by
  have h12 : (pullbackTensorStep2 f ((pushforwardModules f).obj M) ((pushforwardModules f).obj N)
        (M ⊗ N) (Functor.LaxMonoidal.μ (pushforwardModules f) M N)).1 =
      canonicalPairing (A := Y.O.obj) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property
          ((pushforwardModules f).obj M) ((pushforwardModules f).obj N) ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          (Functor.LaxMonoidal.μ (pushforwardModules f) M N) :=
    congrArg Subtype.val
      ((congrArg (fun z ↦ pullbackTensorStep2 f ((pushforwardModules f).obj M)
          ((pushforwardModules f).obj N) (M ⊗ N) z)
          (Category.id_comp (Functor.LaxMonoidal.μ (pushforwardModules f) M N)).symm).trans
        (bilinearEquivTensorSheafHom_symm_naturality
          (hA := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property)
          (𝟙 _) (Functor.LaxMonoidal.μ (pushforwardModules f) M N)))
  have h23 : pullbackTensorStep2 f ((pushforwardModules f).obj M) ((pushforwardModules f).obj N)
        (M ⊗ N) (Functor.LaxMonoidal.μ (pushforwardModules f) M N) =
      (pullbackTensorStep3 f ((pushforwardModules f).obj M) ((pushforwardModules f).obj N)
        (M ⊗ N)).symm (invChainPairing f ((pushforwardModules f).obj M)
          ((pushforwardModules f).obj N) (M ⊗ N)
          ((pullbackAdjPushforwardModules f).counit.app M ⊗ₘ
            (pullbackAdjPushforwardModules f).counit.app N)) := by
    refine (Equiv.eq_symm_apply _).mp ?_
    refine Eq.trans ?_ (step1_comparison_comp f ((pushforwardModules f).obj M)
      ((pushforwardModules f).obj N) (M ⊗ N) ((pullbackAdjPushforwardModules f).counit.app M ⊗ₘ
        (pullbackAdjPushforwardModules f).counit.app N))
    unfold pushforwardModulesLaxMonoidal pushforwardLaxMonoidal
    rw [Adjunction.rightAdjointLaxMonoidal_μ, delta_monoidal]
    rfl
  have h3 := inverseImageBilinearEquiv_apply_coe_eq_unit_comp f.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
    ((pushforwardModules f).obj M) ((pushforwardModules f).obj N)
    ((_root_.SheafOfModules.restrictScalars f.fSharpInverseImage).obj (M ⊗ N))
    (invChainPairing f ((pushforwardModules f).obj M)
          ((pushforwardModules f).obj N) (M ⊗ N)
          ((pullbackAdjPushforwardModules f).counit.app M ⊗ₘ
            (pullbackAdjPushforwardModules f).counit.app N))
  rw [invChainPairing_counit_tensorHom_counit] at h3
  have key := f.toToposHom.adj.prodComparison_comp_unit_comp_map_prodMap_counit
    (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)
    (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)
  refine (congrArg (_ ≫ ·) (h12.symm.trans ((congrArg Subtype.val h23).trans h3))).trans ?_
  refine Eq.trans ?_ ((congrArg (· ≫ f.toToposHom.pushforward.map
    (canonicalPairing (A := X.O.obj) (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
      M N)) key).trans
      (Category.id_comp _))
  exact comp_comp_map_comp_comp f.toToposHom.pushforward _ _ _ _ _

/-- **The unit of the lax monoidal structure of the direct image is the structure map.** On
underlying sheaves of sets, `ε : O_D ⟶ f_*O_C` is the direct-image form `f♯` of the structure
map: it is the transpose along Tag 03D7 of the comparison `ν : f^*O_D ≅ O_C`, whose transpose is
the inverse-image form of `f♯`, and the two forms of `f♯` are adjunct. -/
theorem moduleSheafFunctor_map_ε :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        (Functor.LaxMonoidal.ε (pushforwardModules f)) = fSharpSet f :=
  ((congrArg (fun e : _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≅
        f.pullbackModules.obj
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ↦
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        ((pullbackAdjPushforwardModules f).homEquiv _ _ e.inv))
      (pullbackModulesObjUnitIso_eq f)).trans
    (moduleSheafFunctor_map_pullbackAdjPushforwardModules_homEquiv f)).trans
    f.fSharp_adjunct.symm

end Tensorator

/-! ### The comparison of direct images along a composite is monoidal -/

section Composition

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
    {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  (φ : RingedToposHom X Y) (ψ : RingedToposHom Y Z) (χ : RingedToposHom X Z)
  (τ : φ.toToposHom.pushforward ⋙ ψ.toToposHom.pushforward ≅ χ.toToposHom.pushforward)
  (hτ : fSharpSetComp φ ψ ≫
      τ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) = fSharpSet χ)

/-- The product comparison of the composite direct image, written as the two product
comparisons in succession. -/
abbrev compProdComparison
    (M N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ψ.toToposHom.pushforward.obj (φ.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M ⨯
          Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) ⟶
      ψ.toToposHom.pushforward.obj
          (φ.toToposHom.pushforward.obj
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)) ⨯
        ψ.toToposHom.pushforward.obj
          (φ.toToposHom.pushforward.obj
            (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) :=
  ψ.toToposHom.pushforward.map
      (prodComparison φ.toToposHom.pushforward
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) ≫
    prodComparison ψ.toToposHom.pushforward
      (φ.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))
      (φ.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N))

/-- The composite tensorator followed by the comparison, on the canonical pairing read through
the product comparison of the composite direct image: it is `τ` followed by the direct image
along `χ` of the canonical pairing. -/
theorem compProdComparison_comp_tensorPairing_comp_μ_comp
    (M N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    compProdComparison φ ψ M N ≫
      tensorPairing ((pushforwardModules ψ).obj ((pushforwardModules φ).obj M))
          ((pushforwardModules ψ).obj ((pushforwardModules φ).obj N)) ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
          (Functor.LaxMonoidal.μ (pushforwardModules ψ) ((pushforwardModules φ).obj M)
              ((pushforwardModules φ).obj N) ≫
            (pushforwardModules ψ).map (Functor.LaxMonoidal.μ (pushforwardModules φ) M N) ≫
              (pushforwardModulesCompIso φ ψ χ τ hτ).hom.app (M ⊗ N)) =
      τ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M ⨯
          Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N) ≫
        χ.toToposHom.pushforward.map (tensorPairing M N) := by
  rw [Functor.map_comp, Functor.map_comp, moduleSheafFunctor_map_pushforwardModules_map,
    moduleSheafFunctor_map_pushforwardModulesCompIso_hom_app]
  exact (comp_comp_comp_map_comp_eq ψ.toToposHom.pushforward _ _ _ _ _ _ _ _
    (prodComparison_comp_tensorPairing_comp_μ ψ ((pushforwardModules φ).obj M)
      ((pushforwardModules φ).obj N))
    (prodComparison_comp_tensorPairing_comp_μ φ M N)).trans
    (τ.hom.naturality (tensorPairing M N))

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasWeakSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}] in
/-- The product comparison of the composite direct image is carried by `τ` to the product
comparison of the direct image along `χ`. -/
theorem compProdComparison_comp_prodMap
    (M N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    compProdComparison φ ψ M N ≫
      prod.map (τ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))
        (τ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N)) =
      τ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M ⨯
          Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N) ≫
        prodComparison χ.toToposHom.pushforward
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N) := by
  rw [compProdComparison, ← prodComparison_comp, prodComparison_natural_of_natTrans]

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The tensor product of the two components of the comparison followed by the tensorator of
`χ_*`, on the canonical pairing read through the product comparison of the composite direct
image: it is `τ` followed by the direct image along `χ` of the canonical pairing. -/
theorem compProdComparison_comp_tensorPairing_comp_tensorHom_comp_μ
    (M N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    compProdComparison φ ψ M N ≫
      tensorPairing ((pushforwardModules ψ).obj ((pushforwardModules φ).obj M))
          ((pushforwardModules ψ).obj ((pushforwardModules φ).obj N)) ≫
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map
          (((pushforwardModulesCompIso φ ψ χ τ hτ).hom.app M ⊗ₘ
              (pushforwardModulesCompIso φ ψ χ τ hτ).hom.app N) ≫
            Functor.LaxMonoidal.μ (pushforwardModules χ) M N) =
      τ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M ⨯
          Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N) ≫
        χ.toToposHom.pushforward.map (tensorPairing M N) := by
  have hn := tensorPairing_comp_tensorHom ((pushforwardModulesCompIso φ ψ χ τ hτ).hom.app M)
      ((pushforwardModulesCompIso φ ψ χ τ hτ).hom.app N)
  rw [moduleSheafFunctor_map_pushforwardModulesCompIso_hom_app,
    moduleSheafFunctor_map_pushforwardModulesCompIso_hom_app] at hn
  rw [Functor.map_comp]
  exact comp_comp_comp_eq_of_eq _ _ _ _ _ _ _ hn
    (compProdComparison_comp_prodMap φ ψ χ τ M N)
    (prodComparison_comp_tensorPairing_comp_μ χ M N)

/-- **The comparison `ψ_*φ_* ≅ χ_*` is compatible with the tensorators.** The tensorator of the
composite direct image, `μ_ψ` followed by `ψ_*` of `μ_φ`, is carried by the comparison to the
tensorator of `χ_*`. Both sides are morphisms out of a tensor product, so they are compared on
the canonical pairing, where the tensorators become direct images of canonical pairings and the
comparison becomes `τ`, natural in the module and so compatible with the product comparisons. -/
theorem pushforwardModulesCompIso_μ
    (M N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Functor.LaxMonoidal.μ (pushforwardModules ψ) ((pushforwardModules φ).obj M)
          ((pushforwardModules φ).obj N) ≫
        (pushforwardModules ψ).map (Functor.LaxMonoidal.μ (pushforwardModules φ) M N) ≫
          (pushforwardModulesCompIso φ ψ χ τ hτ).hom.app (M ⊗ N) =
      ((pushforwardModulesCompIso φ ψ χ τ hτ).hom.app M ⊗ₘ
          (pushforwardModulesCompIso φ ψ χ τ hτ).hom.app N) ≫
        Functor.LaxMonoidal.μ (pushforwardModules χ) M N := by
  have := φ.toToposHom.adj.rightAdjoint_preservesLimits
  have := ψ.toToposHom.adj.rightAdjoint_preservesLimits
  refine hom_ext_tensorPairing ((cancel_epi (compProdComparison φ ψ M N)).1 ?_)
  exact (compProdComparison_comp_tensorPairing_comp_μ_comp φ ψ χ τ hτ M N).trans
    (compProdComparison_comp_tensorPairing_comp_tensorHom_comp_μ φ ψ χ τ hτ M N).symm

/-- **The comparison `ψ_*φ_* ≅ χ_*` is compatible with the units.** On underlying sheaves of sets
the unit of each direct image is its structure map, and the comparison is `τ`, so this is the
hypothesis that `τ` carries the composite structure map to the structure map of `χ`. -/
theorem pushforwardModulesCompIso_ε :
    Functor.LaxMonoidal.ε (pushforwardModules ψ) ≫
        (pushforwardModules ψ).map (Functor.LaxMonoidal.ε (pushforwardModules φ)) ≫
          (pushforwardModulesCompIso φ ψ χ τ hτ).hom.app
            (𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) =
      Functor.LaxMonoidal.ε (pushforwardModules χ) := by
  refine hom_ext_moduleSheafFunctor ?_
  rw [Functor.map_comp, Functor.map_comp, moduleSheafFunctor_map_ε,
    moduleSheafFunctor_map_pushforwardModules_map, moduleSheafFunctor_map_ε,
    moduleSheafFunctor_map_pushforwardModulesCompIso_hom_app, moduleSheafFunctor_map_ε]
  exact (Category.assoc _ _ _).symm.trans hτ

/-- **The comparison `ψ_*φ_* ≅ χ_*` of direct images of sheaves of modules is a monoidal natural
transformation**, for the composite lax monoidal structure on `φ_* ⋙ ψ_*` and the lax monoidal
structure on `χ_*`, each of them the right adjoint of the monoidal pullback of Tag 03EL. -/
instance isMonoidal_pushforwardModulesCompIso_hom :
    NatTrans.IsMonoidal (pushforwardModulesCompIso φ ψ χ τ hτ).hom where
  unit := (Category.assoc _ _ _).trans (pushforwardModulesCompIso_ε φ ψ χ τ hτ)
  tensor M N := (Category.assoc _ _ _).trans (pushforwardModulesCompIso_μ φ ψ χ τ hτ M N)

end Composition

end Stacks.Sheaves.RingedToposModules
