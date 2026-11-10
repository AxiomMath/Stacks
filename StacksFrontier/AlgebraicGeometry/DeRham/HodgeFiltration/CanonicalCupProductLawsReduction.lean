module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.CanonicalCupProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorPureTensors
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSquareZeroThickening
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAlgebraFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.ComplexesOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.AssociatorOnLocalSections

/-!
# The complex-level laws of a multiplication from its laws on local pure tensors

Let `A` be a sheaf of commutative rings on a ringed space `X` and let `m : Tot(K ⊗_A L) ⟶ M` be a
multiplication of `ℕ`-indexed complexes of sheaves of `A`-modules, with extended multiplication
`AlgebraicGeometry.SheafOfModules.multiplicationInt m` on the extensions by zero `K'`, `L'`, `M'`.
This file shows that the associativity and the graded commutativity of extended multiplications
in the symmetric monoidal category of complexes of [Stacks, Tag 0FPQ] follow from the
corresponding identities of the multiplications on homogeneous local pure tensors.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.multiplicationValue`: the value of a multiplication on the
  local pure tensor `x ⊗ y` of a section of `K^a` and a section of `L^b`, a section of `M^{a+b}`.
* `AlgebraicGeometry.SheafOfModules.extendSection`: the section of `K^a` corresponding to a
  section of the extension by zero `K'^a`.

## Main results

* `AlgebraicGeometry.SheafOfModules.multiplicationInt_assoc`: if the two bracketings of four
  multiplications agree on iterated local pure tensors, then
  `(m₁ ⊗ 𝟙) ≫ m₂ = α ≫ (𝟙 ⊗ m₃) ≫ m₄` for the extended multiplications.
* `AlgebraicGeometry.SheafOfModules.multiplicationInt_braiding`: if
  `m(x ⊗ y) = (-1)^{ab} m'(y ⊗ x)` on local pure tensors, then `β ≫ m' = m` for the extended
  multiplications and the Koszul symmetry of complexes.

## References

* [Stacks Project, Tag 0FP4](https://stacks.math.columbia.edu/tag/0FP4)
* [Stacks Project, Tag 0FP5](https://stacks.math.columbia.edu/tag/0FP5)
* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape Opposite
open TopologicalSpace
open Stacks.SheafOfModules.Tensor (sheafTensor)
open scoped TensorProduct Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier}

variable {K L N P Q M : CochainComplex
  (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ}

/-- The class `x ⊗ y` in `F ⊗_A G` of a local pure tensor. -/
private abbrev tmulClass (F G : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) {U : (Opens X.carrier)ᵒᵖ}
    (x : F.val.obj U) (y : G.val.obj U) :
    (((sheafTensor.{u, u, u, u, u} A).obj F).obj G).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
    (PresheafOfModules.tensorObj F.val G.val)).app U (x ⊗ₜ[A.obj.obj U] y)

/-- **The value of a multiplication `Tot(K ⊗_A L) ⟶ M` on a local pure tensor**: on the local
pure tensor `x ⊗ y` of a section `x` of `K^a` and a section `y` of `L^b`, the restriction of the
multiplication to the `(a, b)` summand, a section of `M^{a + b}`. -/
def multiplicationValue (m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M) (a b : ℕ)
    (U : (Opens X.carrier)ᵒᵖ) (x : (K.X a).val.obj U) (y : (L.X b).val.obj U) :
    (M.X (a + b)).val.obj U :=
  (HomologicalComplex.ιMapBifunctor K L (sheafTensor.{u, u, u, u, u} A) (up ℕ) a b (a + b) rfl ≫
      m.f (a + b)).val.app U
    (((PresheafOfModules.sheafificationAdjunction (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
      (PresheafOfModules.tensorObj (K.X a).val (L.X b).val)).app U (x ⊗ₜ[A.obj.obj U] y))

/-- The section of the extension by zero `K'^a` corresponding to a section of `K^a`. -/
abbrev extendSection (K : CochainComplex
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ) (a : ℕ)
    {U : (Opens X.carrier)ᵒᵖ} (x : ((K.extend embeddingUpNat).X (a : ℤ)).val.obj U) :
    (K.X a).val.obj U :=
  (K.extendXIso embeddingUpNat (i := a) (i' := (a : ℤ)) rfl).hom.val.app U x

/-- Tensoring a morphism on the left, on the class of a local pure tensor. -/
private theorem tensorMap_app_tmulClass {F F' : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)} (f : F ⟶ F')
    (G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
    {U : (Opens X.carrier)ᵒᵖ} (x : F.val.obj U) (y : G.val.obj U) :
    (((sheafTensor.{u, u, u, u, u} A).map f).app G).val.app U (tmulClass F G x y) =
      tmulClass F' G (f.val.app U x) y :=
  PresheafOfModules.hom_congr_apply'
    (PresheafOfModules.unit_comp_map (α := 𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)
      (PresheafOfModules.tensorHom (O := A.obj) f.val (𝟙 G.val))) U (x ⊗ₜ[A.obj.obj U] y)

/-- Tensoring a morphism on the right, on the class of a local pure tensor. -/
private theorem tensorObjMap_tmulClass (F : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
    {G G' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (g : G ⟶ G') {U : (Opens X.carrier)ᵒᵖ} (x : F.val.obj U) (y : G.val.obj U) :
    (((sheafTensor.{u, u, u, u, u} A).obj F).map g).val.app U (tmulClass F G x y) =
      tmulClass F G' x (g.val.app U y) :=
  PresheafOfModules.hom_congr_apply'
    (PresheafOfModules.unit_comp_map (α := 𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)
      (PresheafOfModules.tensorHom (O := A.obj) (𝟙 F.val) g.val)) U (x ⊗ₜ[A.obj.obj U] y)

/-- **The extended multiplication on the class of a local pure tensor** of the `(a, b)` summand
of `Tot(K' ⊗ L')`: it is the value of the multiplication, read in `M'^n`. -/
private theorem multiplicationInt_ι_tmul (m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M)
    (a b n : ℕ) (hn : a + b = n) (h : (a : ℤ) + (b : ℤ) = (n : ℤ))
    (U : (Opens X.carrier)ᵒᵖ) (x : ((K.extend embeddingUpNat).X (a : ℤ)).val.obj U)
    (y : ((L.extend embeddingUpNat).X (b : ℤ)).val.obj U) :
    (HomologicalComplex.ιMapBifunctor (K.extend embeddingUpNat) (L.extend embeddingUpNat)
        (sheafTensor.{u, u, u, u, u} A) (up ℤ) (a : ℤ) (b : ℤ) (n : ℤ) h ≫
        (multiplicationInt m).f (n : ℤ)).val.app U (tmulClass _ _ x y) =
      (M.extendXIso embeddingUpNat (i := n) (i' := (n : ℤ)) rfl).inv.val.app U
        ((M.XIsoOfEq hn).hom.val.app U
          (multiplicationValue m a b U (extendSection K a x) (extendSection L b y))) := by
  subst hn
  let m' : HomologicalComplex.mapBifunctor K L (sheafTensor.{u, u, u, u, u} A) (up ℕ) ⟶ M := m
  have key : HomologicalComplex.ιMapBifunctor (K.extend embeddingUpNat)
      (L.extend embeddingUpNat) (sheafTensor.{u, u, u, u, u} A) (up ℤ) (a : ℤ) (b : ℤ)
      ((a + b : ℕ) : ℤ) h ≫ (HomologicalComplex.mapBifunctorExtendHom
        (sheafTensor.{u, u, u, u, u} A) K L ≫ HomologicalComplex.extendMap m' embeddingUpNat).f
          ((a + b : ℕ) : ℤ) =
      ((sheafTensor.{u, u, u, u, u} A).map
          (K.extendXIso embeddingUpNat (i' := (a : ℤ)) (i := a) rfl).hom).app _ ≫
        ((sheafTensor.{u, u, u, u, u} A).obj (K.X a)).map
          (L.extendXIso embeddingUpNat (i' := (b : ℤ)) (i := b) rfl).hom ≫
        HomologicalComplex.ιMapBifunctor K L (sheafTensor.{u, u, u, u, u} A) (up ℕ) a b (a + b)
          rfl ≫ m'.f (a + b) ≫
        (M.extendXIso embeddingUpNat (i := a + b) (i' := ((a + b : ℕ) : ℤ)) rfl).inv := by
    rw [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorExtendHom_f_assoc,
      HomologicalComplex.extendMap_f m' embeddingUpNat (i := a + b) (i' := ((a + b : ℕ) : ℤ)) rfl]
    simp only [Iso.inv_hom_id_assoc]
  change (HomologicalComplex.ιMapBifunctor (K.extend embeddingUpNat)
      (L.extend embeddingUpNat) (sheafTensor.{u, u, u, u, u} A) (up ℤ) (a : ℤ) (b : ℤ)
      ((a + b : ℕ) : ℤ) h ≫ (HomologicalComplex.mapBifunctorExtendHom
        (sheafTensor.{u, u, u, u, u} A) K L ≫ HomologicalComplex.extendMap m' embeddingUpNat).f
          ((a + b : ℕ) : ℤ)).val.app U (tmulClass _ _ x y) = _
  rw [key]
  simp only [Stacks.SheafOfModules.comp_val_app_apply]
  rw [tensorMap_app_tmulClass, tensorObjMap_tmulClass, HomologicalComplex.XIsoOfEq_rfl]
  rfl

/-- Transport along an equality of degrees is determined by heterogeneous equality. -/
private theorem XIsoOfEq_val_app_of_heq {i j k : ℕ} (hi : i = k) (hj : j = k)
    {U : (Opens X.carrier)ᵒᵖ} {x : (M.X i).val.obj U} {y : (M.X j).val.obj U} (h : HEq x y) :
    (M.XIsoOfEq hi).hom.val.app U x = (M.XIsoOfEq hj).hom.val.app U y := by
  subst hi; subst hj; cases h; rfl

/-- A tensor product with a zero left factor is zero. -/
private theorem isZero_tensor_left {Z : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (W : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
    (hZ : IsZero Z) : IsZero (((sheafTensor.{u, u, u, u, u} A).obj Z).obj W) :=
  ((sheafTensor.{u, u, u, u, u} A).map_isZero hZ).obj W

/-- A tensor product with a zero right factor is zero. -/
private theorem isZero_tensor_right
    (Z : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
    {W : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (hW : IsZero W) : IsZero (((sheafTensor.{u, u, u, u, u} A).obj Z).obj W) :=
  ((sheafTensor.{u, u, u, u, u} A).obj Z).map_isZero hW

/-- The extension by zero of a complex is zero in negative degrees. -/
private theorem isZero_extend_X_of_neg {i : ℤ} (hi : i < 0) :
    IsZero ((K.extend embeddingUpNat).X i) :=
  HomologicalComplex.isZero_extend_X K embeddingUpNat i fun j hj => by
    change (j : ℤ) = i at hj; omega

section Monoidal

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor
  _root_.SheafOfModules.symmetricCategorySheafTensor
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory

/-- The ringed site of the opens of `X` with the sheaf of rings `A`. -/
private abbrev siteOf (A : TopCat.Sheaf CommRingCat.{u} X.carrier) : RingedSite.{u, u, u} :=
  ⟨Opens X.carrier, Opens.grothendieckTopology X.carrier, A⟩

/-- The associator of sheaves of modules, typed at the spelling of `sheafTensor`. -/
private abbrev modAssoc (F G H : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) :
    ((sheafTensor.{u, u, u, u, u} A).obj (((sheafTensor.{u, u, u, u, u} A).obj F).obj G)).obj H ⟶
      ((sheafTensor.{u, u, u, u, u} A).obj F).obj (((sheafTensor.{u, u, u, u, u} A).obj G).obj H) :=
  (α_ F G H).hom

/-- The associator of complexes, typed at the spelling of total complexes of `sheafTensor`. -/
private abbrev cxAssoc (K L N : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ) :
    HomologicalComplex.mapBifunctor (HomologicalComplex.mapBifunctor K L
        (sheafTensor.{u, u, u, u, u} A) (up ℤ)) N (sheafTensor.{u, u, u, u, u} A) (up ℤ) ⟶
      HomologicalComplex.mapBifunctor K (HomologicalComplex.mapBifunctor L N
        (sheafTensor.{u, u, u, u, u} A) (up ℤ)) (sheafTensor.{u, u, u, u, u} A) (up ℤ) :=
  (α_ K L N).hom

/-- The associator of complexes on the summand of tridegree `(a, b, c)`, at the spelling of
`Stacks.SheafOfModules.Tensor.sheafTensor`. -/
private theorem ι₁₂_comp_associator_hom_f' (K L N : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ) (a b c j : ℤ)
    (h : (up ℤ).r (up ℤ) (up ℤ) (up ℤ) (up ℤ) (a, b, c) = j) :
    HomologicalComplex.mapBifunctor₁₂.ι (sheafTensor.{u, u, u, u, u} A)
        (sheafTensor.{u, u, u, u, u} A) K L N (up ℤ) (up ℤ) a b c j h ≫
        (cxAssoc K L N).f j =
      modAssoc (K.X a) (L.X b) (N.X c) ≫
        HomologicalComplex.mapBifunctor₂₃.ι (sheafTensor.{u, u, u, u, u} A)
          (sheafTensor.{u, u, u, u, u} A) K L N (up ℤ) (up ℤ) (up ℤ) a b c j h :=
  AlgebraicGeometry.RingedSite.ι₁₂_comp_associator_hom_f (siteOf A) K L N a b c j h

/-- The left-bracketed side of the associativity identity on the summand of tridegree
`(a, b, c)`. -/
private theorem ι₁₂_comp_mapBifunctorMap_left (K L N P M : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
    (φ : HomologicalComplex.mapBifunctor K L (sheafTensor.{u, u, u, u, u} A) (up ℤ) ⟶ P)
    (ψ : HomologicalComplex.mapBifunctor P N (sheafTensor.{u, u, u, u, u} A) (up ℤ) ⟶ M)
    (a b c ab j : ℤ) (hab : a + b = ab) (hj : ab + c = j)
    (h : (up ℤ).r (up ℤ) (up ℤ) (up ℤ) (up ℤ) (a, b, c) = j) :
    HomologicalComplex.mapBifunctor₁₂.ι (sheafTensor.{u, u, u, u, u} A)
        (sheafTensor.{u, u, u, u, u} A) K L N (up ℤ) (up ℤ) a b c j h ≫
        (HomologicalComplex.mapBifunctorMap φ (𝟙 N) (sheafTensor.{u, u, u, u, u} A) (up ℤ)).f j ≫
          ψ.f j =
      ((sheafTensor.{u, u, u, u, u} A).map
          (HomologicalComplex.ιMapBifunctor K L (sheafTensor.{u, u, u, u, u} A) (up ℤ) a b ab hab ≫
            φ.f ab)).app (N.X c) ≫
        HomologicalComplex.ιMapBifunctor P N (sheafTensor.{u, u, u, u, u} A) (up ℤ) ab c j hj ≫
          ψ.f j := by
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq _ _ _ _ _ _ _ a b c ab j hab hj, Category.assoc,
    HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.id_f,
    CategoryTheory.Functor.map_id, Category.id_comp, Functor.map_comp, NatTrans.comp_app,
    Category.assoc]

/-- The right-bracketed side of the associativity identity on the summand of tridegree
`(a, b, c)`. -/
private theorem ι₁₂_comp_associator_mapBifunctorMap_right
    (K L N Q M : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ)
    (φ : HomologicalComplex.mapBifunctor L N (sheafTensor.{u, u, u, u, u} A) (up ℤ) ⟶ Q)
    (ψ : HomologicalComplex.mapBifunctor K Q (sheafTensor.{u, u, u, u, u} A) (up ℤ) ⟶ M)
    (a b c bc j : ℤ) (hbc : b + c = bc) (hj : a + bc = j)
    (h : (up ℤ).r (up ℤ) (up ℤ) (up ℤ) (up ℤ) (a, b, c) = j) :
    HomologicalComplex.mapBifunctor₁₂.ι (sheafTensor.{u, u, u, u, u} A)
        (sheafTensor.{u, u, u, u, u} A) K L N (up ℤ) (up ℤ) a b c j h ≫
        (cxAssoc K L N).f j ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 K) φ (sheafTensor.{u, u, u, u, u} A) (up ℤ)).f j ≫
          ψ.f j =
      modAssoc (K.X a) (L.X b) (N.X c) ≫
        ((sheafTensor.{u, u, u, u, u} A).obj (K.X a)).map
          (HomologicalComplex.ιMapBifunctor L N (sheafTensor.{u, u, u, u, u} A) (up ℤ) b c bc hbc ≫
            φ.f bc) ≫
        HomologicalComplex.ιMapBifunctor K Q (sheafTensor.{u, u, u, u, u} A) (up ℤ) a bc j hj ≫
          ψ.f j := by
  rw [reassoc_of% (ι₁₂_comp_associator_hom_f' K L N a b c j h),
    HomologicalComplex.mapBifunctor₂₃.ι_eq _ _ _ _ _ _ _ _ a b c bc j hbc hj, Category.assoc,
    HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.id_f,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Functor.map_comp,
    Category.assoc]

/-- **The associativity square on modules from its values on iterated local pure tensors.** -/
private theorem assoc_square_of_tmul
    {Ka Lb Nc Pab Qbc Mn : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)}
    (f₁ : ((sheafTensor.{u, u, u, u, u} A).obj Ka).obj Lb ⟶ Pab)
    (g₂ : ((sheafTensor.{u, u, u, u, u} A).obj Pab).obj Nc ⟶ Mn)
    (f₃ : ((sheafTensor.{u, u, u, u, u} A).obj Lb).obj Nc ⟶ Qbc)
    (g₄ : ((sheafTensor.{u, u, u, u, u} A).obj Ka).obj Qbc ⟶ Mn)
    (h : ∀ (U : (Opens X.carrier)ᵒᵖ) (x : Ka.val.obj U) (y : Lb.val.obj U) (z : Nc.val.obj U),
      g₂.val.app U (tmulClass Pab Nc (f₁.val.app U (tmulClass Ka Lb x y)) z) =
        g₄.val.app U (tmulClass Ka Qbc x (f₃.val.app U (tmulClass Lb Nc y z)))) :
    ((sheafTensor.{u, u, u, u, u} A).map f₁).app Nc ≫ g₂ =
      modAssoc Ka Lb Nc ≫ ((sheafTensor.{u, u, u, u, u} A).obj Ka).map f₃ ≫ g₄ := by
  refine Stacks.SheafOfModules.Tensor.sheafTensor_hom_ext₁₂ A fun U x y z => ?_
  refine ((congrArg (g₂.val.app U) (tensorMap_app_tmulClass f₁ Nc _ z)).trans (h U x y z)).trans ?_
  refine (congrArg (g₄.val.app U) (tensorObjMap_tmulClass Ka f₃ x _)).symm.trans ?_
  exact congrArg
    (fun t => g₄.val.app U ((((sheafTensor.{u, u, u, u, u} A).obj Ka).map f₃).val.app U t))
    (Stacks.SheafOfModules.Tensor.associator_hom_app_sheafifyUnit_tmul A Ka Lb Nc U x y z).symm

/-- The two bracketings of the extended multiplications on an iterated local pure tensor. -/
private theorem assoc_tmul_value
    (m₁ : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ P)
    (m₂ : ((tensorBifunctorNat (A := A)).obj P).obj N ⟶ M)
    (m₃ : ((tensorBifunctorNat (A := A)).obj L).obj N ⟶ Q)
    (m₄ : ((tensorBifunctorNat (A := A)).obj K).obj Q ⟶ M)
    (h : ∀ (a b c : ℕ) (U : (Opens X.carrier)ᵒᵖ) (x : (K.X a).val.obj U)
      (y : (L.X b).val.obj U) (z : (N.X c).val.obj U),
      HEq (multiplicationValue m₂ (a + b) c U (multiplicationValue m₁ a b U x y) z)
        (multiplicationValue m₄ a (b + c) U x (multiplicationValue m₃ b c U y z)))
    (a b c : ℕ) (h₁ : (a : ℤ) + (b : ℤ) = ((a + b : ℕ) : ℤ))
    (h₂ : ((a + b : ℕ) : ℤ) + (c : ℤ) = ((a + b + c : ℕ) : ℤ))
    (h₃ : (b : ℤ) + (c : ℤ) = ((b + c : ℕ) : ℤ))
    (h₄ : (a : ℤ) + ((b + c : ℕ) : ℤ) = ((a + b + c : ℕ) : ℤ))
    (U : (Opens X.carrier)ᵒᵖ) (x : ((K.extend embeddingUpNat).X (a : ℤ)).val.obj U)
    (y : ((L.extend embeddingUpNat).X (b : ℤ)).val.obj U)
    (z : ((N.extend embeddingUpNat).X (c : ℤ)).val.obj U) :
    (HomologicalComplex.ιMapBifunctor (P.extend embeddingUpNat) (N.extend embeddingUpNat)
        (sheafTensor.{u, u, u, u, u} A) (up ℤ) ((a + b : ℕ) : ℤ) (c : ℤ)
          ((a + b + c : ℕ) : ℤ) h₂ ≫ (multiplicationInt m₂).f ((a + b + c : ℕ) : ℤ)).val.app U
      (tmulClass _ _ ((HomologicalComplex.ιMapBifunctor (K.extend embeddingUpNat)
        (L.extend embeddingUpNat) (sheafTensor.{u, u, u, u, u} A) (up ℤ) (a : ℤ) (b : ℤ)
          ((a + b : ℕ) : ℤ) h₁ ≫ (multiplicationInt m₁).f ((a + b : ℕ) : ℤ)).val.app U
            (tmulClass _ _ x y)) z) =
    (HomologicalComplex.ιMapBifunctor (K.extend embeddingUpNat) (Q.extend embeddingUpNat)
        (sheafTensor.{u, u, u, u, u} A) (up ℤ) (a : ℤ) ((b + c : ℕ) : ℤ)
          ((a + b + c : ℕ) : ℤ) h₄ ≫ (multiplicationInt m₄).f ((a + b + c : ℕ) : ℤ)).val.app U
      (tmulClass _ _ x ((HomologicalComplex.ιMapBifunctor (L.extend embeddingUpNat)
        (N.extend embeddingUpNat) (sheafTensor.{u, u, u, u, u} A) (up ℤ) (b : ℤ) (c : ℤ)
          ((b + c : ℕ) : ℤ) h₃ ≫ (multiplicationInt m₃).f ((b + c : ℕ) : ℤ)).val.app U
            (tmulClass _ _ y z))) := by
  rw [multiplicationInt_ι_tmul m₁ a b (a + b) rfl h₁,
    multiplicationInt_ι_tmul m₃ b c (b + c) rfl h₃,
    multiplicationInt_ι_tmul m₂ (a + b) c (a + b + c) rfl h₂,
    multiplicationInt_ι_tmul m₄ a (b + c) (a + b + c) (Nat.add_assoc a b c).symm h₄]
  refine congrArg _ ?_
  simp only [extendSection, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    Stacks.SheafOfModules.hom_val_app_inv_val_app]
  exact XIsoOfEq_val_app_of_heq (M := M) (rfl : a + b + c = a + b + c)
    (Nat.add_assoc a b c).symm (h a b c U _ _ _)

/-- **Associativity of the extended multiplications from associativity on local pure tensors.**
If the two bracketings of four multiplications agree on the iterated local pure tensors of
homogeneous local sections, the extended multiplications satisfy the associativity identity in
the symmetric monoidal category of complexes of Stacks 0FPQ:
`(m₁ ⊗ 𝟙) ≫ m₂ = α ≫ (𝟙 ⊗ m₃) ≫ m₄` on the extensions by zero. -/
theorem multiplicationInt_assoc
    (m₁ : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ P)
    (m₂ : ((tensorBifunctorNat (A := A)).obj P).obj N ⟶ M)
    (m₃ : ((tensorBifunctorNat (A := A)).obj L).obj N ⟶ Q)
    (m₄ : ((tensorBifunctorNat (A := A)).obj K).obj Q ⟶ M)
    (h : ∀ (a b c : ℕ) (U : (Opens X.carrier)ᵒᵖ) (x : (K.X a).val.obj U)
      (y : (L.X b).val.obj U) (z : (N.X c).val.obj U),
      HEq (multiplicationValue m₂ (a + b) c U (multiplicationValue m₁ a b U x y) z)
        (multiplicationValue m₄ a (b + c) U x (multiplicationValue m₃ b c U y z))) :
    (multiplicationInt m₁ ⊗ₘ 𝟙 (N.extend embeddingUpNat)) ≫ multiplicationInt m₂ =
      (α_ (K.extend embeddingUpNat) (L.extend embeddingUpNat) (N.extend embeddingUpNat)).hom ≫
        (𝟙 (K.extend embeddingUpNat) ⊗ₘ multiplicationInt m₃) ≫ multiplicationInt m₄ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : ∃ k : ℕ, (k : ℤ) = n
  · obtain ⟨k, rfl⟩ := hn
    refine HomologicalComplex.mapBifunctor₁₂.hom_ext (F₁₂ := sheafTensor.{u, u, u, u, u} A)
      (G := sheafTensor.{u, u, u, u, u} A) (c₁₂ := up ℤ) fun i₁ i₂ i₃ hi => ?_
    have hi' : i₁ + i₂ + i₃ = (k : ℤ) := hi
    by_cases hneg : i₁ < 0 ∨ i₂ < 0 ∨ i₃ < 0
    · refine IsZero.eq_of_src ?_ _ _
      rcases hneg with h₁ | h₂ | h₃
      · exact isZero_tensor_left _ (isZero_tensor_left _
          (isZero_extend_X_of_neg (K := K) h₁))
      · exact isZero_tensor_left _ (isZero_tensor_right _
          (isZero_extend_X_of_neg (K := L) h₂))
      · exact isZero_tensor_right _
          (isZero_extend_X_of_neg (K := N) h₃)
    · push Not at hneg
      obtain ⟨a, rfl⟩ : ∃ a : ℕ, (a : ℤ) = i₁ := ⟨i₁.toNat, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b : ℕ, (b : ℤ) = i₂ := ⟨i₂.toNat, by omega⟩
      obtain ⟨c, rfl⟩ : ∃ c : ℕ, (c : ℤ) = i₃ := ⟨i₃.toNat, by omega⟩
      obtain rfl : a + b + c = k := by omega
      change HomologicalComplex.mapBifunctor₁₂.ι (sheafTensor.{u, u, u, u, u} A)
          (sheafTensor.{u, u, u, u, u} A)
          (K.extend embeddingUpNat) (L.extend embeddingUpNat) (N.extend embeddingUpNat)
          (up ℤ) (up ℤ) (a : ℤ) (b : ℤ) (c : ℤ) ((a + b + c : ℕ) : ℤ) hi ≫
          (HomologicalComplex.mapBifunctorMap (multiplicationInt m₁) (𝟙 (N.extend embeddingUpNat))
            (sheafTensor.{u, u, u, u, u} A) (up ℤ)).f ((a + b + c : ℕ) : ℤ) ≫
            (multiplicationInt m₂).f ((a + b + c : ℕ) : ℤ) =
        HomologicalComplex.mapBifunctor₁₂.ι (sheafTensor.{u, u, u, u, u} A)
          (sheafTensor.{u, u, u, u, u} A)
          (K.extend embeddingUpNat) (L.extend embeddingUpNat) (N.extend embeddingUpNat)
          (up ℤ) (up ℤ) (a : ℤ) (b : ℤ) (c : ℤ) ((a + b + c : ℕ) : ℤ) hi ≫
          (cxAssoc (K.extend embeddingUpNat) (L.extend embeddingUpNat)
            (N.extend embeddingUpNat)).f ((a + b + c : ℕ) : ℤ) ≫
          (HomologicalComplex.mapBifunctorMap (𝟙 (K.extend embeddingUpNat)) (multiplicationInt m₃)
            (sheafTensor.{u, u, u, u, u} A) (up ℤ)).f ((a + b + c : ℕ) : ℤ) ≫
            (multiplicationInt m₄).f ((a + b + c : ℕ) : ℤ)
      rw [ι₁₂_comp_mapBifunctorMap_left _ _ _ _ _ _ _ (a : ℤ) (b : ℤ) (c : ℤ) ((a + b : ℕ) : ℤ)
          ((a + b + c : ℕ) : ℤ) (by push_cast; rfl) (by push_cast; rfl),
        ι₁₂_comp_associator_mapBifunctorMap_right _ _ _ _ _ _ _ (a : ℤ) (b : ℤ) (c : ℤ)
          ((b + c : ℕ) : ℤ) ((a + b + c : ℕ) : ℤ) (by push_cast; rfl) (by push_cast; ring)]
      exact assoc_square_of_tmul _ _ _ _ fun U x y z =>
        assoc_tmul_value m₁ m₂ m₃ m₄ h a b c _ _ _ _ U x y z
  · exact (HomologicalComplex.isZero_extend_X M embeddingUpNat n
      fun i hi => hn ⟨i, hi⟩).eq_of_tgt _ _

end Monoidal

section Symmetric

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor
  _root_.SheafOfModules.symmetricCategorySheafTensor
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor
  _root_.SheafOfModules.monoidalClosedSheafTensor
  _root_.SheafOfModules.preservesColimit_tensorRight_sheafTensor
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexSymmetricCategory

/-- The symmetry of sheaves of modules, typed at the spelling of `sheafTensor`. -/
private abbrev modBraid (F G : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) :
    ((sheafTensor.{u, u, u, u, u} A).obj F).obj G ⟶ ((sheafTensor.{u, u, u, u, u} A).obj G).obj F :=
  (β_ F G).hom

/-- The Koszul symmetry of complexes, typed at the spelling of total complexes of
`sheafTensor`. -/
private abbrev cxBraid (K L : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ) :
    HomologicalComplex.mapBifunctor K L (sheafTensor.{u, u, u, u, u} A) (up ℤ) ⟶
      HomologicalComplex.mapBifunctor L K (sheafTensor.{u, u, u, u, u} A) (up ℤ) :=
  (β_ K L).hom

/-- The Koszul symmetry of complexes on the summand of bidegree `(a, b)`. -/
private theorem ι_comp_braiding_f' (K L : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℤ) (a b n : ℤ) (h : a + b = n)
    (h' : b + a = n) :
    HomologicalComplex.ιMapBifunctor K L (sheafTensor.{u, u, u, u, u} A) (up ℤ) a b n h ≫
        (cxBraid K L).f n =
      ((a * b).negOnePow : ℤˣ) • (modBraid (K.X a) (L.X b) ≫
        HomologicalComplex.ιMapBifunctor L K (sheafTensor.{u, u, u, u, u} A) (up ℤ) b a n h') :=
  CochainComplex.ιTensorObj_koszulBraiding K L a b n h

/-- The two sides of the commutativity identity on a local pure tensor. -/
private theorem braiding_tmul_value
    (m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M)
    (m' : ((tensorBifunctorNat (A := A)).obj L).obj K ⟶ M)
    (h : ∀ (a b : ℕ) (U : (Opens X.carrier)ᵒᵖ) (x : (K.X a).val.obj U) (y : (L.X b).val.obj U),
      HEq (multiplicationValue m a b U x y)
        ((-1 : ℤ) ^ (a * b) • multiplicationValue m' b a U y x))
    (a b : ℕ) (h₁ : (a : ℤ) + (b : ℤ) = ((a + b : ℕ) : ℤ))
    (h₂ : (b : ℤ) + (a : ℤ) = ((a + b : ℕ) : ℤ))
    (U : (Opens X.carrier)ᵒᵖ) (x : ((K.extend embeddingUpNat).X (a : ℤ)).val.obj U)
    (y : ((L.extend embeddingUpNat).X (b : ℤ)).val.obj U) :
    (((a : ℤ) * (b : ℤ)).negOnePow : ℤ) •
      (HomologicalComplex.ιMapBifunctor (L.extend embeddingUpNat) (K.extend embeddingUpNat)
        (sheafTensor.{u, u, u, u, u} A) (up ℤ) (b : ℤ) (a : ℤ) ((a + b : ℕ) : ℤ) h₂ ≫
          (multiplicationInt m').f ((a + b : ℕ) : ℤ)).val.app U (tmulClass _ _ y x) =
    (HomologicalComplex.ιMapBifunctor (K.extend embeddingUpNat) (L.extend embeddingUpNat)
        (sheafTensor.{u, u, u, u, u} A) (up ℤ) (a : ℤ) (b : ℤ) ((a + b : ℕ) : ℤ) h₁ ≫
          (multiplicationInt m).f ((a + b : ℕ) : ℤ)).val.app U (tmulClass _ _ x y) := by
  rw [multiplicationInt_ι_tmul m a b (a + b) rfl h₁,
    multiplicationInt_ι_tmul m' b a (a + b) (Nat.add_comm b a) h₂,
    XIsoOfEq_val_app_of_heq (M := M) (rfl : a + b = a + b) (Nat.add_comm b a)
      (h a b U _ _)]
  have hs : (((a : ℤ) * (b : ℤ)).negOnePow : ℤ) = (-1 : ℤ) ^ (a * b) := by
    rw [← Int.coe_negOnePow_natCast]; push_cast; rfl
  rw [hs]
  exact (map_zsmul (ConcreteCategory.hom ((M.extendXIso embeddingUpNat (i := a + b)
    (i' := ((a + b : ℕ) : ℤ)) rfl).inv.val.app U)) _ _).symm.trans
      (congrArg _ (map_zsmul (ConcreteCategory.hom
        ((M.XIsoOfEq (Nat.add_comm b a)).hom.val.app U)) _ _).symm)

/-- **Graded commutativity of the extended multiplications from graded commutativity on local
pure tensors.** If `m(x ⊗ y) = (-1)^{ab} m'(y ⊗ x)` on the local pure tensors of a section `x` of
`K^a` and a section `y` of `L^b`, then the Koszul symmetry of complexes of Stacks 0FPQ carries the
extended `m'` to the extended `m`: `β ≫ m' = m` on the extensions by zero. -/
theorem multiplicationInt_braiding
    (m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M)
    (m' : ((tensorBifunctorNat (A := A)).obj L).obj K ⟶ M)
    (h : ∀ (a b : ℕ) (U : (Opens X.carrier)ᵒᵖ) (x : (K.X a).val.obj U) (y : (L.X b).val.obj U),
      HEq (multiplicationValue m a b U x y)
        ((-1 : ℤ) ^ (a * b) • multiplicationValue m' b a U y x)) :
    (β_ (K.extend embeddingUpNat) (L.extend embeddingUpNat)).hom ≫ multiplicationInt m' =
      multiplicationInt m := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : ∃ k : ℕ, (k : ℤ) = n
  · obtain ⟨k, rfl⟩ := hn
    refine HomologicalComplex.mapBifunctor.hom_ext fun i₁ i₂ hi => ?_
    have hi' : i₁ + i₂ = (k : ℤ) := hi
    by_cases hneg : i₁ < 0 ∨ i₂ < 0
    · refine IsZero.eq_of_src ?_ _ _
      rcases hneg with h₁ | h₂
      · exact isZero_tensor_left _
          (isZero_extend_X_of_neg (K := K) h₁)
      · exact isZero_tensor_right _
          (isZero_extend_X_of_neg (K := L) h₂)
    · push Not at hneg
      obtain ⟨a, rfl⟩ : ∃ a : ℕ, (a : ℤ) = i₁ := ⟨i₁.toNat, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b : ℕ, (b : ℤ) = i₂ := ⟨i₂.toNat, by omega⟩
      obtain rfl : a + b = k := by omega
      change HomologicalComplex.ιMapBifunctor (K.extend embeddingUpNat) (L.extend embeddingUpNat)
          (sheafTensor.{u, u, u, u, u} A) (up ℤ) (a : ℤ) (b : ℤ) ((a + b : ℕ) : ℤ) hi ≫
          (cxBraid (K.extend embeddingUpNat) (L.extend embeddingUpNat)).f ((a + b : ℕ) : ℤ) ≫
            (multiplicationInt m').f ((a + b : ℕ) : ℤ) = _
      rw [reassoc_of% (ι_comp_braiding_f' _ _ (a : ℤ) (b : ℤ) ((a + b : ℕ) : ℤ) hi
        (by push_cast; ring)), Linear.units_smul_comp, Category.assoc]
      refine Stacks.SheafOfModules.FlatSquareZero.tensorSheaf_hom_ext A _ _ _ fun U x y => ?_
      rw [Units.smul_def]
      refine (_root_.SheafOfModules.zsmul_val_app _ _ U _).trans (Eq.trans ?_
        (braiding_tmul_value m m' h a b hi (by push_cast; ring) U x y))
      exact congrArg (fun t => (((a : ℤ) * (b : ℤ)).negOnePow : ℤ) •
        (HomologicalComplex.ιMapBifunctor (L.extend embeddingUpNat) (K.extend embeddingUpNat)
          (sheafTensor.{u, u, u, u, u} A) (up ℤ) (b : ℤ) (a : ℤ) ((a + b : ℕ) : ℤ)
            (show (b : ℤ) + (a : ℤ) = ((a + b : ℕ) : ℤ) by push_cast; ring) ≫
              (multiplicationInt m').f ((a + b : ℕ) : ℤ)).val.app U t)
        (Stacks.SheafOfModules.Tensor.braiding_hom_app_sheafifyUnit_tmul A _ _ U x y)
  · exact (HomologicalComplex.isZero_extend_X M embeddingUpNat n
      fun i hi => hn ⟨i, hi⟩).eq_of_tgt _ _

end Symmetric

end AlgebraicGeometry.SheafOfModules

end
