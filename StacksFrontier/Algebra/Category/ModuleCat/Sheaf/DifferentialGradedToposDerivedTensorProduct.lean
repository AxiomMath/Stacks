module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesId
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDirectImageComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPullbackAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDerivedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensorProduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived tensor product, as the functor of Tag 0FTF at the identity

Let `(Sh(C), O)` be a ringed topos, let `A` and `A'` be sheaves of differential graded
`O`-algebras and let `N` be a differential graded `(A, A')`-bimodule. Tag 0FTF, applied to the
identity morphism of `(Sh(C), O)` and to the identity `A ⟶ id_*A`, gives a functor
`D(A, d) ⥤ D(A', d)`: by [Stacks, Tag 0FTG](https://stacks.math.columbia.edu/tag/0FTG) (1) this is
**the derived tensor product** `- ⊗^𝐋_A N`.

This file constructs the identity homomorphism `A ⟶ id_*A`, defines that functor, and identifies
it, compatibly with the comparison maps, with the derived tensor product
`SheafOfModules.DifferentialGradedModule.derivedTensorProduct` of the ringed site.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.toposIdAlgebraHom`: the identity `A ⟶ id_*A`, a unital
  homomorphism of sheaves of differential graded algebras.
* `SheafOfModules.DifferentialGradedModule.toposPushforwardIsoOfIso`: for `f : X ⟶ X` with a
  monoidal isomorphism `f_* ≅ 𝟭`, the direct image along `(f, A ⟶ f_*A)` is the identity functor
  of right differential graded `A`-modules, and so is the pullback
  (`toposDGPullbackIsoOfIso`); hence the functor of Tag 0FTF there is the derived tensor product
  (`derivedToposPullbackTensorIsoOfIso`).
* `SheafOfModules.DifferentialGradedModule.derivedTensorProductTopos`: **the derived tensor
  product `- ⊗^𝐋_A N`** of Tag 0FTG (1), the functor of Tag 0FTF at the identity.
* `SheafOfModules.DifferentialGradedModule.derivedTensorProductToposIso`: it is the derived tensor
  product `derivedTensorProduct` of the ringed site, compatibly with the comparison maps
  (`derivedTensorProductToposIso_hom_fac`).

## References

* [Stacks Project, Tag 0FTG](https://stacks.math.columbia.edu/tag/0FTG)
* [Stacks Project, Tag 0FTF](https://stacks.math.columbia.edu/tag/0FTF)
* [Stacks Project, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules

universe u

namespace SheafOfModules.DifferentialGradedModule

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-- A tensor product with an identity followed by a whiskering is a tensor product. -/
theorem tensorHom_id_comp_whiskerLeft {C : Type*} [Category C] [MonoidalCategory C]
    {Y₁ Y₂ Z₁ Z₂ : C} (a : Y₁ ⟶ Y₂) (b : Z₁ ⟶ Z₂) :
    (a ⊗ₘ 𝟙 Z₁) ≫ (Y₂ ◁ b) = a ⊗ₘ b := by
  rw [MonoidalCategory.tensorHom_id, ← MonoidalCategory.tensorHom_def]

/-! ### A direct image of sheaves of modules isomorphic to the identity -/

section General

variable {X : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]

variable (f : RingedToposHom X X)
  (e : toposDirectImageModules (X := X) (Y := X) f ≅ 𝟭 (SheafOfModules.{u} (toRingCat X.J X.O)))
  [NatTrans.IsMonoidal e.hom]

include e in
/-- The inverse comparison `𝟭 ≅ f_*` carries the tensorator of `f_*` to the identity. -/
theorem tensorHom_inv_comp_μ_of_iso (M N : SheafOfModules.{u} (toRingCat X.J X.O)) :
    (e.inv.app M ⊗ₘ e.inv.app N) ≫
        Functor.LaxMonoidal.μ (toposDirectImageModules (X := X) (Y := X) f) M N =
      e.inv.app (M ⊗ N) :=
  (NatTrans.IsMonoidal.tensor (τ := e.inv) M N).symm.trans (Category.id_comp _)

include e in
/-- The inverse comparison `𝟭 ≅ f_*` at the unit is the unit of the lax structure of `f_*`. -/
theorem inv_app_unit_of_iso :
    e.inv.app (𝟙_ (SheafOfModules.{u} (toRingCat X.J X.O))) =
      Functor.LaxMonoidal.ε (toposDirectImageModules (X := X) (Y := X) f) :=
  (Category.id_comp _).symm.trans (NatTrans.IsMonoidal.unit (τ := e.inv))

variable (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))

include e in
/-- The image of a multiplication under `f_*`, after the comparisons, is the multiplication
followed by the comparison. -/
theorem mapMul_comp_inv_app_of_iso
    {P Q R : SheafOfModules.{u} (toRingCat X.J X.O)} (μ' : P ⊗ Q ⟶ R) :
    μ' ≫ e.inv.app R =
      (e.inv.app P ⊗ₘ e.inv.app Q) ≫
        Stacks.MonoidalGraded.mapMul (toposDirectImageModules (X := X) (Y := X) f) μ' := by
  simp only [Stacks.MonoidalGraded.mapMul]
  rw [reassoc_of% (tensorHom_inv_comp_μ_of_iso f e P Q)]
  exact e.inv.naturality μ'

include e in
/-- An action `P ⊗ Q ⟶ R` restricted along the comparison in the second factor and transported
along `f_*`, after the comparison in the first factor, is the action followed by the comparison. -/
theorem whiskerLeft_comp_mapMul_comp_inv_app_of_iso
    {P Q R : SheafOfModules.{u} (toRingCat X.J X.O)} (s : P ⊗ Q ⟶ R) :
    s ≫ e.inv.app R =
      (e.inv.app P ⊗ₘ 𝟙 Q) ≫ ((toposDirectImageModules (X := X) (Y := X) f).obj P ◁ e.inv.app Q ≫
        Stacks.MonoidalGraded.mapMul (toposDirectImageModules (X := X) (Y := X) f) s) := by
  rw [← Category.assoc, tensorHom_id_comp_whiskerLeft]
  exact mapMul_comp_inv_app_of_iso f e s

/-- The multiplication of `A`, followed by the comparison `A ⟶ f_*A`, is the tensor product of
the comparisons followed by the multiplication of `f_*A`. -/
theorem mulSheaf_comp_inv_app_of_iso (n m : ℤ) :
    GradedAlgebra.mulSheaf A.toGradedAlgebra n m ≫ e.inv.app (A.complex.X (n + m)) =
      (e.inv.app (A.complex.X n) ⊗ₘ e.inv.app (A.complex.X m)) ≫
        GradedAlgebra.mulSheaf (toposPushforwardAlgebra (Osharp := X.O) (Psharp := X.O)
          (toposDirectImageModules (X := X) (Y := X) f) A).toGradedAlgebra n m := by
  have h : GradedAlgebra.mulSheaf (toposPushforwardAlgebra (Osharp := X.O) (Psharp := X.O)
        (toposDirectImageModules (X := X) (Y := X) f) A).toGradedAlgebra n m =
      Stacks.MonoidalGraded.mapMul (toposDirectImageModules (X := X) (Y := X) f)
        (GradedAlgebra.mulSheaf A.toGradedAlgebra n m) :=
    GradedAlgebra.mulSheaf_transport (toposDirectImageModules (X := X) (Y := X) f)
      A.toGradedAlgebra
      (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O)
      (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O) n m
  rw [h]
  exact mapMul_comp_inv_app_of_iso f e _

/-- **The comparison `A ⟶ f_*A`** of sheaves of differential graded algebras attached to a
monoidal isomorphism `f_* ≅ 𝟭`: in degree `n` it is the comparison `A^n ≅ f_*A^n`. -/
def toposAlgebraHomOfIso :
    A ⟶ toposPushforwardAlgebra (Osharp := X.O) (Psharp := X.O)
      (toposDirectImageModules (X := X) (Y := X) f) A where
  toHomologicalComplex :=
    { f := fun n ↦ e.inv.app (A.complex.X n)
      comm' := fun i j _ ↦ (e.inv.naturality (A.complex.d i j)).symm }
  map_mul n m := (GradedAlgebra.mulSheaf_comp_eq_iff
      (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O)
      A.toGradedAlgebra
      (toposPushforwardAlgebra (Osharp := X.O) (Psharp := X.O)
        (toposDirectImageModules (X := X) (Y := X) f) A).toGradedAlgebra
      (fun n ↦ e.inv.app (A.complex.X n)) n m).mp (mulSheaf_comp_inv_app_of_iso f e A n m)

/-- The comparison `A ⟶ f_*A` in degree `n`. -/
@[simp]
theorem toposAlgebraHomOfIso_f (n : ℤ) :
    (toposAlgebraHomOfIso f e A).toHomologicalComplex.f n = e.inv.app (A.complex.X n) :=
  rfl

/-- **The comparison `A ⟶ f_*A` is unital**, the isomorphism `f_* ≅ 𝟭` being compatible with the
units. -/
theorem isUnital_toposAlgebraHomOfIso : (toposAlgebraHomOfIso f e A).IsUnital := by
  refine DifferentialGradedAlgebra.Hom.isUnital_of_oneHom_comp _ ?_
  rw [oneHom_toGradedAlgebra_transport (toposDirectImageModules (X := X) (Y := X) f)
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O)
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O) A,
    ← inv_app_unit_of_iso f e]
  exact e.inv.naturality _

/-- The action of `Q`, followed by the comparison `Q ⟶ f_*Q`, is the comparison in the first
factor followed by the action of `f_*Q`. -/
theorem smulSheaf_comp_inv_app_of_iso (Q : DifferentialGradedModule.{u, u, u} A) (n i : ℤ) :
    smulSheaf Q n i ≫ e.inv.app (Q.complex.X (n + i)) =
      (e.inv.app (Q.complex.X n) ⊗ₘ 𝟙 (A.complex.X i)) ≫
        smulSheaf ((toposPushforward (toposDirectImageModules (X := X) (Y := X) f)
          (toposAlgebraHomOfIso f e A) (isUnital_toposAlgebraHomOfIso f e A)).obj Q) n i := by
  rw [smulSheaf_toposPushforward (toposDirectImageModules (X := X) (Y := X) f)
      (toposAlgebraHomOfIso f e A) (isUnital_toposAlgebraHomOfIso f e A) Q,
    toposAlgebraHomOfIso_f]
  dsimp only [toposPushforward_obj_complex_X]
  exact whiskerLeft_comp_mapMul_comp_inv_app_of_iso f e (P := Q.complex.X n)
    (Q := A.complex.X i) (R := Q.complex.X (n + i)) (smulSheaf Q n i)

/-- The comparison `Q ⟶ f_*Q` of right differential graded `A`-modules, degreewise the
comparison `𝟭 ≅ f_*`. -/
def toposPushforwardHomAppOfIso (Q : DifferentialGradedModule.{u, u, u} A) :
    Q ⟶ (toposPushforward (toposDirectImageModules (X := X) (Y := X) f)
      (toposAlgebraHomOfIso f e A) (isUnital_toposAlgebraHomOfIso f e A)).obj Q where
  toHomologicalComplex :=
    { f := fun n ↦ e.inv.app (Q.complex.X n)
      comm' := fun i j _ ↦ (e.inv.naturality (Q.complex.d i j)).symm }
  map_mul n i := (smulSheaf_comp_eq_iff Q
      (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf X.O)
      ((toposPushforward (toposDirectImageModules (X := X) (Y := X) f)
        (toposAlgebraHomOfIso f e A) (isUnital_toposAlgebraHomOfIso f e A)).obj Q)
      (fun n ↦ e.inv.app (Q.complex.X n)) n i).mp (smulSheaf_comp_inv_app_of_iso f e A Q n i)

/-- **The direct image of right differential graded modules along `(f, A ⟶ f_*A)` is the
identity**, degreewise the comparison `𝟭 ≅ f_*` of sheaves of modules. -/
def toposPushforwardIsoOfIso :
    𝟭 (DifferentialGradedModule.{u, u, u} A) ≅
      toposPushforward (toposDirectImageModules (X := X) (Y := X) f)
        (toposAlgebraHomOfIso f e A) (isUnital_toposAlgebraHomOfIso f e A) :=
  NatIso.ofComponents (fun Q ↦ isoOfDegreewiseIso (toposPushforwardHomAppOfIso f e A Q)
      (fun p ↦ (e.app (Q.complex.X p)).isIso_inv))
    (fun {Q Q'} (g : Q ⟶ Q') ↦ Hom.ext fun n ↦ e.inv.naturality (g.toHomologicalComplex.f n))

/-- **The pullback of right differential graded modules along `(f, A ⟶ f_*A)` is the identity**:
`M ↦ f^*M ⊗_{f^*A} A` is left adjoint to the direct image, which is the identity. -/
def toposDGPullbackIsoOfIso :
    toposDGPullback f (toposAlgebraHomOfIso f e A) (isUnital_toposAlgebraHomOfIso f e A) ≅
      𝟭 (DifferentialGradedModule.{u, u, u} A) :=
  (toposBaseChangeAdjunction f (toposAlgebraHomOfIso f e A)
    (isUnital_toposAlgebraHomOfIso f e A)).leftAdjointUniq
      (Adjunction.id.ofNatIsoRight (toposPushforwardIsoOfIso f e A))

variable {A} {A' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  (N : DifferentialGradedBimodule.{u, u, u} A A')

/-- The functor `M ↦ f^*M ⊗_A N` of Tag 0FTE along `(f, A ⟶ f_*A)` is `M ↦ M ⊗_A N`. -/
def toposPullbackTensorIsoOfIso :
    toposPullbackTensor f (toposAlgebraHomOfIso f e A) (isUnital_toposAlgebraHomOfIso f e A) N ≅
      pullbackTensorFunctor (idPullbackData (A := A)) (tensorData (X := X.toRingedSite) N) :=
  Functor.isoWhiskerRight (toposDGPullbackIsoOfIso f e A) (toposPullbackTensorData N).functor

/-- The same on homotopy categories. -/
def homotopyToposPullbackTensorIsoOfIso :
    homotopyToposPullbackTensor f (toposAlgebraHomOfIso f e A)
        (isUnital_toposAlgebraHomOfIso f e A) N ≅
      HomotopyCategory.pullbackTensor (idPullbackDataHomotopyExtension (A := A))
        (tensorData (X := X.toRingedSite) N) :=
  HomotopyCategory.descendNatIso (preservesHomotopic_toposPullbackTensor _ _ _ N)
    (preservesHomotopic_pullbackTensorFunctor (idPullbackDataHomotopyExtension (A := A))
      (tensorData (X := X.toRingedSite) N))
    (toposPullbackTensorIsoOfIso f e N)

/-- The comparison map of the functor of Tag 0FTF along `(f, A ⟶ f_*A)`, followed by the
identification of `M ↦ f^*M ⊗_A N` with `M ↦ M ⊗_A N`. -/
def derivedToposPullbackTensorCounitOfIso :
    toDerivedCategory A ⋙ derivedToposPullbackTensor f (toposAlgebraHomOfIso f e A)
        (isUnital_toposAlgebraHomOfIso f e A) N ⟶
      HomotopyCategory.pullbackTensor (idPullbackDataHomotopyExtension (A := A))
          (tensorData (X := X.toRingedSite) N) ⋙ toDerivedCategory A' :=
  derivedToposPullbackTensorCounit _ _ _ N ≫
    Functor.whiskerRight (homotopyToposPullbackTensorIsoOfIso f e N).hom (toDerivedCategory A')

/-- With this comparison map, the functor of Tag 0FTF along `(f, A ⟶ f_*A)` is a left derived
functor of `M ↦ M ⊗_A N` followed by the localization. -/
theorem isLeftDerivedFunctor_derivedToposPullbackTensorCounitOfIso :
    (derivedToposPullbackTensor f (toposAlgebraHomOfIso f e A)
        (isUnital_toposAlgebraHomOfIso f e A) N).IsLeftDerivedFunctor
      (derivedToposPullbackTensorCounitOfIso f e N) (quasiIsomorphisms.{u, u, u} A) := by
  rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension]
  refine (Functor.isRightKanExtension_iff_of_iso₂ (derivedToposPullbackTensorCounit _ _ _ N) _
    (Functor.isoWhiskerRight (homotopyToposPullbackTensorIsoOfIso f e N) (toDerivedCategory A'))
    (Iso.refl _) ?_).1 ?_
  · exact (Category.id_comp _).trans rfl
  · exact (Functor.isLeftDerivedFunctor_iff_isRightKanExtension _ _
      (quasiIsomorphisms.{u, u, u} A)).1 inferInstance

/-- **The functor of Tag 0FTF along `(f, A ⟶ f_*A)` is the derived tensor product**, both being
left derived functors of `M ↦ M ⊗_A N` followed by the localization. -/
def derivedToposPullbackTensorIsoOfIso :
    derivedToposPullbackTensor f (toposAlgebraHomOfIso f e A)
        (isUnital_toposAlgebraHomOfIso f e A) N ≅
      derivedTensorProduct (X := X.toRingedSite) N :=
  derivedTensorProductIsoOfIsLeftDerivedFunctor (X := X.toRingedSite) N _
    (derivedToposPullbackTensorCounitOfIso f e N)
    (isLeftDerivedFunctor_derivedToposPullbackTensorCounitOfIso f e N)

/-- The isomorphism `derivedToposPullbackTensorIsoOfIso` is compatible with the comparison
maps. -/
theorem derivedToposPullbackTensorIsoOfIso_hom_fac :
    Functor.whiskerLeft (toDerivedCategory A) (derivedToposPullbackTensorIsoOfIso f e N).hom ≫
        derivedTensorProductCounit (X := X.toRingedSite) N =
      derivedToposPullbackTensorCounit _ _ _ N ≫
        Functor.whiskerRight (homotopyToposPullbackTensorIsoOfIso f e N).hom
          (toDerivedCategory A') :=
  derivedTensorProductIsoOfIsLeftDerivedFunctor_hom_fac (X := X.toRingedSite) N _
    (derivedToposPullbackTensorCounitOfIso f e N)
    (isLeftDerivedFunctor_derivedToposPullbackTensorCounitOfIso f e N)

end General

/-! ### The identity morphism, and Tag 0FTG (1) -/

section Tags

attribute [local instance] AlgebraicGeometry.RingedTopos.hasSheafCompose_forget₂_ringCat
  AlgebraicGeometry.RingedTopos.hasSheafify_addCommGrpCat
  AlgebraicGeometry.RingedTopos.wEqualsLocallyBijective_addCommGrpCat

variable {X : AlgebraicGeometry.RingedTopos.{u, u, u}}

/-- The direct image of sheaves of modules along the identity morphism of a ringed topos is the
identity functor, at the `toRingCat` spelling of the structure sheaf. -/
abbrev toposDirectImageIdIso :
    toposDirectImageModules (X := X) (Y := X) (RingedToposHom.id X) ≅
      𝟭 (SheafOfModules.{u} (toRingCat X.J X.O)) :=
  pushforwardModulesIdIso X

/-- The comparison `id_* ≅ 𝟭` is monoidal, at the `toRingCat` spelling. -/
instance isMonoidal_toposDirectImageIdIso_hom :
    NatTrans.IsMonoidal (toposDirectImageIdIso (X := X)).hom :=
  isMonoidal_pushforwardModulesIdIso_hom X

variable (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))

/-- **The identity homomorphism `A ⟶ id_*A`** of sheaves of differential graded algebras along
the identity morphism of a ringed topos: in degree `n` it is the comparison `A^n ≅ id_*A^n`, the
identity on underlying sheaves of sets. -/
abbrev toposIdAlgebraHom :
    A ⟶ toposPushforwardAlgebra (Osharp := X.O) (Psharp := X.O)
      (toposDirectImageModules (X := X) (Y := X) (RingedToposHom.id X)) A :=
  toposAlgebraHomOfIso (RingedToposHom.id X) toposDirectImageIdIso A

/-- The identity homomorphism `A ⟶ id_*A` is unital. -/
theorem isUnital_toposIdAlgebraHom : (toposIdAlgebraHom A).IsUnital :=
  isUnital_toposAlgebraHomOfIso _ _ A


variable {A A' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)}
  (N : DifferentialGradedBimodule.{u, u, u} A A')

/-- The functor `M ↦ id^*M ⊗_A N` of Tag 0FTE at the identity is `M ↦ M ⊗_A N`, on homotopy
categories. -/
abbrev homotopyToposPullbackTensorIdIso :
    homotopyToposPullbackTensor (RingedToposHom.id X) (toposIdAlgebraHom A)
        (isUnital_toposIdAlgebraHom A) N ≅
      HomotopyCategory.pullbackTensor (idPullbackDataHomotopyExtension (A := A))
        (tensorData (X := X.toRingedSite) N) :=
  homotopyToposPullbackTensorIsoOfIso (RingedToposHom.id X) toposDirectImageIdIso N

/-- **The derived tensor product** `- ⊗^𝐋_A N : D(A, d) ⥤ D(A', d)`. Let `(Sh(C), O)` be a ringed
topos, let `A` and `A'` be sheaves of differential graded `O`-algebras and let `N` be a
differential graded `(A, A')`-bimodule. The derived tensor product is the functor
`D(A, d) ⥤ D(A', d)` of Tag 0FTF for the identity morphism of `(Sh(C), O)` and the identity
homomorphism `A ⟶ id_*A`: `derivedPullbackTensorRingedTopos` at `RingedToposHom.id` and
`toposIdAlgebraHom`. It is the left derived functor of `M ↦ M ⊗_A N` followed by the localization,
and it is the derived tensor product `derivedTensorProduct` constructed on the ringed site
(`derivedTensorProductToposIso`). -/
@[stacks 0FTG "(1) the derived tensor product - ⊗^L_A N", sga "4 XVII 4.2.12" "The case g = id"]
def derivedTensorProductTopos :
    derivedCategory.{u, u, u} A ⥤ derivedCategory.{u, u, u} A' :=
  derivedPullbackTensorRingedTopos (RingedToposHom.id X) (toposIdAlgebraHom A)
    (isUnital_toposIdAlgebraHom A) N

/-- The comparison map `M ⊗^𝐋_A N ⟶ M ⊗_A N` of `derivedTensorProductTopos`, that of Tag 0FTF at
the identity. -/
def derivedTensorProductToposCounit :
    toDerivedCategory A ⋙ derivedTensorProductTopos N ⟶
      homotopyToposPullbackTensor (RingedToposHom.id X) (toposIdAlgebraHom A)
        (isUnital_toposIdAlgebraHom A) N ⋙ toDerivedCategory A' :=
  derivedPullbackTensorRingedToposCounit (RingedToposHom.id X) (toposIdAlgebraHom A)
    (isUnital_toposIdAlgebraHom A) N

/-- `derivedTensorProductTopos`, with its comparison map, is the left derived functor of
`M ↦ M ⊗_A N` followed by the localization. -/
instance isLeftDerivedFunctor_derivedTensorProductTopos :
    (derivedTensorProductTopos N).IsLeftDerivedFunctor (derivedTensorProductToposCounit N)
      (quasiIsomorphisms.{u, u, u} A) :=
  isLeftDerivedFunctor_derivedPullbackTensorRingedTopos _ _ _ N

/-- **The functor of Tag 0FTF at the identity is the derived tensor product of the ringed site**:
`derivedTensorProductTopos N ≅ derivedTensorProduct N`, the two being left derived functors of
isomorphic functors. -/
def derivedTensorProductToposIso :
    derivedTensorProductTopos N ≅ derivedTensorProduct (X := X.toRingedSite) N :=
  derivedToposPullbackTensorIsoOfIso (RingedToposHom.id X) toposDirectImageIdIso N

/-- The isomorphism `derivedTensorProductToposIso` is compatible with the comparison maps. -/
theorem derivedTensorProductToposIso_hom_fac :
    Functor.whiskerLeft (toDerivedCategory A) (derivedTensorProductToposIso N).hom ≫
        derivedTensorProductCounit (X := X.toRingedSite) N =
      derivedTensorProductToposCounit N ≫
        Functor.whiskerRight (homotopyToposPullbackTensorIdIso N).hom (toDerivedCategory A') :=
  derivedToposPullbackTensorIsoOfIso_hom_fac (RingedToposHom.id X) toposDirectImageIdIso N

end Tags

end SheafOfModules.DifferentialGradedModule

end
