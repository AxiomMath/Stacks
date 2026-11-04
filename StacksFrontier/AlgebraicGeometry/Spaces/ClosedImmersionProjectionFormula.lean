module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAnnihilation
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackTensorPower

/-!
# The projection formula for a closed immersion of algebraic spaces

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S`, let `𝒢` be an
`𝒪_Z`-module and `ℒ` an `𝒪_X`-module. The projection formula

`i_*𝒢 ⊗_{𝒪_X} ℒ ≅ i_*(𝒢 ⊗_{𝒪_Z} i^*ℒ)`

holds. The tensor product `i_*𝒢 ⊗ ℒ` is annihilated by the ideal `ℐ` cutting out `Z`, because
`i_*𝒢` is; so it is in the essential image of `i_*` (Stacks 08KS), that is, the unit
`i_*𝒢 ⊗ ℒ ⟶ i_*i^*(i_*𝒢 ⊗ ℒ)` is an isomorphism, and
`i^*(i_*𝒢 ⊗ ℒ) ≅ i^*i_*𝒢 ⊗ i^*ℒ ≅ 𝒢 ⊗ i^*ℒ` because `i^*` commutes with tensor products
(Stacks 03EL) and `i^*i_* ≅ id`.

## Main results

* `Stacks.SheafOfModules.smul_tensorSheafBifunctor_eq_zero_of_left`: a section of the structure
  sheaf annihilating the left factor annihilates the tensor product sheaf.
* `AlgebraicGeometry.Space.annihilatedByKerIdeal_sheafTensor_modulePushforward`: the ideal of a
  closed subspace annihilates `i_*𝒢 ⊗ ℒ`.
* `AlgebraicGeometry.Space.sheafTensorModulePushforwardIso`: **the projection formula**
  `i_*𝒢 ⊗ ℒ ≅ i_*(𝒢 ⊗ i^*ℒ)`.

## References

* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u w

namespace Stacks.SheafOfModules

/-- **A ring element killing the left factor kills the whole tensor product.** On a pure tensor
`m ⊗ n` the scalar can be moved onto `m`, where it already acts by zero. -/
theorem smul_tensorProduct_eq_zero_of_left {A : Type*} [CommRing A] {M N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (b : A)
    (hM : ∀ x : M, b • x = 0) (z : TensorProduct A M N) : b • z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => exact smul_zero b
  | tmul m n => rw [TensorProduct.smul_tmul', hM m, TensorProduct.zero_tmul]
  | add z₁ z₂ h₁ h₂ => rw [smul_add, h₁, h₂, add_zero]

/-- **A section of a presheaf of rings killing the sections of `M` over an object kills the
objectwise tensor product there.** -/
theorem smul_presheafTensorObj_eq_zero_of_left {C : Type u} [Category.{v} C]
    {R : Cᵒᵖ ⥤ CommRingCat.{w}}
    (M N : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat.{w} RingCat.{w})) (V : Cᵒᵖ)
    (b : (R ⋙ forget₂ CommRingCat.{w} RingCat.{w}).obj V)
    (hM : ∀ x : M.obj V, b • x = 0) (z : (PresheafOfModules.tensorObj M N).obj V) : b • z = 0 :=
  smul_tensorProduct_eq_zero_of_left b hM z

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  {Osharp : Sheaf J CommRingCat.{w}}

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **A section of the structure sheaf annihilating the left factor annihilates the tensor
product sheaf.** If `a` over `U` kills the sections of `M` over every object mapping to `U`, then
it kills every section of `M ⊗_{Osharp} N` over `U`. This is
`Stacks.SheafOfModules.smul_tensorSheafBifunctor_eq_zero` with the roles of the two factors
exchanged, and has the same proof. -/
theorem smul_tensorSheafBifunctor_eq_zero_of_left
    (M N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) (U : Cᵒᵖ)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.obj U)
    (hM : ∀ {V : Cᵒᵖ} (g : U ⟶ V) (y : M.val.obj V),
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.map g a • y = 0)
    (s : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj M).obj N).val.obj
        U) :
    a • s = 0 := by
  let η := (PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.Tensor.ringSheaf Osharp)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj)).unit.app
      (PresheafOfModules.tensorObj M.val N.val)
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero (J := J) _
    (Presheaf.imageSieve_mem J
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj).map η)
      s) ?_
  intro V g hg
  obtain ⟨z, hz⟩ := hg
  change (PresheafOfModules.tensorObj M.val N.val).obj (op V) at z
  change η.app (op V) z =
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj M).obj N).val.map g.op s
      at hz
  have hz0 : (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.map g.op a • z = 0 :=
    smul_presheafTensorObj_eq_zero_of_left (R := Osharp.obj) _ _ (op V) _ (fun y => hM g.op y) z
  rw [PresheafOfModules.map_smul, ← hz]
  exact ((η.app (op V)).hom.map_smul
    ((Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj.map g.op a) z).symm.trans
      (by rw [hz0]; exact map_zero _)

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-- **The ideal of a closed subspace annihilates `i_*𝒢 ⊗ ℒ`**: a section of the ideal kills
`i_*𝒢` over every chart, hence the tensor product
(`Stacks.SheafOfModules.smul_tensorSheafBifunctor_eq_zero_of_left`). -/
theorem annihilatedByKerIdeal_sheafTensor_modulePushforward (i : Z ⟶ X)
    (G : Modules.{u, u} B S hS Z.1 Z.2) (L : Modules.{u, u} B S hS X.1 X.2) :
    AnnihilatedByKerIdeal B S hS i
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj ((modulePushforward B S hS i).obj G)).obj
          L) := by
  have : HasWeakSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u})
  have : (smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstanceAs ((SmallEtale.topology B S hS X.1).WEqualsLocallyBijective AddCommGrpCat.{u})
  intro U a ha m
  refine Stacks.SheafOfModules.smul_tensorSheafBifunctor_eq_zero_of_left
    (smallEtaleRingedSite B S hS X.1 X.2).J _ _ U a (fun {V} g y => ?_) m
  refine annihilatedByKerIdeal_modulePushforward B S hS i G V _
    ((SheafOfModules.mem_kerIdeal (structureSharp B S hS i) V _).2 ?_) y
  rw [SheafOfModules.mem_kerIdeal, RingHom.mem_ker] at ha
  show ((structureRingSheaf B S hS X).obj.map g ≫ (structureSharp B S hS i).hom.app V).hom a = 0
  rw [(structureSharp B S hS i).hom.naturality g]
  show ((structureRingSheafDirectImage B S hS i).obj.map g).hom
    (((structureSharp B S hS i).hom.app U).hom a) = 0
  rw [ha, map_zero]

/-- **The projection formula for a closed immersion of algebraic spaces**:
`i_*𝒢 ⊗ ℒ ≅ i_*(𝒢 ⊗ i^*ℒ)` for an `𝒪_Z`-module `𝒢` and an `𝒪_X`-module `ℒ`. -/
def sheafTensorModulePushforwardIso (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i.hom)
    (G : Modules.{u, u} B S hS Z.1 Z.2) (L : Modules.{u, u} B S hS X.1 X.2) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj ((modulePushforward B S hS i).obj G)).obj
          L ≅
      (modulePushforward B S hS i).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS Z.1 Z.2).O).obj G).obj
            ((modulePullback B S hS i).obj L)) :=
  @asIso _ _ _ _ ((modulePullbackAdjunction B S hS i).unit.app
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj ((modulePushforward B S hS i).obj G)).obj L))
    ((essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit B S hS i hi _).1
      (essImage_modulePushforward_of_annihilatedByKerIdeal B S hS i hi _
        (annihilatedByKerIdeal_sheafTensor_modulePushforward B S hS i G L))) ≪≫
    (modulePushforward B S hS i).mapIso
      (modulePullbackSheafTensorIso B S hS i _ L ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedSite B S hS Z.1 Z.2).O).mapIso
            ((modulePullbackCounitIso B S hS i hi).app G)).app _)

end AlgebraicGeometry.Space

end
