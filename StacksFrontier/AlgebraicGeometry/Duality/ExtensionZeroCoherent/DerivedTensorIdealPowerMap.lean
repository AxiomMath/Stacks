module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafUnitSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DerivedTensorIdealPower
public import StacksFrontier.AlgebraicGeometry.IdealPowerMultipleComparison.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorSections
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.IdealPowerIterate
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType.Basis
public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor

/-!
# The canonical maps `𝓕^• ⊗^L 𝓘^n ⟶ 𝓘^n 𝓕^•`

Let `X` be a scheme, `𝓘 ⊆ 𝒪_X` a quasi-coherent sheaf of ideals and `𝓕^•` a complex of
`𝒪_X`-modules. Multiplication `m ⊗ a ↦ a • m` maps `𝓕^p ⊗ 𝓘^n` into the subsheaf `𝓘^n 𝓕^p`, and
these maps assemble, through the comparison of the derived tensor product of [Stacks, Tag 06YU]
with the total tensor complex, into maps `𝓕^• ⊗^L 𝓘^n ⟶ 𝓘^n 𝓕^•` in `D(𝒪_X)`, compatible with
the transitions. These are the maps whose pro-system is the subject of [Stacks, Tag 0G3N] and of
[Stacks, Tag 0G4U].

## Main definitions

* `AlgebraicGeometry.idealPowerTensorMul`: the multiplication map `𝓜 ⊗ 𝓘^n ⟶ 𝓘^n 𝓜`.
* `AlgebraicGeometry.idealPowerTensorComplexMap`: `Tot(𝓕^• ⊗ 𝓘^n[0]) ⟶ 𝓘^n 𝓕^•`.
* `AlgebraicGeometry.derivedTensorIdealPowerMap`: `𝓕^• ⊗^L 𝓘^n ⟶ 𝓘^n 𝓕^•` in `D(𝒪_X)`.
* `AlgebraicGeometry.derivedTensorIdealPowerNatTrans`: the same as a map of inverse systems.
* `AlgebraicGeometry.idealPowerResolutionMap`: its representative on a resolution `𝓟^• ⟶ 𝓕^•`.

## Main results

* `AlgebraicGeometry.top_le_sheafSubmoduleComap_idealPowerTensorMulAmbient`: the image of
  `𝓜 ⊗ 𝓘^n ⟶ 𝓜` lies in `𝓘^n 𝓜`.
* `AlgebraicGeometry.derivedTensorIdealPowerMap_eq_of_kFlat`: on a K-flat resolution the derived
  map is the class of `AlgebraicGeometry.idealPowerResolutionMap`.

## Implementation notes

The tensor product of sheaves of modules is stated at the spelling
`Stacks.DerivedTensor.RingedSite.Modules X.sheaf` of the category of `𝒪_X`-modules, which is
`X.Modules` by `rfl`; complexes entering a tensor product are retyped once, through
`Stacks.Duality.TensorComplex X`, and the abbreviations `AlgebraicGeometry.idealPowerSingle` and
`AlgebraicGeometry.idealPowerTensorComplex` record the retyped objects. Section-level facts about
the tensor product sheaf are taken at its ringed-space spelling
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, which is the same sheaf by `rfl`.

## References

* [Stacks Project, Tag 0G3N](https://stacks.math.columbia.edu/tag/0G3N)
* [Stacks Project, Tag 0G4U](https://stacks.math.columbia.edu/tag/0G4U)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.SheafOfModules.TensorStalkRingedSpace

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)

/-- **A section of `𝓘^n` times a section of `𝓜` is a section of `𝓘^n 𝓜`**, over any open. Over
an affine open `W` the sections of `𝓘^n` are `𝓘(W)^n`, so the product lies in `𝓘(W)^n 𝓜(W)`,
which is contained in the sections of `𝓘^n 𝓜`; membership in a subsheaf is local. -/
public lemma smul_mem_idealPowerMultiple (M : X.Modules) (V : (Opens X)ᵒᵖ)
    (a : (idealPowerSheaf I n).val.obj V) (m : M.val.obj V) :
    (show X.ringCatSheaf.obj.obj V from
      ((idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).ι.val.app V).hom a) • m ∈
      (idealPowerMultiple I n M).toSubmodule.obj V := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isQuasicoherent_unit
  refine (idealPowerMultiple I n M).isSheaf _ fun x hx ↦ ?_
  obtain ⟨-, ⟨W, hWaff, rfl⟩, hxW, hWle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.unop.isOpen
  refine ⟨W, homOfLE hWle, ?_, hxW⟩
  let f : V ⟶ op W := (homOfLE hWle).op
  let ι := (idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).ι
  let a' := ((idealPowerSheaf I n).val.map f).hom a
  have h1 : (ι.val.app (op W)).hom a' ∈
      (idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj (op W) := a'.2
  rw [Stacks.AlgebraicGeometry.IdealPowerComparison.obj_idealPowerMultiple I n
      (SheafOfModules.unit X.ringCatSheaf) ⟨W, hWaff⟩] at h1
  have hnat : (ι.val.app (op W)).hom a' =
      (X.ringCatSheaf.obj.map f).hom ((ι.val.app V).hom a) :=
    congrArg (fun g => g.hom a) (ι.val.naturality f)
  have key : ∀ (r : Γ(X, W)) (y : Γ(M, W)),
      r ∈ I.ideal ⟨W, hWaff⟩ ^ n • (⊤ : Submodule Γ(X, W) Γ(X, W)) →
        r • y ∈ (idealPowerMultiple I n M).toSubmodule.obj (op W) := by
    intro r y hr
    refine le_idealPowerMultiple_obj I n M ⟨W, hWaff⟩ ?_
    rw [Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id] at hr
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  show (M.val.map f).hom (_ • m) ∈ (idealPowerMultiple I n M).toSubmodule.obj (op W)
  rw [PresheafOfModules.map_smul, ← hnat]
  exact key _ _ h1

/-- `𝓜 ⊗ 𝓘^n ⟶ 𝓜`: the tensor product of `𝓜` with the inclusion `𝓘^n ⟶ 𝒪_X`, followed by the
right unitor. On local sections it is `m ⊗ a ↦ a • m`. -/
public def idealPowerTensorMulAmbient (M : X.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj (idealPowerSheaf I n) ⟶ M :=
  show ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X.toRingedSpace) CommRingCat.{u})).obj M).obj
        (idealPowerSheaf I n) ⟶ M from
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X.toRingedSpace) CommRingCat.{u}))).map
      (X := (M, idealPowerSheaf I n))
      (Y := (M, _root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace)))
      (𝟙 _, (idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).ι) ≫
    (AlgebraicGeometry.SheafOfModules.tensorSheafUnitRightIso X.toRingedSpace M).hom

/-- `idealPowerTensorMulAmbient` on the image of a pure tensor `m ⊗ a` of local sections is
`a • m`. -/
public lemma idealPowerTensorMulAmbient_app_toTensorSheafSection (M : X.Modules)
    (V : Opens X) (m : M.val.obj (op V)) (a : (idealPowerSheaf I n).val.obj (op V)) :
    ((idealPowerTensorMulAmbient I n M).val.app (op V)).hom
        (toTensorSheafSection X.toRingedSpace M (idealPowerSheaf I n) (op V)
          (m ⊗ₜ[X.presheaf.obj (op V)] a)) =
      (show X.ringCatSheaf.obj.obj (op V) from
        ((idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).ι.val.app (op V)).hom a) •
        m :=
  (congrArg ((AlgebraicGeometry.SheafOfModules.tensorSheafUnitRightIso X.toRingedSpace
      M).hom.val.app (op V)).hom (tensorSheafMap_app_toTensorSheafSection X.toRingedSpace M
        (idealPowerSheaf I n) M (SheafOfModules.unit X.ringCatSheaf) (𝟙 M)
        (idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).ι V m a)).trans
    (AlgebraicGeometry.SheafOfModules.tensorSheafUnitRightIso_hom_toTensorSheafSection
      X.toRingedSpace M (op V) _ _)

/-- The image of `𝓜 ⊗ 𝓘^n ⟶ 𝓜` lies in `𝓘^n 𝓜`. -/
public lemma top_le_sheafSubmoduleComap_idealPowerTensorMulAmbient (M : X.Modules) :
    (⊤ : ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M |>.obj
      (idealPowerSheaf I n) : X.Modules).Submodule) ≤
      sheafSubmoduleComap (idealPowerTensorMulAmbient I n M) (idealPowerMultiple I n M) := by
  intro V s _
  obtain ⟨S, hS, hsum⟩ := Stacks.SheafOfModules.TensorUnit.exists_sieve_sum_toTensorSheafSection
    X.toRingedSpace M (idealPowerSheaf I n) V.unop s
  refine (sheafSubmoduleComap (idealPowerTensorMulAmbient I n M)
    (idealPowerMultiple I n M)).isSheaf s ?_
  refine (Opens.grothendieckTopology X).superset_covering ?_ hS
  intro W k hk
  obtain ⟨N, a, b, hab⟩ := hsum k hk
  have e : ((idealPowerTensorMulAmbient I n M).val.app (op W)).hom
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M).obj
        (idealPowerSheaf I n)).val.map k.op s) =
      ∑ j, ((idealPowerTensorMulAmbient I n M).val.app (op W)).hom
        (toTensorSheafSection X.toRingedSpace M (idealPowerSheaf I n) (op W)
          (a j ⊗ₜ[X.presheaf.obj (op W)] b j)) :=
    (congrArg ((idealPowerTensorMulAmbient I n M).val.app (op W)).hom hab).trans (map_sum _ _ _)
  refine (show _ ∈ (idealPowerMultiple I n M).toSubmodule.obj (op W) from ?_)
  refine (congrArg (· ∈ (idealPowerMultiple I n M).toSubmodule.obj (op W)) e).mpr ?_
  refine Submodule.sum_mem _ fun j _ => ?_
  refine (congrArg (· ∈ (idealPowerMultiple I n M).toSubmodule.obj (op W))
    (idealPowerTensorMulAmbient_app_toTensorSheafSection I n M W (a j) (b j))).mpr ?_
  exact smul_mem_idealPowerMultiple I n M (op W) (b j) (a j)

/-- **The multiplication map `𝓜 ⊗ 𝓘^n ⟶ 𝓘^n 𝓜`**: `m ⊗ a ↦ a • m` on local sections, which lands
in the subsheaf `𝓘^n 𝓜` by `top_le_sheafSubmoduleComap_idealPowerTensorMulAmbient`. -/
public def idealPowerTensorMul (M : X.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj (idealPowerSheaf I n) ⟶
      (idealPowerMultiple I n M).toSheafOfModules :=
  sheafSubmoduleLift (idealPowerTensorMulAmbient I n M) (idealPowerMultiple I n M)
    (top_le_sheafSubmoduleComap_idealPowerTensorMulAmbient I n M)

/-- The multiplication map followed by the inclusion `𝓘^n 𝓜 ⟶ 𝓜` is `m ⊗ a ↦ a • m`. -/
public lemma idealPowerTensorMul_ι (M : X.Modules) :
    idealPowerTensorMul I n M ≫ (idealPowerMultiple I n M).ι = idealPowerTensorMulAmbient I n M :=
  sheafSubmoduleLift_comp_ι _ _ _

/-- A map `φ` of tensor sheaves equal to `f ⊗ g` sends a pure tensor of local sections to the pure
tensor of the images. -/
private theorem map_toTensorSheafSection_of_eq {M M' A B : X.Modules}
    (f : M ⟶ M') (g : A ⟶ B)
    {φ : ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj A ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M').obj B}
    (hφ : φ = ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map f).app A ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M').map g)
    (V : Opens X) (m : M.val.obj (op V)) (a : A.val.obj (op V)) :
    (φ.val.app (op V)).hom
        (toTensorSheafSection X.toRingedSpace M A (op V) (m ⊗ₜ[X.presheaf.obj (op V)] a)) =
      toTensorSheafSection X.toRingedSpace M' B (op V)
        ((f.val.app (op V)).hom m ⊗ₜ[X.presheaf.obj (op V)] (g.val.app (op V)).hom a) :=
  hφ ▸ tensorSheafMap_app_toTensorSheafSection X.toRingedSpace M A M' B f g V m a

/-- `m ⊗ a ↦ a • m` is natural in the module. -/
public lemma idealPowerTensorMulAmbient_naturality {M M' : X.Modules} (f : M ⟶ M') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map f).app (idealPowerSheaf I n) ≫
        idealPowerTensorMulAmbient I n M' = idealPowerTensorMulAmbient I n M ≫ f := by
  refine tensorSheaf_hom_ext fun V m a => ?_
  obtain ⟨V⟩ := V
  have h1' := map_toTensorSheafSection_of_eq f (𝟙 (idealPowerSheaf I n))
    ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·)
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M').map_id _).symm)) V m a
  have h2 := idealPowerTensorMulAmbient_app_toTensorSheafSection I n M' V
    ((f.val.app (op V)).hom m) a
  have h3 := idealPowerTensorMulAmbient_app_toTensorSheafSection I n M V m a
  show ((idealPowerTensorMulAmbient I n M').val.app (op V)).hom
      (((((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map f).app
        (idealPowerSheaf I n)).val.app (op V)).hom
        (toTensorSheafSection X.toRingedSpace M (idealPowerSheaf I n) (op V)
          (m ⊗ₜ[X.presheaf.obj (op V)] a))) =
    (f.val.app (op V)).hom (((idealPowerTensorMulAmbient I n M).val.app (op V)).hom
        (toTensorSheafSection X.toRingedSpace M (idealPowerSheaf I n) (op V)
          (m ⊗ₜ[X.presheaf.obj (op V)] a)))
  exact (congrArg ((idealPowerTensorMulAmbient I n M').val.app (op V)).hom h1').trans
    (h2.trans (((f.val.app (op V)).hom.map_smul _ m).symm.trans
      (congrArg (f.val.app (op V)).hom h3.symm)))

/-- `m ⊗ a ↦ a • m` is compatible with the inclusions `𝓘^{n+1} ⊆ 𝓘^n`. -/
public lemma idealPowerTensorMulAmbient_transition (M : X.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).map
        (idealPowerSheafTransition I n) ≫ idealPowerTensorMulAmbient I n M =
      idealPowerTensorMulAmbient I (n + 1) M := by
  refine tensorSheaf_hom_ext fun V m a => ?_
  obtain ⟨V⟩ := V
  have h1' := map_toTensorSheafSection_of_eq (𝟙 M) (idealPowerSheafTransition I n)
    ((Category.id_comp _).symm.trans (congrArg (· ≫ _)
      (congrArg (fun t => NatTrans.app t (idealPowerSheaf I (n + 1)))
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map_id M)).symm)) V m a
  have h2 := idealPowerTensorMulAmbient_app_toTensorSheafSection I n M V m
    (((idealPowerSheafTransition I n).val.app (op V)).hom a)
  have h3 := idealPowerTensorMulAmbient_app_toTensorSheafSection I (n + 1) M V m a
  have h4 : ((idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).ι.val.app (op V)).hom
      (((idealPowerSheafTransition I n).val.app (op V)).hom a) =
      ((idealPowerMultiple I (n + 1) (SheafOfModules.unit X.ringCatSheaf)).ι.val.app (op V)).hom
        a :=
    congrArg (fun g => (g.val.app (op V)).hom a)
      (idealPowerMultipleMap_comp_ι I (SheafOfModules.unit X.ringCatSheaf) (Nat.le_succ n))
  show ((idealPowerTensorMulAmbient I n M).val.app (op V)).hom
      (((((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).map
        (idealPowerSheafTransition I n)).val.app (op V)).hom
          (toTensorSheafSection X.toRingedSpace M (idealPowerSheaf I (n + 1)) (op V)
            (m ⊗ₜ[X.presheaf.obj (op V)] a))) = _
  refine (congrArg ((idealPowerTensorMulAmbient I n M).val.app (op V)).hom h1').trans
    (h2.trans ?_)
  refine Eq.trans ?_ h3.symm
  simp only [h4]

/-- `μ` commutes with the inclusions `𝓘^{n+1} ⊆ 𝓘^n`: the square with `𝓘^{n+1}𝓜 ⊆ 𝓘^n 𝓜`. -/
public lemma idealPowerTensorMul_transition (M : X.Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).map
        (idealPowerSheafTransition I n) ≫ idealPowerTensorMul I n M =
      idealPowerTensorMul I (n + 1) M ≫ idealPowerMultipleMap I M (Nat.le_succ n) :=
  cancel_sheafSubmodule_ι (idealPowerMultiple I n M) _ _ <| (Category.assoc _ _ _).trans
    ((congrArg (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).map
        (idealPowerSheafTransition I n) ≫ ·) (idealPowerTensorMul_ι I n M)).trans
      ((idealPowerTensorMulAmbient_transition I n M).trans
        ((idealPowerTensorMul_ι I (n + 1) M).symm.trans
          ((congrArg (idealPowerTensorMul I (n + 1) M ≫ ·)
            (idealPowerMultipleMap_comp_ι I M (Nat.le_succ n))).symm.trans
            (Category.assoc _ _ _).symm))))

/-- **The multiplication maps on the terms of a complex** `𝓕^p ⊗ 𝓘^n ⟶ 𝓘^n 𝓕^p` form a map from
the termwise tensor product complex to the ideal-power subcomplex `𝓘^n 𝓕^•`. -/
public def idealPowerRowMap (F : CochainComplex X.Modules ℤ) :
    CochainComplex.KFlatBifunctor.rowComplex (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
        (show Stacks.Duality.TensorComplex X from F) (idealPowerSheaf I n) ⟶
      (idealPowerComplexSystem I F).complex n where
  f p := idealPowerTensorMul I n (F.X p)
  comm' p q _ := by
    apply cancel_sheafSubmodule_ι (idealPowerMultiple I n (F.X q))
    refine Eq.symm ?_
    exact (Category.assoc _ _ _).trans
      ((congrArg (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map (F.d p q)).app
          (idealPowerSheaf I n) ≫ ·) (idealPowerTensorMul_ι I n (F.X q))).trans
        ((idealPowerTensorMulAmbient_naturality I n (F.d p q)).trans
          ((congrArg (· ≫ F.d p q) (idealPowerTensorMul_ι I n (F.X p))).symm.trans
            ((Category.assoc _ _ _).trans
              ((congrArg (idealPowerTensorMul I n (F.X p) ≫ ·)
                (((idealPowerComplexSystem I F).inclusion n).comm p q)).trans
                (Category.assoc _ _ _).symm)))))

/-- The termwise multiplication maps followed by the inclusion `𝓘^n 𝓕^• ⟶ 𝓕^•`. -/
public lemma idealPowerRowMap_inclusion_f (F : CochainComplex X.Modules ℤ) (p : ℤ) :
    (idealPowerRowMap I n F).f p ≫ ((idealPowerComplexSystem I F).inclusion n).f p =
      idealPowerTensorMulAmbient I n (F.X p) :=
  idealPowerTensorMul_ι I n (F.X p)

/-- The termwise multiplication maps commute with the transitions. -/
public lemma idealPowerRowMap_transition (F : CochainComplex X.Modules ℤ) :
    CochainComplex.KFlatBifunctor.rowComplexMapRight
        (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
        (show Stacks.Duality.TensorComplex X from F) (idealPowerSheafTransition I n) ≫
        idealPowerRowMap I n F =
      idealPowerRowMap I (n + 1) F ≫ (idealPowerComplexSystem I F).transition n := by
  ext p : 1
  exact idealPowerTensorMul_transition I n (F.X p)

/-- The complex `𝓘^n 𝓕^•` of `AlgebraicGeometry.idealPowerComplexSystem`, retyped at the spelling
`Stacks.Duality.TensorComplex X` of complexes of `𝒪_X`-modules at which the tensor product of
sheaves of modules is stated (the two spellings are equal by `rfl`; only instance search and
unification at reducible transparency tell them apart). -/
public abbrev idealPowerTensorComplex (F : CochainComplex X.Modules ℤ) :
    Stacks.Duality.TensorComplex X :=
  (idealPowerComplexSystem I F).complex n

/-- The transition `𝓘^{n+1} 𝓕^• ⟶ 𝓘^n 𝓕^•`, at the tensor spelling. -/
public abbrev idealPowerTensorComplexTransition (F : CochainComplex X.Modules ℤ) :
    idealPowerTensorComplex I (n + 1) F ⟶ idealPowerTensorComplex I n F :=
  (idealPowerComplexSystem I F).transition n

/-- The ideal power `𝓘^n` placed in degree zero, at the tensor spelling. -/
public abbrev idealPowerSingle : Stacks.Duality.TensorComplex X :=
  (HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules X.sheaf)
    (ComplexShape.up ℤ) 0).obj (idealPowerSheaf I n)

/-- The inclusion `𝓘^{n+1}[0] ⟶ 𝓘^n[0]`, at the tensor spelling. -/
public abbrev idealPowerSingleTransition : idealPowerSingle I (n + 1) ⟶ idealPowerSingle I n :=
  (HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules X.sheaf)
    (ComplexShape.up ℤ) 0).map (idealPowerSheafTransition I n)

/-- **The multiplication map of complexes** `Tot(𝓕^• ⊗ 𝓘^n[0]) ⟶ 𝓘^n 𝓕^•`: the total complex
against a module in degree zero is the termwise complex (`totalSingleIso`), followed by the
termwise multiplication maps. -/
public def idealPowerTensorComplexMap (F : CochainComplex X.Modules ℤ) :
    Stacks.Duality.totalTensorComplex (show Stacks.Duality.TensorComplex X from F)
        (idealPowerSingle I n) ⟶ idealPowerTensorComplex I n F :=
  (CochainComplex.KFlatBifunctor.totalSingleIso (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
      (show Stacks.Duality.TensorComplex X from F) (idealPowerSheaf I n)).hom ≫
    idealPowerRowMap I n F

/-- The multiplication maps of complexes commute with the transitions. -/
public lemma idealPowerTensorComplexMap_transition (F : CochainComplex X.Modules ℤ) :
    HomologicalComplex.mapBifunctorMap (𝟙 (show Stacks.Duality.TensorComplex X from F))
        (idealPowerSingleTransition I n) (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
        (ComplexShape.up ℤ) ≫ idealPowerTensorComplexMap I n F =
      idealPowerTensorComplexMap I (n + 1) F ≫ idealPowerTensorComplexTransition I n F := by
  have h1 := CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality_right
    (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
    (show Stacks.Duality.TensorComplex X from F) (idealPowerSheafTransition I n)
  have h2 := idealPowerRowMap_transition I n F
  let e₀ := (CochainComplex.KFlatBifunctor.totalSingleIso
    (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
    (show Stacks.Duality.TensorComplex X from F) (idealPowerSheaf I n)).hom
  let e₁ := (CochainComplex.KFlatBifunctor.totalSingleIso
    (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
    (show Stacks.Duality.TensorComplex X from F) (idealPowerSheaf I (n + 1))).hom
  calc _ = (HomologicalComplex.mapBifunctorMap (𝟙 (show Stacks.Duality.TensorComplex X from F))
          (idealPowerSingleTransition I n) (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
          (ComplexShape.up ℤ) ≫ e₀) ≫ idealPowerRowMap I n F := (Category.assoc _ _ _).symm
    _ = (e₁ ≫ CochainComplex.KFlatBifunctor.rowComplexMapRight
          (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
          (show Stacks.Duality.TensorComplex X from F) (idealPowerSheafTransition I n)) ≫
          idealPowerRowMap I n F := congrArg (fun x => x ≫ idealPowerRowMap I n F) h1
    _ = e₁ ≫ (CochainComplex.KFlatBifunctor.rowComplexMapRight
          (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
          (show Stacks.Duality.TensorComplex X from F) (idealPowerSheafTransition I n) ≫
          idealPowerRowMap I n F) := Category.assoc _ _ _
    _ = e₁ ≫ (idealPowerRowMap I (n + 1) F ≫ (idealPowerComplexSystem I F).transition n) :=
          congrArg (fun x => e₁ ≫ x) h2
    _ = _ := (Category.assoc _ _ _).symm

/-- **The canonical map `𝓕^• ⊗^L 𝓘^n ⟶ 𝓘^n 𝓕^•`** in `D(𝒪_X)`: the comparison `toTensor` of the
derived tensor product of [Stacks, Tag 06YU] with the total tensor complex, followed by the
multiplication maps of complexes. -/
public def derivedTensorIdealPowerMap (F : CochainComplex X.Modules ℤ) :
    (derivedTensorIdealPowerSystem I (DerivedCategory.Q.obj F)).obj (op n) ⟶
      DerivedCategory.Q.obj (idealPowerTensorComplex I n F) :=
  ((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor.obj
      (DerivedCategory.Q.obj F)).map
      ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).hom.app (idealPowerSheaf I n)) ≫
    (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).toTensor
      (show Stacks.Duality.TensorComplex X from F) (idealPowerSingle I n) ≫
    DerivedCategory.Q.map (idealPowerTensorComplexMap I n F)

/-- The canonical maps `𝓕^• ⊗^L 𝓘^n ⟶ 𝓘^n 𝓕^•` commute with the transitions. -/
public lemma derivedTensorIdealPowerMap_naturality (F : CochainComplex X.Modules ℤ) :
    (derivedTensorIdealPowerSystem I (DerivedCategory.Q.obj F)).map (homOfLE (Nat.le_succ n)).op ≫
        derivedTensorIdealPowerMap I n F =
      derivedTensorIdealPowerMap I (n + 1) F ≫
        DerivedCategory.Q.map (idealPowerTensorComplexTransition I n F) := by
  let T := Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace
  let G := T.tensor.obj (DerivedCategory.Q.obj F)
  let F' : Stacks.Duality.TensorComplex X := F
  let s₀ := (DerivedCategory.singleFunctorIsoCompQ X.Modules 0).hom.app (idealPowerSheaf I n)
  let s₁ := (DerivedCategory.singleFunctorIsoCompQ X.Modules 0).hom.app (idealPowerSheaf I (n + 1))
  have hsingle : (DerivedCategory.singleFunctor X.Modules 0).map (idealPowerSheafTransition I n) ≫
      s₀ = s₁ ≫ DerivedCategory.Q.map (idealPowerSingleTransition I n) :=
    (DerivedCategory.singleFunctorIsoCompQ X.Modules 0).hom.naturality
      (idealPowerSheafTransition I n)
  have htt : G.map (DerivedCategory.Q.map (idealPowerSingleTransition I n)) ≫
      T.toTensor F' (idealPowerSingle I n) = T.toTensor F' (idealPowerSingle I (n + 1)) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 F')
          (idealPowerSingleTransition I n) (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
          (ComplexShape.up ℤ)) := by
    simpa only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] using
      T.toTensor_naturality (𝟙 F') (idealPowerSingleTransition I n)
  have hc : DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 F')
        (idealPowerSingleTransition I n) (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
        (ComplexShape.up ℤ)) ≫ DerivedCategory.Q.map (idealPowerTensorComplexMap I n F) =
      DerivedCategory.Q.map (idealPowerTensorComplexMap I (n + 1) F) ≫
        DerivedCategory.Q.map (idealPowerTensorComplexTransition I n F) :=
    (DerivedCategory.Q.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Q.map (idealPowerTensorComplexMap_transition I n F)).trans
        (DerivedCategory.Q.map_comp _ _))
  have hmap : (derivedTensorIdealPowerSystem I (DerivedCategory.Q.obj F)).map
      (homOfLE (Nat.le_succ n)).op =
      G.map ((DerivedCategory.singleFunctor X.Modules 0).map (idealPowerSheafTransition I n)) :=
    Functor.ofOpSequence_map_homOfLE_succ _ n
  rw [hmap]
  show G.map ((DerivedCategory.singleFunctor X.Modules 0).map (idealPowerSheafTransition I n)) ≫
      G.map s₀ ≫ T.toTensor F' (idealPowerSingle I n) ≫
        DerivedCategory.Q.map (idealPowerTensorComplexMap I n F) =
    (G.map s₁ ≫ T.toTensor F' (idealPowerSingle I (n + 1)) ≫
        DerivedCategory.Q.map (idealPowerTensorComplexMap I (n + 1) F)) ≫
      DerivedCategory.Q.map (idealPowerTensorComplexTransition I n F)
  let a := (DerivedCategory.singleFunctor X.Modules 0).map (idealPowerSheafTransition I n)
  let g := DerivedCategory.Q.map (idealPowerSingleTransition I n)
  let τ₀ := T.toTensor F' (idealPowerSingle I n)
  let τ₁ := T.toTensor F' (idealPowerSingle I (n + 1))
  let c₀ := DerivedCategory.Q.map (idealPowerTensorComplexMap I n F)
  let c₁ := DerivedCategory.Q.map (idealPowerTensorComplexMap I (n + 1) F)
  let mb := DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 F')
    (idealPowerSingleTransition I n) (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
    (ComplexShape.up ℤ))
  let tr := DerivedCategory.Q.map (idealPowerTensorComplexTransition I n F)
  calc G.map a ≫ G.map s₀ ≫ τ₀ ≫ c₀ = G.map (a ≫ s₀) ≫ τ₀ ≫ c₀ :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ τ₀ ≫ c₀) (G.map_comp a s₀).symm)
    _ = G.map (s₁ ≫ g) ≫ τ₀ ≫ c₀ := congrArg (fun x => G.map x ≫ τ₀ ≫ c₀) hsingle
    _ = G.map s₁ ≫ (G.map g ≫ τ₀) ≫ c₀ :=
        (congrArg (· ≫ τ₀ ≫ c₀) (G.map_comp s₁ g)).trans
          ((Category.assoc _ _ _).trans (congrArg (G.map s₁ ≫ ·) (Category.assoc _ _ _).symm))
    _ = G.map s₁ ≫ (τ₁ ≫ mb) ≫ c₀ := congrArg (fun x => G.map s₁ ≫ x ≫ c₀) htt
    _ = G.map s₁ ≫ τ₁ ≫ (mb ≫ c₀) := congrArg (G.map s₁ ≫ ·) (Category.assoc _ _ _)
    _ = G.map s₁ ≫ τ₁ ≫ (c₁ ≫ tr) := congrArg (fun x => G.map s₁ ≫ τ₁ ≫ x) hc
    _ = (G.map s₁ ≫ τ₁ ≫ c₁) ≫ tr :=
        (congrArg (G.map s₁ ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm

/-- **The canonical comparison `(𝓕^• ⊗^L 𝓘^n)_n ⟶ (𝓘^n 𝓕^•)_n`** of inverse systems in `D(𝒪_X)`,
whose components are `AlgebraicGeometry.derivedTensorIdealPowerMap`. Its target is the system of
the Deligne system `(𝓘^n 𝓕^•)` of `AlgebraicGeometry.DeligneTriangle.deligneSystemOfComplex`. -/
public def derivedTensorIdealPowerNatTrans (F : CochainComplex X.Modules ℤ) :
    derivedTensorIdealPowerSystem I (DerivedCategory.Q.obj F) ⟶
      Functor.ofOpSequence (idealPowerComplexSystem I F).transition ⋙ DerivedCategory.Q :=
  NatTrans.ofOpSequence (fun n => derivedTensorIdealPowerMap I n F) fun n =>
    (derivedTensorIdealPowerMap_naturality I n F).trans
      (congrArg (derivedTensorIdealPowerMap I (n + 1) F ≫ ·)
        (congrArg DerivedCategory.Q.map
          (Functor.ofOpSequence_map_homOfLE_succ (idealPowerComplexSystem I F).transition n).symm))

/-- The components of `AlgebraicGeometry.derivedTensorIdealPowerNatTrans`. -/
public lemma derivedTensorIdealPowerNatTrans_app (F : CochainComplex X.Modules ℤ) (n : ℕ) :
    (derivedTensorIdealPowerNatTrans I F).app (op n) = derivedTensorIdealPowerMap I n F :=
  NatTrans.ofOpSequence_app _ _ (op n)

/-- **The canonical map computed from a K-flat resolution.** For a chain map `π : 𝓟^• ⟶ 𝓕^•`
from a K-flat complex, the canonical map `𝓕^• ⊗^L 𝓘^n ⟶ 𝓘^n 𝓕^•` precomposed with
`π ⊗^L 𝓘^n` is, through the identification `𝓟^• ⊗^L 𝓘^n ≅ Tot(𝓟^• ⊗ 𝓘^n[0])` of the derived
tensor product with a K-flat left factor, the class of the map of complexes
`Tot(𝓟^• ⊗ 𝓘^n[0]) ⟶ Tot(𝓕^• ⊗ 𝓘^n[0]) ⟶ 𝓘^n 𝓕^•`. -/
public lemma derivedTensorIdealPowerMap_eq_of_kFlat (F : CochainComplex X.Modules ℤ)
    (P : Stacks.Duality.TensorComplex X) (hP : Stacks.Duality.KFlatComplex P)
    (π : P ⟶ (show Stacks.Duality.TensorComplex X from F)) :
    ((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor.map
        (DerivedCategory.Q.map π)).app
        ((DerivedCategory.singleFunctor X.Modules 0).obj (idealPowerSheaf I n)) ≫
        derivedTensorIdealPowerMap I n F =
      ((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor.obj
          (DerivedCategory.Q.obj P)).map
          ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).hom.app (idealPowerSheaf I n)) ≫
        ((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).comparisonLeft P
          (idealPowerSingle I n) hP).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap π (𝟙 (idealPowerSingle I n))
            (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ) ≫
          idealPowerTensorComplexMap I n F) := by
  let T := Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace
  let s := (DerivedCategory.singleFunctorIsoCompQ X.Modules 0).hom.app (idealPowerSheaf I n)
  have hnat := (T.tensor.map (DerivedCategory.Q.map π)).naturality s
  have htt : (T.tensor.map (DerivedCategory.Q.map π)).app
      (DerivedCategory.Q.obj (idealPowerSingle I n)) ≫
      T.toTensor (show Stacks.Duality.TensorComplex X from F) (idealPowerSingle I n) =
      T.toTensor P (idealPowerSingle I n) ≫ DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap π (𝟙 (idealPowerSingle I n))
          (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)) := by
    simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using
      T.toTensor_naturality π (𝟙 (idealPowerSingle I n))
  have hcomp := T.toTensor_eq_comparisonLeft P (idealPowerSingle I n) hP
  let α := T.tensor.map (DerivedCategory.Q.map π)
  let τF := T.toTensor (show Stacks.Duality.TensorComplex X from F) (idealPowerSingle I n)
  let τP := T.toTensor P (idealPowerSingle I n)
  let c := DerivedCategory.Q.map (idealPowerTensorComplexMap I n F)
  let mb := DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap π
    (𝟙 (idealPowerSingle I n)) (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
    (ComplexShape.up ℤ))
  let GF := T.tensor.obj (DerivedCategory.Q.obj (show Stacks.Duality.TensorComplex X from F))
  let GP := T.tensor.obj (DerivedCategory.Q.obj P)
  show α.app _ ≫ GF.map s ≫ τF ≫ c = _
  calc α.app _ ≫ GF.map s ≫ τF ≫ c = (GP.map s ≫ α.app _) ≫ τF ≫ c :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ τF ≫ c) hnat.symm)
    _ = GP.map s ≫ (τP ≫ mb) ≫ c :=
        (Category.assoc _ _ _).trans (congrArg (GP.map s ≫ ·)
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ c) htt)))
    _ = _ := congrArg (GP.map s ≫ ·) ((Category.assoc _ _ _).trans
          ((congrArg (· ≫ mb ≫ c) hcomp).trans
            (congrArg (_ ≫ ·) (DerivedCategory.Q.map_comp _ _).symm)))

/-- **The comparison map computed on a resolution**: for a chain map `π : 𝓟^• ⟶ 𝓕^•`, the map of
complexes `Tot(𝓟^• ⊗ 𝓘^n[0]) ⟶ Tot(𝓕^• ⊗ 𝓘^n[0]) ⟶ 𝓘^n 𝓕^•`. When `𝓟^•` is K-flat its class in
`D(𝒪_X)` is the canonical map `𝓕^• ⊗^L 𝓘^n ⟶ 𝓘^n 𝓕^•`
(`AlgebraicGeometry.derivedTensorIdealPowerMap_eq_of_kFlat`). -/
public def idealPowerResolutionMap {F : CochainComplex X.Modules ℤ}
    {P : Stacks.Duality.TensorComplex X} (π : P ⟶ (show Stacks.Duality.TensorComplex X from F)) :
    Stacks.Duality.totalTensorComplex P (idealPowerSingle I n) ⟶ idealPowerTensorComplex I n F :=
  HomologicalComplex.mapBifunctorMap π (𝟙 (idealPowerSingle I n))
      (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ) ≫
    idealPowerTensorComplexMap I n F

/-- The comparison maps computed on a resolution commute with the transitions. -/
public lemma idealPowerResolutionMap_transition {F : CochainComplex X.Modules ℤ}
    {P : Stacks.Duality.TensorComplex X} (π : P ⟶ (show Stacks.Duality.TensorComplex X from F)) :
    HomologicalComplex.mapBifunctorMap (𝟙 P) (idealPowerSingleTransition I n)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ) ≫
        idealPowerResolutionMap I n π =
      idealPowerResolutionMap I (n + 1) π ≫ idealPowerTensorComplexTransition I n F := by
  let tP := HomologicalComplex.mapBifunctorMap (𝟙 P) (idealPowerSingleTransition I n)
    (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)
  let tF := HomologicalComplex.mapBifunctorMap
    (𝟙 (show Stacks.Duality.TensorComplex X from F)) (idealPowerSingleTransition I n)
    (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)
  let p₀ := HomologicalComplex.mapBifunctorMap π (𝟙 (idealPowerSingle I n))
    (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)
  let p₁ := HomologicalComplex.mapBifunctorMap π (𝟙 (idealPowerSingle I (n + 1)))
    (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)
  have hsq : tP ≫ p₀ = p₁ ≫ tF :=
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).map π).naturality
      (idealPowerSingleTransition I n)
  calc tP ≫ p₀ ≫ idealPowerTensorComplexMap I n F
      = (tP ≫ p₀) ≫ idealPowerTensorComplexMap I n F := (Category.assoc _ _ _).symm
    _ = (p₁ ≫ tF) ≫ idealPowerTensorComplexMap I n F :=
        congrArg (· ≫ idealPowerTensorComplexMap I n F) hsq
    _ = p₁ ≫ (tF ≫ idealPowerTensorComplexMap I n F) := Category.assoc _ _ _
    _ = p₁ ≫ (idealPowerTensorComplexMap I (n + 1) F ≫ idealPowerTensorComplexTransition I n F) :=
        congrArg (p₁ ≫ ·) (idealPowerTensorComplexMap_transition I n F)
    _ = _ := (Category.assoc _ _ _).symm

/-- The inverse system of complexes `(Tot(𝓟^• ⊗ 𝓘^n[0]))_n`, along the inclusions
`𝓘^{n+1} ⊆ 𝓘^n`. -/
public def idealPowerResolutionSystem (P : Stacks.Duality.TensorComplex X) :
    ℕᵒᵖ ⥤ Stacks.Duality.TensorComplex X :=
  Functor.ofOpSequence (X := fun n => Stacks.Duality.totalTensorComplex P (idealPowerSingle I n))
    fun n => HomologicalComplex.mapBifunctorMap (𝟙 P) (idealPowerSingleTransition I n)
      (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)

/-- **The comparison maps on a resolution, as a map of inverse systems of complexes**
`(Tot(𝓟^• ⊗ 𝓘^n[0]))_n ⟶ (𝓘^n 𝓕^•)_n`, with components
`AlgebraicGeometry.idealPowerResolutionMap`. -/
public def idealPowerResolutionNatTrans {F : CochainComplex X.Modules ℤ}
    {P : Stacks.Duality.TensorComplex X} (π : P ⟶ (show Stacks.Duality.TensorComplex X from F)) :
    idealPowerResolutionSystem I P ⟶
      Functor.ofOpSequence (fun n => idealPowerTensorComplexTransition I n F) :=
  NatTrans.ofOpSequence (fun n => idealPowerResolutionMap I n π) fun n =>
    (congrArg (· ≫ idealPowerResolutionMap I n π)
        (Functor.ofOpSequence_map_homOfLE_succ _ n)).trans
      ((idealPowerResolutionMap_transition I n π).trans
        (congrArg (idealPowerResolutionMap I (n + 1) π ≫ ·)
          (Functor.ofOpSequence_map_homOfLE_succ _ n).symm))

/-- The components of `AlgebraicGeometry.idealPowerResolutionNatTrans`. -/
public lemma idealPowerResolutionNatTrans_app {F : CochainComplex X.Modules ℤ}
    {P : Stacks.Duality.TensorComplex X} (π : P ⟶ (show Stacks.Duality.TensorComplex X from F))
    (n : ℕ) : (idealPowerResolutionNatTrans I π).app (op n) = idealPowerResolutionMap I n π :=
  NatTrans.ofOpSequence_app _ _ (op n)

end AlgebraicGeometry

end
