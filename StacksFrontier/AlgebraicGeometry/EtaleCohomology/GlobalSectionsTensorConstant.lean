module

public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksFrontier.AlgebraicGeometry.EilenbergWatts.Devissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DirectSumsOfEtaleCohomology

/-!
# Pulling a flat constant coefficient group out of étale cohomology

Let `X` be a quasi-compact and quasi-separated scheme, let `ℰ` be an abelian sheaf on the small
étale site of `X` and let `M` be a flat `ℤ`-module. Writing `M̲` for the constant sheaf attached
to `M`, the canonical map

> `H^p(X, ℰ) ⊗_ℤ M ⟶ H^p(X, ℰ ⊗_ℤ M̲)`

is an isomorphism. This is the content of steps 6 to 8 of the proof of [Stacks, Tag 0F0E], the
case of that statement in which `E ∈ D⁺(X_étale)` is a single abelian sheaf placed in one degree
and `K ∈ D⁺(ℤ)` is a single flat `ℤ`-module placed in one degree.

The argument of the source is: write `M` as a filtered colimit of free `ℤ`-modules of finite
rank, which is Lazard's theorem [Stacks, Tag 058G]; cohomology on a quasi-compact and
quasi-separated scheme commutes with filtered colimits of abelian sheaves, [Stacks, Tag 09YQ] —
available here in the form of its small-étale case [Stacks, Tag 03Q5] — so the claim reduces to
free `ℤ`-modules of finite rank, where it is additivity of cohomology over a finite direct sum.

## Main definitions

* `Stacks.EtaleCohomology.TensorConstant.tensorConstLeft` — the functor `M ↦ A ⊗_ℤ M` on abelian
  groups, with its right adjoint `homConstLeft` and the resulting tensor-hom adjunction, and
  `tensorBif` — the tensor product of abelian groups as a bifunctor.
* `Stacks.EtaleCohomology.TensorConstant.tensorComp` — for an additive endofunctor `F` of abelian
  groups, the canonical comparison `F(ℤ) ⊗_ℤ M ⟶ F(M)`, natural in `M`.
* `Stacks.EtaleCohomology.TensorConstant.tensorConstSheaf` — the functor `M ↦ 𝓕 ⊗_ℤ M̲` carrying
  an abelian group to the tensor product of a fixed abelian sheaf with the constant sheaf on it.
* `Stacks.EtaleCohomology.etaleTensorConstH` — the composite `M ↦ H^p(X, ℰ ⊗_ℤ M̲)`, and
  `Stacks.EtaleCohomology.etaleTensorConstComparison` — the canonical comparison
  `H^p(X, ℰ) ⊗_ℤ M ⟶ H^p(X, ℰ ⊗_ℤ M̲)`.

## Main results

* `Stacks.EtaleCohomology.TensorConstant.isIso_tensorComp_app_of_free_finite` — the comparison of
  an additive endofunctor with tensoring by its value at `ℤ` is invertible at a free `ℤ`-module
  of finite rank. This is the additivity step.
* `Stacks.EtaleCohomology.TensorConstant.fgCoconeIsColimit` — an abelian group is the filtered
  colimit of its finitely generated subgroups.
* `Stacks.EtaleCohomology.TensorConstant.isIso_tensorComp_app_of_flat` — the comparison is
  invertible at a flat `ℤ`-module, for an additive endofunctor preserving the relevant filtered
  colimits. This is the coefficient-free form of steps 7 and 8.
* `Stacks.EtaleCohomology.isIso_etaleTensorConstComparison_app` — **the result**: over a
  quasi-compact and quasi-separated scheme the canonical map
  `H^p(X, ℰ) ⊗_ℤ M ⟶ H^p(X, ℰ ⊗_ℤ M̲)` is an isomorphism for every abelian sheaf `ℰ` and every
  flat `ℤ`-module `M`.

## Implementation notes

*Relation to the full statement.* The source states its lemma for arbitrary
`E ∈ D⁺(X_étale)` and `K ∈ D⁺(ℤ)` and reduces it, through stupid truncations, to the case of a
single sheaf and a single flat module, which is the case treated in this file, for abelian
sheaves. The full statement, for the derived tensor product of sheaves of modules over the
lifted integers and the derived constant sheaf on complexes, is
`nonempty_derivedSections_tensor_derivedConstantSheaf_iso` (namespace
`Stacks.EtaleCohomology.DerivedTensorConstant`) in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedGlobalSectionsTensorConstant`.

*Flatness rather than Lazard's theorem.* The source invokes Lazard's theorem to present a flat
module as a filtered colimit of free modules of finite rank. Over `ℤ` the presentation is
available directly and at every universe: a flat `ℤ`-module is torsion free, its finitely
generated subgroups are therefore free of finite rank, and they form a filtered system with
colimit the whole module (`fgCoconeIsColimit`). Lazard's theorem in the repository,
`flat_iff_directLimit_free_finite`, is stated for a ring and a module in a common universe, so
over `ℤ` it would confine the coefficient module to `Type 0`, which the étale statement cannot
afford: its coefficients must live in the universe of the sheaves.

*The shape of the comparison map.* For any additive endofunctor `F` of abelian groups there is a
canonical map `F(ℤ) ⊗_ℤ M ⟶ F(M)`, natural in `M`, sending `a ⊗ m` to `F(m̂)(a)` where
`m̂ : ℤ ⟶ M` is the morphism carrying the generator to `m`. Taking `F` to be
`M ↦ H^p(X, ℰ ⊗_ℤ M̲)` and identifying `F(ℤ)` with `H^p(X, ℰ)` — the identification is
`etaleTensorConstHObjIntIso`, which rests on `ℰ ⊗_ℤ ℤ̲ ≅ ℰ` — produces the map of the statement.
Proving the result for this map, rather than asserting the existence of some isomorphism, is
what makes it usable: it is invertibility of a map constructed before the theorem is stated.

*Relation to Eilenberg–Watts.* `Stacks.EilenbergWatts.isIso_wattsMap` is the same comparison
map proved invertible for **every** module, under the hypothesis that the functor preserves
**every** colimit. It does not apply here, in either of two independent ways. Étale cohomology
in positive degree is not right exact, so it does not preserve cokernels and the hypothesis
fails; and that development lives in `ModuleCat.{u} R` with `R : Type u`, which over `R = ℤ`
confines the modules to `Type 0`, whereas the coefficients here must live in the universe of the
sheaves. What is proved below is the trade: only filtered colimits are required, and in exchange
the module is required to be flat. The one piece that is shared is the transfer principle
`Stacks.EilenbergWatts.isIso_app_of_isColimit`, which is imported rather than re-proved.

*Why the two sides both commute with filtered colimits.* The left-hand side does because
`A ⊗_ℤ -` is a left adjoint, `tensorConstLeftAdj`. The right-hand side does because
`M ↦ ℰ ⊗_ℤ M̲` is computed by tensoring sections pointwise and then sheafifying, both
colimit-preserving, and because of [Stacks, Tag 03Q5] in the form
`Stacks.EtaleCohomology.preservesColimitsOfShape_rightDerived_Γ_smallEtale`.

*The tensor product with a constant sheaf.* `ℰ ⊗_ℤ M̲` is `tensorConstSheaf`: the sheafification
of the presheaf `U ↦ ℰ(U) ⊗_ℤ M`. This is the tensor product of abelian sheaves applied to `ℰ`
and the constant sheaf on `M`: the tensor product of sheaves is the sheafification of the
presheaf tensor product, and the presheaf tensor product of `ℰ` with the constant presheaf on `M`
is `U ↦ ℰ(U) ⊗_ℤ M`.

*Coefficients and universes.* Abelian sheaves have values in `AddCommGrpCat.{max (u + 1) v}` for
a scheme universe `u` and arbitrary `v`, matching the rest of the étale abelian development, and
the coefficient module `M` is an object of that same category. The index category of the
filtered colimit is the poset of finitely generated subgroups of `M`, which lives in the same
universe, so [Stacks, Tag 03Q5] applies to it.

## References

* [Stacks Project, Tag 0F0E](https://stacks.math.columbia.edu/tag/0F0E)
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
* [Stacks Project, Tag 058G](https://stacks.math.columbia.edu/tag/058G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Submodule TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v₁ u₁ v u w

namespace Stacks.EtaleCohomology.TensorConstant

/-! ### Tensoring abelian groups by a fixed abelian group -/

/-- Tensoring on the left by a fixed abelian group, over `ℤ`: the functor `M ↦ A ⊗_ℤ M`. -/
noncomputable def tensorConstLeft (A : Type w) [AddCommGroup A] :
    AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} where
  obj M := AddCommGrpCat.of (A ⊗[ℤ] M)
  map {M N} f := AddCommGrpCat.ofHom
    (LinearMap.lTensor A (AddMonoidHom.toIntLinearMap f.hom)).toAddMonoidHom
  map_id M := by ext x; induction x using TensorProduct.inductionOn <;> simp_all
  map_comp f g := by ext x; induction x using TensorProduct.inductionOn <;> simp_all

/-- The right adjoint of `tensorConstLeft A`: the functor `T ↦ Hom_ℤ(A, T)`. -/
noncomputable def homConstLeft (A : Type w) [AddCommGroup A] :
    AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} where
  obj T := AddCommGrpCat.of (A →ₗ[ℤ] T)
  map {T T'} f := AddCommGrpCat.ofHom
    (LinearMap.llcomp ℤ A T T' (AddMonoidHom.toIntLinearMap f.hom)).toAddMonoidHom

variable {A : Type w} [AddCommGroup A] {M T : AddCommGrpCat.{w}}

/-- The forward direction of the tensor-hom adjunction: a map out of `A ⊗_ℤ M` read as a map
from `M` into `Hom_ℤ(A, T)`. -/
noncomputable def hFwd (f : (tensorConstLeft A).obj M ⟶ T) : M ⟶ (homConstLeft A).obj T :=
  AddCommGrpCat.ofHom
    ((TensorProduct.curry (AddMonoidHom.toIntLinearMap f.hom)).flip).toAddMonoidHom

/-- The backward direction of the tensor-hom adjunction: a map from `M` into `Hom_ℤ(A, T)` read
as a map out of `A ⊗_ℤ M`. -/
noncomputable def hBwd (g : M ⟶ (homConstLeft A).obj T) : (tensorConstLeft A).obj M ⟶ T :=
  AddCommGrpCat.ofHom
    (TensorProduct.lift ((AddMonoidHom.toIntLinearMap g.hom :
      (M : Type w) →ₗ[ℤ] (A →ₗ[ℤ] T)).flip)).toAddMonoidHom

/-- Two maps out of `A ⊗_ℤ M` agree once they agree on the pure tensors. -/
theorem tensorConstLeft_hom_ext {f g : (tensorConstLeft A).obj M ⟶ T}
    (h : ∀ (a : A) (m : M), f.hom (a ⊗ₜ[ℤ] m) = g.hom (a ⊗ₜ[ℤ] m)) : f = g := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
  have hl : AddMonoidHom.toIntLinearMap f.hom = AddMonoidHom.toIntLinearMap g.hom :=
    TensorProduct.ext' h
  exact DFunLike.congr_fun hl x

/-- The tensor-hom adjunction on abelian groups: `A ⊗_ℤ -` is left adjoint to `Hom_ℤ(A, -)`. -/
noncomputable def tensorConstLeftAdj (A : Type w) [AddCommGroup A] :
    tensorConstLeft A ⊣ homConstLeft A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M T =>
        { toFun := hFwd
          invFun := hBwd
          left_inv := fun f => tensorConstLeft_hom_ext (fun _ _ => rfl)
          right_inv := fun g => by ext m; rfl }
      homEquiv_naturality_left_symm := fun {_ _ _} _ _ =>
        tensorConstLeft_hom_ext (fun _ _ => rfl)
      homEquiv_naturality_right := fun {_ _ _} _ _ => by ext m; rfl }

instance isLeftAdjoint_tensorConstLeft (A : Type w) [AddCommGroup A] :
    (tensorConstLeft A).IsLeftAdjoint :=
  ⟨_, ⟨tensorConstLeftAdj A⟩⟩

noncomputable instance preservesColimits_tensorConstLeft (A : Type w) [AddCommGroup A] :
    PreservesColimits (tensorConstLeft A) :=
  (tensorConstLeftAdj A).leftAdjoint_preservesColimits

instance additive_tensorConstLeft (A : Type w) [AddCommGroup A] :
    (tensorConstLeft A).Additive where
  map_add {_ _ f g} := tensorConstLeft_hom_ext (fun a m => by
    change a ⊗ₜ[ℤ] (f.hom m + g.hom m) = a ⊗ₜ[ℤ] f.hom m + a ⊗ₜ[ℤ] g.hom m
    exact TensorProduct.tmul_add a _ _)

/-- The tensor product of abelian groups over `ℤ`, as a bifunctor. -/
noncomputable def tensorBif : AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w} where
  obj A := tensorConstLeft (A : Type w)
  map {_ _} f :=
    { app := fun M => AddCommGrpCat.ofHom
        (LinearMap.rTensor (M : Type w) (AddMonoidHom.toIntLinearMap f.hom)).toAddMonoidHom
      naturality := fun _ _ _ => tensorConstLeft_hom_ext (fun _ _ => rfl) }
  map_id _ := NatTrans.ext (funext fun _ => tensorConstLeft_hom_ext (fun _ _ => rfl))
  map_comp _ _ := NatTrans.ext (funext fun _ => tensorConstLeft_hom_ext (fun _ _ => rfl))

/-- An isomorphism of abelian groups, read as an isomorphism in `AddCommGrpCat`. -/
def isoOfAddEquiv {A B : Type w} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) :
    AddCommGrpCat.of A ≅ AddCommGrpCat.of B where
  hom := AddCommGrpCat.ofHom e.toAddMonoidHom
  inv := AddCommGrpCat.ofHom e.symm.toAddMonoidHom
  hom_inv_id := by ext x; exact e.symm_apply_apply x
  inv_hom_id := by ext x; exact e.apply_symm_apply x

/-- An isomorphism of abelian groups induces one of the tensor products by a fixed group. -/
noncomputable def tensorCongrLeftIso {A B : AddCommGrpCat.{w}} (e : A ≅ B)
    (M : AddCommGrpCat.{w}) :
    (tensorConstLeft (A : Type w)).obj M ≅ (tensorConstLeft (B : Type w)).obj M where
  hom := AddCommGrpCat.ofHom
    (LinearMap.rTensor (M : Type w) (AddMonoidHom.toIntLinearMap e.hom.hom)).toAddMonoidHom
  inv := AddCommGrpCat.ofHom
    (LinearMap.rTensor (M : Type w) (AddMonoidHom.toIntLinearMap e.inv.hom)).toAddMonoidHom
  hom_inv_id := tensorConstLeft_hom_ext (fun a m => by
    have h : e.inv.hom (e.hom.hom a) = a :=
      DFunLike.congr_fun (AddCommGrpCat.hom_ext_iff.mp e.hom_inv_id) a
    exact congrArg (fun x => x ⊗ₜ[ℤ] m) h)
  inv_hom_id := tensorConstLeft_hom_ext (fun b m => by
    have h : e.hom.hom (e.inv.hom b) = b :=
      DFunLike.congr_fun (AddCommGrpCat.hom_ext_iff.mp e.inv_hom_id) b
    exact congrArg (fun x => x ⊗ₜ[ℤ] m) h)

/-! ### `ℤ` as an abelian group, and the morphisms out of it -/

/-- `ℤ`, as an object of `AddCommGrpCat`. -/
noncomputable abbrev intObj : AddCommGrpCat.{w} := AddCommGrpCat.of (ULift.{w} ℤ)

/-- The morphism of abelian groups `ℤ ⟶ M` carrying the generator to `m`. -/
noncomputable def intHom {M : AddCommGrpCat.{w}} (m : M) : intObj.{w} ⟶ M :=
  AddCommGrpCat.ofHom (uliftZMultiplesHom (M : Type w) m)

theorem intHom_apply {M : AddCommGrpCat.{w}} (m : M) (k : intObj.{w}) :
    (intHom m).hom k = k.down • m := rfl

theorem intHom_add {M : AddCommGrpCat.{w}} (m m' : M) :
    intHom (m + m') = intHom m + intHom m' := by
  ext k
  change k.down • (m + m') = k.down • m + k.down • m'
  exact smul_add _ _ _

theorem intHom_zsmul {M : AddCommGrpCat.{w}} (c : ℤ) (m : M) :
    intHom (c • m) = c • intHom m := by
  ext k
  change k.down • (c • m) = c • (k.down • m)
  exact smul_comm _ _ _

theorem intHom_comp {M N : AddCommGrpCat.{w}} (m : M) (φ : M ⟶ N) :
    intHom (φ.hom m) = intHom m ≫ φ := by
  ext k
  change k.down • (φ.hom m) = φ.hom (k.down • m)
  exact (map_zsmul φ.hom _ _).symm

theorem intHom_eq_zsmul_id (k : ℤ) :
    intHom (M := intObj.{w}) (ULift.up k) = k • CategoryStruct.id intObj.{w} := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun j => ?_)
  change j.down • (ULift.up k : ULift.{w} ℤ) = k • j
  refine ULift.down_injective ?_
  change j.down * k = k * j.down
  exact mul_comm _ _

/-! ### The canonical comparison for an additive endofunctor -/

variable (F : AddCommGrpCat.{w} ⥤ AddCommGrpCat.{w}) [F.Additive]

/-- The bilinear map `F(ℤ) × M → F(M)` carrying `(a, m)` to the value at `a` of `F` applied to
the morphism `ℤ ⟶ M` with generator `m`. -/
noncomputable def tensorCompBil (M : AddCommGrpCat.{w}) :
    (F.obj intObj.{w} : Type w) →ₗ[ℤ] (M : Type w) →ₗ[ℤ] (F.obj M : Type w) :=
  LinearMap.mk₂ ℤ (fun a m => (F.map (intHom m)).hom a)
    (fun _ _ _ => map_add _ _ _)
    (fun _ _ _ => map_zsmul _ _ _)
    (fun _ _ _ => by rw [intHom_add, F.map_add]; rfl)
    (fun _ _ _ => by rw [intHom_zsmul, F.map_zsmul]; rfl)

/-- The canonical comparison `F(ℤ) ⊗_ℤ M ⟶ F(M)` attached to an additive endofunctor of abelian
groups, natural in `M`. -/
noncomputable def tensorComp : tensorConstLeft (F.obj intObj.{w} : Type w) ⟶ F where
  app M := AddCommGrpCat.ofHom (TensorProduct.lift (tensorCompBil F M)).toAddMonoidHom
  naturality {_ _} φ := tensorConstLeft_hom_ext (fun a m => by
    change (F.map (intHom (φ.hom m))).hom a = (F.map φ).hom ((F.map (intHom m)).hom a)
    rw [intHom_comp, F.map_comp]; rfl)

@[simp] theorem tensorComp_app_tmul (M : AddCommGrpCat.{w})
    (a : (F.obj intObj.{w} : Type w)) (m : M) :
    ((tensorComp F).app M).hom (a ⊗ₜ[ℤ] m) = (F.map (intHom m)).hom a := rfl

/-- The comparison is an isomorphism at `ℤ`. -/
instance isIso_tensorComp_app_intObj : IsIso ((tensorComp F).app intObj.{w}) := by
  refine ⟨AddCommGrpCat.ofHom
    ((TensorProduct.mk ℤ (F.obj intObj.{w} : Type w) (ULift.{w} ℤ)).flip
      (ULift.up 1)).toAddMonoidHom, ?_, ?_⟩
  · refine tensorConstLeft_hom_ext (fun a k => ?_)
    change ((F.map (intHom k)).hom a) ⊗ₜ[ℤ] (ULift.up (1 : ℤ)) = a ⊗ₜ[ℤ] k
    rw [show k = (ULift.up k.down : ULift.{w} ℤ) from rfl, intHom_eq_zsmul_id,
      F.map_zsmul, F.map_id]
    change ((k.down : ℤ) • a) ⊗ₜ[ℤ] (ULift.up (1 : ℤ)) = a ⊗ₜ[ℤ] (ULift.up k.down)
    rw [TensorProduct.smul_tmul]
    congr 1
    refine ULift.down_injective ?_
    change k.down * 1 = k.down
    exact mul_one _
  · refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a => ?_)
    change (F.map (intHom (ULift.up (1 : ℤ)))).hom a = a
    rw [intHom_eq_zsmul_id, F.map_zsmul, F.map_id]
    change (1 : ℤ) • a = a
    exact one_smul _ _

/-! ### Free modules of finite rank -/

/-- A basis of an abelian group exhibits it as a coproduct of copies of `ℤ`. -/
noncomputable def isColimitBasisCofan {G : AddCommGrpCat.{w}} {n : Type}
    (b : Module.Basis n ℤ (G : Type w)) :
    IsColimit (Cofan.mk (f := fun _ : n => intObj.{w}) G (fun i => intHom (b i))) where
  desc t := AddCommGrpCat.ofHom
    (b.constr ℤ (fun i => (Cofan.inj t i).hom (ULift.up 1))).toAddMonoidHom
  fac t := by
    rintro ⟨i⟩
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun k => ?_)
    change (b.constr ℤ _) (k.down • b i) = (Cofan.inj t i).hom k
    rw [map_zsmul, Module.Basis.constr_basis,
      show k = k.down • (ULift.up 1 : ULift.{w} ℤ) from
        ULift.down_injective (by change k.down = k.down * 1; exact (mul_one _).symm),
      map_zsmul]
    congr 1
    change k.down * 1 = k.down
    exact mul_one _
  uniq t m hm := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.toIntLinearMap_injective ?_)
    refine Module.Basis.ext b fun i => ?_
    change m.hom (b i) = (b.constr ℤ _) (b i)
    rw [Module.Basis.constr_basis]
    have h1 := DFunLike.congr_fun
      (AddCommGrpCat.hom_ext_iff.mp (hm ⟨i⟩)) (ULift.up (1 : ℤ))
    change m.hom (b i) = (Cofan.inj t i).hom (ULift.up 1)
    refine Eq.trans ?_ h1
    change m.hom (b i) = m.hom ((1 : ℤ) • b i)
    rw [one_smul]

/-- **The comparison is an isomorphism at a free `ℤ`-module of finite rank.** This is additivity
of `F` over a finite direct sum: a free module of finite rank is a finite coproduct of copies of
`ℤ`, both sides preserve finite coproducts, and the comparison is invertible at `ℤ`. -/
@[ega "III 7.2.4" "special case"]
theorem isIso_tensorComp_app_of_free_finite (G : AddCommGrpCat.{w})
    [Module.Free ℤ (G : Type w)] [Module.Finite ℤ (G : Type w)] :
    IsIso ((tensorComp F).app G) := by
  classical
  have : Fintype (Module.Free.ChooseBasisIndex ℤ (G : Type w)) :=
    Module.Free.ChooseBasisIndex.fintype ℤ _
  set b : Module.Basis (Fin _) ℤ (G : Type w) := (Module.Free.chooseBasis ℤ (G : Type w)).reindex
    (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (G : Type w)))
  exact Stacks.EilenbergWatts.isIso_app_of_isColimit (tensorComp F) (isColimitBasisCofan b)
    (fun j => by cases j with | mk i => exact isIso_tensorComp_app_intObj F)

/-! ### An abelian group as the filtered colimit of its finitely generated subgroups -/

/-- The poset of finitely generated subgroups of an abelian group, as an index category. -/
abbrev FGSub (M : AddCommGrpCat.{w}) := {N : Submodule ℤ (M : Type w) // N.FG}

/-- The diagram of finitely generated subgroups of `M`, with the inclusions as transition
maps. -/
noncomputable def fgDiagram (M : AddCommGrpCat.{w}) : FGSub M ⥤ AddCommGrpCat.{w} where
  obj N := AddCommGrpCat.of (N.1 : Type w)
  map {_ _} h := AddCommGrpCat.ofHom (Submodule.inclusion (leOfHom h)).toAddMonoidHom

/-- The cocone on `fgDiagram M` given by the inclusions of the finitely generated subgroups
into `M`. -/
noncomputable def fgCocone (M : AddCommGrpCat.{w}) : Cocone (fgDiagram M) where
  pt := M
  ι := { app := fun N => AddCommGrpCat.ofHom N.1.subtype.toAddMonoidHom
         naturality := by intros; rfl }

/-- The value of a cocone leg on an element `x` does not depend on which finitely generated
subgroup containing `x` the leg is taken at. -/
theorem fgCocone_app_apply_eq (t : Cocone (fgDiagram M)) (B C : FGSub M)
    (x : M) (hB : x ∈ B.1) (hC : x ∈ C.1) :
    (t.ι.app B).hom ⟨x, hB⟩ = (t.ι.app C).hom ⟨x, hC⟩ := by
  have key : ∀ (P Q : FGSub M) (h : P ≤ Q) (y : M) (hP : y ∈ P.1),
      (t.ι.app P).hom ⟨y, hP⟩ = (t.ι.app Q).hom ⟨y, h hP⟩ := by
    intro P Q h y hP
    exact (DFunLike.congr_fun
      (AddCommGrpCat.hom_ext_iff.mp (t.w (homOfLE h))) (⟨y, hP⟩ : P.1)).symm
  rw [key B ⟨B.1 ⊔ C.1, B.2.sup C.2⟩ le_sup_left x hB,
    key C ⟨B.1 ⊔ C.1, B.2.sup C.2⟩ le_sup_right x hC]

/-- The map out of `M` induced by a cocone on the diagram of finitely generated subgroups: an
element `x` is sent to the value of the cocone leg at the subgroup it generates. -/
noncomputable def fgDesc (t : Cocone (fgDiagram M)) : M ⟶ t.pt :=
  AddCommGrpCat.ofHom
    { toFun := fun x =>
        (t.ι.app ⟨(ℤ : Type) ∙ x, fg_span_singleton x⟩).hom ⟨x, mem_span_singleton_self x⟩
      map_zero' := by
        refine Eq.trans ?_ (map_zero (t.ι.app ⟨(ℤ : Type) ∙ (0 : M), fg_span_singleton 0⟩).hom)
        rfl
      map_add' := fun x y => by
        have hx : x ∈ ((ℤ : Type) ∙ x) ⊔ ((ℤ : Type) ∙ y) :=
          mem_sup_left (mem_span_singleton_self x)
        have hy : y ∈ ((ℤ : Type) ∙ x) ⊔ ((ℤ : Type) ∙ y) :=
          mem_sup_right (mem_span_singleton_self y)
        set C : FGSub M :=
          ⟨((ℤ : Type) ∙ x) ⊔ ((ℤ : Type) ∙ y),
            (fg_span_singleton x).sup (fg_span_singleton y)⟩ with hC
        rw [fgCocone_app_apply_eq t _ C (x + y) _ (add_mem hx hy),
          fgCocone_app_apply_eq t _ C x _ hx, fgCocone_app_apply_eq t _ C y _ hy]
        exact map_add (t.ι.app C).hom (⟨x, hx⟩ : C.1) ⟨y, hy⟩ }

/-- **An abelian group is the filtered colimit of its finitely generated subgroups.** -/
noncomputable def fgCoconeIsColimit (M : AddCommGrpCat.{w}) : IsColimit (fgCocone M) where
  desc t := fgDesc t
  fac t N := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x =>
    fgCocone_app_apply_eq t _ N x.1 _ x.2)
  uniq _ _ hm := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x =>
    DFunLike.congr_fun (AddCommGrpCat.hom_ext_iff.mp
      (hm ⟨(ℤ : Type) ∙ x, fg_span_singleton x⟩))
      (⟨x, mem_span_singleton_self x⟩ : ((ℤ : Type) ∙ x)))

/-- **The comparison is an isomorphism at a flat `ℤ`-module.** A flat `ℤ`-module is torsion
free, so its finitely generated subgroups are free of finite rank, and it is their filtered
colimit; the comparison is invertible on that diagram and both sides preserve the colimit. -/
theorem isIso_tensorComp_app_of_flat (N : AddCommGrpCat.{w})
    [Module.Flat ℤ (N : Type w)] (hF : PreservesColimitsOfShape (FGSub N) F) :
    IsIso ((tensorComp F).app N) := by
  have := hF
  have : Module.IsTorsionFree ℤ (N : Type w) :=
    Submodule.isTorsionFree_iff_torsion_eq_bot.mpr Module.Flat.torsion_eq_bot
  refine Stacks.EilenbergWatts.isIso_app_of_isColimit (tensorComp F)
    (fgCoconeIsColimit N) (fun P => ?_)
  have : Module.Finite ℤ (P.1 : Type w) := Module.Finite.iff_fg.mpr P.2
  exact isIso_tensorComp_app_of_free_finite F (AddCommGrpCat.of (P.1 : Type w))

/-! ### Tensoring a sheaf by a constant sheaf -/

section Site

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

/-- Tensoring a presheaf of abelian groups by a varying abelian group: the functor
`M ↦ (U ↦ P(U) ⊗_ℤ M)`. -/
noncomputable def tensorPsh (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    AddCommGrpCat.{w} ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{w}) :=
  tensorBif.flip ⋙ (Functor.whiskeringLeft Cᵒᵖ AddCommGrpCat.{w} AddCommGrpCat.{w}).obj P

/-- Evaluating `tensorPsh P` at an object of the site is tensoring by the sections over it. -/
theorem tensorPsh_comp_evaluation (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) (U : Cᵒᵖ) :
    tensorPsh P ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj U
      = tensorConstLeft (P.obj U : Type w) := rfl

noncomputable instance preservesColimitsOfShape_tensorPsh (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (I : Type*) [Category* I] : PreservesColimitsOfShape I (tensorPsh P) := by
  refine preservesColimitsOfShape_of_evaluation _ I (fun U => ?_)
  rw [tensorPsh_comp_evaluation]
  infer_instance

instance additive_tensorPsh (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) : (tensorPsh P).Additive where
  map_add {_ _ f g} := by
    refine NatTrans.ext (funext fun _ => tensorConstLeft_hom_ext (fun a m => ?_))
    change a ⊗ₜ[ℤ] (f.hom m + g.hom m) = a ⊗ₜ[ℤ] f.hom m + a ⊗ₜ[ℤ] g.hom m
    exact TensorProduct.tmul_add a _ _

/-- The natural isomorphism `P ⊗_ℤ ℤ ≅ P` of presheaves of abelian groups. -/
noncomputable def tensorPshObjIntIso (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (tensorPsh P).obj intObj.{w} ≅ P :=
  NatIso.ofComponents
    (fun U => isoOfAddEquiv
      (TensorProduct.congr (LinearEquiv.refl ℤ (P.obj U : Type w))
        (ULift.moduleEquiv (R := ℤ) (M := ℤ)) ≪≫ₗ
          TensorProduct.rid ℤ (P.obj U : Type w)).toAddEquiv)
    (fun {U V} f => tensorConstLeft_hom_ext (fun a k => by
      change k.down • ((P.map f).hom a) = (P.map f).hom (k.down • a)
      exact (map_zsmul (P.map f).hom _ _).symm))

theorem additive_presheafToSheaf [HasWeakSheafify J AddCommGrpCat.{w}] :
    (presheafToSheaf J AddCommGrpCat.{w}).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (presheafToSheaf J AddCommGrpCat.{w})
  exact Functor.additive_of_preservesBinaryBiproducts _

variable [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Tensoring a sheaf of abelian groups by the constant sheaf on a varying abelian group: the
functor `M ↦ 𝓕 ⊗_ℤ M̲`, the sheafification of `U ↦ 𝓕(U) ⊗_ℤ M`. -/
noncomputable def tensorConstSheaf (𝓕 : Sheaf J AddCommGrpCat.{w}) :
    AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w} :=
  tensorPsh ((sheafToPresheaf J AddCommGrpCat.{w}).obj 𝓕) ⋙ presheafToSheaf J AddCommGrpCat.{w}

noncomputable instance preservesColimitsOfShape_tensorConstSheaf
    (𝓕 : Sheaf J AddCommGrpCat.{w}) (I : Type*) [Category* I] :
    PreservesColimitsOfShape I (tensorConstSheaf J 𝓕) := by
  dsimp [tensorConstSheaf]
  infer_instance

theorem additive_tensorConstSheaf (𝓕 : Sheaf J AddCommGrpCat.{w}) :
    (tensorConstSheaf J 𝓕).Additive := by
  have : (presheafToSheaf J AddCommGrpCat.{w}).Additive := additive_presheafToSheaf J
  dsimp [tensorConstSheaf]
  infer_instance

/-- `𝓕 ⊗_ℤ ℤ̲ ≅ 𝓕`: tensoring by the constant sheaf on `ℤ` changes nothing. -/
noncomputable def tensorConstSheafObjIntIso (𝓕 : Sheaf J AddCommGrpCat.{w}) :
    (tensorConstSheaf J 𝓕).obj intObj.{w} ≅ 𝓕 :=
  (presheafToSheaf J AddCommGrpCat.{w}).mapIso (tensorPshObjIntIso _) ≪≫
    asIso ((sheafificationAdjunction J AddCommGrpCat.{w}).counit.app 𝓕)

end Site

end Stacks.EtaleCohomology.TensorConstant

namespace Stacks.EtaleCohomology

open Stacks.EtaleCohomology.TensorConstant

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

/-- Abelian sheaves on the small étale site admit sheafification; this is
`AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology` in the form instance search needs,
`CategoryTheory.HasWeakSheafify` being an abbreviation for an adjointness statement rather than
a class. -/
theorem hasWeakSheafify_smallEtaleTopology (X : Scheme.{u}) :
    HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  let : HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
    Scheme.hasSheafify_smallEtaleTopology X
  inferInstance

attribute [local instance 3000] hasWeakSheafify_smallEtaleTopology

/-- The functor `M ↦ H^p(X, ℰ ⊗_ℤ M̲)` on abelian groups, for a fixed abelian sheaf `ℰ` on the
small étale site of `X`. -/
noncomputable def etaleTensorConstH (X : Scheme.{u}) (p : ℕ)
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    AddCommGrpCat.{max (u + 1) v} ⥤ AddCommGrpCat.{max (u + 1) v} :=
  tensorConstSheaf X.smallEtaleTopology E ⋙
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived p

instance additive_etaleTensorConstH (X : Scheme.{u}) (p : ℕ)
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleTensorConstH X p E).Additive := by
  have : (tensorConstSheaf X.smallEtaleTopology E).Additive :=
    additive_tensorConstSheaf X.smallEtaleTopology E
  dsimp only [etaleTensorConstH]
  infer_instance

/-- The value of `M ↦ H^p(X, ℰ ⊗_ℤ M̲)` at `ℤ` is the étale cohomology of `ℰ` itself. -/
noncomputable def etaleTensorConstHObjIntIso (X : Scheme.{u}) (p : ℕ)
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleTensorConstH X p E).obj intObj.{max (u + 1) v} ≅
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj E :=
  ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived p).mapIso
    (tensorConstSheafObjIntIso X.smallEtaleTopology E)

/-- **The canonical comparison `H^p(X, ℰ) ⊗_ℤ M ⟶ H^p(X, ℰ ⊗_ℤ M̲)`.** It is the component
at `M` of the natural transformation `tensorComp`, read through the identification
`etaleTensorConstHObjIntIso` of `H^p(X, ℰ ⊗_ℤ ℤ̲)` with `H^p(X, ℰ)`; on a pure tensor `α ⊗ m` it
is the image of `α` under the map induced by `ℰ ≅ ℰ ⊗_ℤ ℤ̲ ⟶ ℰ ⊗_ℤ M̲` attached to the morphism
`ℤ ⟶ M` carrying the generator to `m`. -/
noncomputable def etaleTensorConstComparison (X : Scheme.{u}) (p : ℕ)
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (M : AddCommGrpCat.{max (u + 1) v}) :
    (tensorConstLeft
        (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj E :
          Type (max (u + 1) v))).obj M ⟶ (etaleTensorConstH X p E).obj M :=
  (tensorCongrLeftIso (etaleTensorConstHObjIntIso X p E).symm M).hom ≫
    (tensorComp (etaleTensorConstH X p E)).app M

/-- **Stacks 0F0E, the case of a single sheaf and a single flat module.** Let `X` be a
quasi-compact and quasi-separated scheme, `ℰ` an abelian sheaf on the small étale site of `X`
and `M` a flat `ℤ`-module. Then the canonical map

> `H^p(X, ℰ) ⊗_ℤ M ⟶ H^p(X, ℰ ⊗_ℤ M̲)`

is an isomorphism, where `M̲` is the constant sheaf on `M`.

This is steps 6 to 8 of the source's proof. `M` is written as the filtered colimit of its
finitely generated subgroups, which are free of finite rank because `M` is torsion free; the
comparison is invertible there by additivity of cohomology over a finite direct sum; and both
sides commute with the filtered colimit, the left because `- ⊗_ℤ M` is a left adjoint and the
right by [Stacks, Tag 03Q5]. -/
theorem isIso_etaleTensorConstComparison (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (p : ℕ)
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (M : AddCommGrpCat.{max (u + 1) v}) [Module.Flat ℤ (M : Type (max (u + 1) v))] :
    IsIso (etaleTensorConstComparison X p E M) := by
  have hcol : PreservesColimitsOfShape (FGSub M) (etaleTensorConstH X p E) := by
    have := preservesColimitsOfShape_rightDerived_Γ_smallEtale.{v} X p (FGSub M)
    dsimp only [etaleTensorConstH]
    infer_instance
  have h2 : IsIso ((tensorComp (etaleTensorConstH X p E)).app M) :=
    isIso_tensorComp_app_of_flat _ M hcol
  dsimp only [etaleTensorConstComparison]
  exact IsIso.comp_isIso

end Stacks.EtaleCohomology
