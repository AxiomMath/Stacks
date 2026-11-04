module

public import StacksFrontier.LinearAlgebra.ExteriorPower.SemilinearDerived
public import StacksFrontier.AlgebraicGeometry.MayerVietorisHgroup.AmbientOpen
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.FiveLemma

/-!
# The exterior and tensor squares as semilinear functors on arrows

Let `A` be a commutative ring and `X = (X₀ → X₁)` an arrow of `A`-modules, with cokernel
`coker X`. This file builds the semilinear functors on arrows (`Stacks.SemilinearArrowFunctor`)
whose simplicial derived functors enter the second Adams operation on the Grothendieck group of
coherent sheaves, `ψ²(F) = Σⱼ (-1)ʲ ([Lⱼ T(F)] - 2 [Lⱼ Λ²(F)])`, where `T(M) = M ⊗ M`:

* `Λ²(X₀)`, `Λ²(X₁)`, `Λ²(coker X)` and `T(X₀)`, `T(X₁)`, `T(coker X)`;
* the relative squares `D_Λ(X) = coker (Λ² X₀ → Λ² X₁)` and `D_T(X) = coker (T X₀ → T X₁)`;
* the cross terms `X₀ ⊗ coker X` and `coker X ⊗ X₀`;

together with the natural maps
`Λ² X₀ → Λ² X₁ → D_Λ(X)`, `X₀ ⊗ coker X → D_Λ(X) → Λ² (coker X)` (`x ⊗ [y] ↦ [x ∧ y]`),
`T X₀ → T X₁ → D_T(X)` and `(X₀ ⊗ coker X) ⊞ (coker X ⊗ X₀) → D_T(X) → T (coker X)`
(`x ⊗ [y] ↦ [x ⊗ y]`, `[y] ⊗ x ↦ [y ⊗ x]`), as morphisms of semilinear functors.

The functors are assembled from a few general constructions on semilinear functors: evaluation
at the source and at the target, objectwise cokernels of morphisms, tensor products, exterior
powers and biproducts. The semilinear structure of each is induced by those of its inputs,
through the lax monoidal structure of restriction of scalars for tensor products and the
comparison `⋀ⁿ_A (φ^* N) → φ^* ⋀ⁿ_B N` for exterior powers.

**Short exact sequences.** On a projective arrow `P`, that is a split monomorphism `u : P₀ → P₁`
with projective source and cokernel `C`, the four sequences

`0 → Λ² P₀ → Λ² P₁ → D_Λ(P) → 0`, `0 → P₀ ⊗ C → D_Λ(P) → Λ² C → 0`,
`0 → T P₀ → T P₁ → D_T(P) → 0`, `0 → (P₀ ⊗ C) ⊞ (C ⊗ P₀) → D_T(P) → T C → 0`

are short exact. The first and third because `Λ² u` and `u ⊗ u` are split monomorphisms. The
second is the filtration `Λ² P₀ ⊆ Fil ⊆ Λ² P₁` of `Stacks.ExteriorSquare`: `Fil` is the kernel of
`Λ² P₁ → Λ² C` and `Fil / Λ² P₀ ≅ P₀ ⊗ C`. For the fourth, the kernel of `P₁ ⊗ P₁ → C ⊗ C` is
spanned by the images of `u ⊗ P₁` and `P₁ ⊗ u`, by right exactness of the tensor product, and
`r ⊗ π` and `π ⊗ r`, for a retraction `r` of `u`, give a left inverse of the first map.

**Flat base change.** Each of these functors commutes with flat base change on projective arrows
(`Stacks.SemilinearArrowFunctor.HasFlatBaseChange`): evaluation does, exterior powers and tensor
products commute with every base change, biproducts are preserved by the additive functor
`B ⊗_A -`, and cokernels by its right exactness, through the five lemma.

## Main definitions

* `Stacks.SemilinearArrowFunctor.left`, `Stacks.SemilinearArrowFunctor.right`,
  `Stacks.SemilinearArrowFunctor.coker`: the source, the target and the cokernel of an arrow.
* `Stacks.SemilinearArrowFunctor.cokernel`, `Stacks.SemilinearArrowFunctor.tensor`,
  `Stacks.SemilinearArrowFunctor.exteriorPower`, `Stacks.SemilinearArrowFunctor.biprod`: the
  general constructions, with the morphisms `cokernelπ`, `cokernelDesc`, `tensorHom`,
  `exteriorPowerMap`, `biprodDesc`, `wedge`, `tensorBraidingIso` and `descOfExact`.
* `Stacks.SemilinearArrowFunctor.relExteriorSquare`,
  `Stacks.SemilinearArrowFunctor.relTensorSquare`, `Stacks.SemilinearArrowFunctor.cross`,
  `Stacks.SemilinearArrowFunctor.crossRev`: `D_Λ`, `D_T` and the cross terms.
* `Stacks.SemilinearArrowFunctor.crossToRelExteriorSquare`,
  `Stacks.SemilinearArrowFunctor.relExteriorSquareToCoker`,
  `Stacks.SemilinearArrowFunctor.crossSumToRelTensorSquare`,
  `Stacks.SemilinearArrowFunctor.relTensorSquareToCoker`,
  `Stacks.SemilinearArrowFunctor.crossIsoCrossRev`: the natural maps.

## Main results

* `Stacks.SemilinearArrowFunctor.shortExact_exteriorSquare`,
  `Stacks.SemilinearArrowFunctor.shortExact_relExteriorSquare`,
  `Stacks.SemilinearArrowFunctor.shortExact_tensorSquare`,
  `Stacks.SemilinearArrowFunctor.shortExact_relTensorSquare`: the four short exact sequences on
  projective arrows.
* `Stacks.SemilinearArrowFunctor.hasFlatBaseChange_cokernel`,
  `Stacks.SemilinearArrowFunctor.hasFlatBaseChange_tensor`,
  `Stacks.SemilinearArrowFunctor.hasFlatBaseChange_exteriorPower`,
  `Stacks.SemilinearArrowFunctor.hasFlatBaseChange_biprod`, and their consequences
  `Stacks.SemilinearArrowFunctor.hasFlatBaseChange_relExteriorSquare`,
  `Stacks.SemilinearArrowFunctor.hasFlatBaseChange_relTensorSquare`,
  `Stacks.SemilinearArrowFunctor.hasFlatBaseChange_cross`: flat base change.
* `ModuleCat.exteriorPower.shortExact_cross`, `ModuleCat.shortExact_tensorCross`: the cross term
  sequences for a split monomorphism of modules.

## Implementation notes

The constructions on semilinear functors are reducible, so that their components unfold to the
underlying functors of modules: for instance the derived functors of `exteriorPower 2 right` are
literally those of `Λ²` on the resolution of the target, and `coker.obj A` is
`CategoryTheory.ComposableArrows.cokernelFunctor`. The vanishing of composites, which the long
exact sequences of short exact sequences of semilinear functors take as input, is stated
componentwise, `∀ A, α.app A ≫ β.app A = 0`. The cokernels are categorical cokernels of
`ModuleCat`; the cross term maps out of `X₀ ⊗ coker X` are obtained by descending along
`X₀ ⊗ X₁ → X₀ ⊗ coker X`, which is an objectwise cokernel by right exactness of the tensor
product (`Stacks.SemilinearArrowFunctor.descOfExact`).

## References

* A. Dold, D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312.
* [Stacks, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings
open Stacks.Cohomology.AmbientMayerVietoris (biprod_inl_fst_app biprod_inl_snd_app
  biprod_inr_fst_app biprod_inr_snd_app biprod_total_app)

universe u

/-- The objectwise cokernel of a natural transformation `τ : F ⟶ G` of functors into an
abelian category, `X ↦ coker (τ_X)`. -/
@[reducible, simps]
def CategoryTheory.NatTrans.cokernelFunctor {J C : Type*} [Category J] [Category C]
    [Abelian C] {F G : J ⥤ C} (τ : F ⟶ G) : J ⥤ C where
  obj X := Limits.cokernel (τ.app X)
  map {X Y} f := cokernel.desc _ (G.map f ≫ cokernel.π (τ.app Y))
    (by rw [← Category.assoc, ← τ.naturality, Category.assoc, cokernel.condition, comp_zero])
  map_id X := by ext; simp
  map_comp f g := by ext; simp

section BiprodApp

variable {J C : Type*} [Category J] [Category C] [Preadditive C] {F G : J ⥤ C}
  [HasBinaryBiproduct F G] (X : J)

/-- `biprod.inl_desc` for a biproduct of functors, evaluated at an object. -/
@[reassoc (attr := simp)]
lemma CategoryTheory.Limits.biprod.inl_desc_app {H : J ⥤ C} (f : F ⟶ H) (g : G ⟶ H) :
    (biprod.inl : F ⟶ F ⊞ G).app X ≫ (biprod.desc f g).app X = f.app X :=
  (NatTrans.comp_app _ _ X).symm.trans (by rw [biprod.inl_desc])

/-- `biprod.inr_desc` for a biproduct of functors, evaluated at an object. -/
@[reassoc (attr := simp)]
lemma CategoryTheory.Limits.biprod.inr_desc_app {H : J ⥤ C} (f : F ⟶ H) (g : G ⟶ H) :
    (biprod.inr : G ⟶ F ⊞ G).app X ≫ (biprod.desc f g).app X = g.app X :=
  (NatTrans.comp_app _ _ X).symm.trans (by rw [biprod.inr_desc])

/-- Two morphisms out of a biproduct of functors evaluated at an object agree as soon as they
agree on both summands. -/
lemma CategoryTheory.Limits.biprod.app_hom_ext {Z : C} {f g : (F ⊞ G).obj X ⟶ Z}
    (h₁ : (biprod.inl : F ⟶ F ⊞ G).app X ≫ f = (biprod.inl : F ⟶ F ⊞ G).app X ≫ g)
    (h₂ : (biprod.inr : G ⟶ F ⊞ G).app X ≫ f = (biprod.inr : G ⟶ F ⊞ G).app X ≫ g) :
    f = g := by
  have h := biprod_total_app F G X
  rw [← Category.id_comp f, ← Category.id_comp g, ← h, Preadditive.add_comp,
    Preadditive.add_comp, Category.assoc, Category.assoc, Category.assoc, Category.assoc, h₁, h₂]

/-- `biprod.desc_eq` for a biproduct of functors, evaluated at an object. -/
lemma CategoryTheory.Limits.biprod.desc_app {H : J ⥤ C} (f : F ⟶ H) (g : G ⟶ H) :
    (biprod.desc f g).app X = (biprod.fst : F ⊞ G ⟶ F).app X ≫ f.app X +
      (biprod.snd : F ⊞ G ⟶ G).app X ≫ g.app X := by
  rw [biprod.desc_eq, NatTrans.app_add, NatTrans.comp_app, NatTrans.comp_app]

end BiprodApp

namespace ModuleCat

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- The lax monoidal structure of restriction of scalars along a ring map equal to the identity
is the identity, under the identification `ModuleCat.restrictScalarsId'`. -/
lemma restrictScalarsId'_inv_tensorHom_comp_μ (f : R →+* R) (hf : f = RingHom.id R)
    (M N : ModuleCat.{u} R) :
    ((restrictScalarsId' f hf).inv.app M ⊗ₘ (restrictScalarsId' f hf).inv.app N) ≫
      Functor.LaxMonoidal.μ (restrictScalars f) M N =
        (restrictScalarsId' f hf).inv.app (M ⊗ N) := by
  refine MonoidalCategory.tensor_ext fun m n => ?_
  exact restrictScalars_μ_tmul f M N m n

/-- The lax monoidal structure of restriction of scalars along a composite of ring maps is the
composite of the lax monoidal structures, under the identification
`ModuleCat.restrictScalarsComp'`. -/
lemma restrictScalarsComp'_inv_tensorHom_comp_μ (f : R →+* S) (g : S →+* T) (gf : R →+* T)
    (hgf : gf = g.comp f) (M N : ModuleCat.{u} T) :
    ((restrictScalarsComp' f g gf hgf).inv.app M ⊗ₘ (restrictScalarsComp' f g gf hgf).inv.app N) ≫
      Functor.LaxMonoidal.μ (restrictScalars gf) M N =
      Functor.LaxMonoidal.μ (restrictScalars f) _ _ ≫
        (restrictScalars f).map (Functor.LaxMonoidal.μ (restrictScalars g) M N) ≫
          (restrictScalarsComp' f g gf hgf).inv.app (M ⊗ N) := by
  refine MonoidalCategory.tensor_ext fun m n => ?_
  refine (restrictScalars_μ_tmul gf M N m n).trans ?_
  show _ = (Functor.LaxMonoidal.μ (restrictScalars g) M N).hom
    ((Functor.LaxMonoidal.μ (restrictScalars f) ((restrictScalars g).obj M)
      ((restrictScalars g).obj N)).hom (m ⊗ₜ n))
  exact ((congrArg (Functor.LaxMonoidal.μ (restrictScalars g) M N).hom
    (restrictScalars_μ_tmul f ((restrictScalars g).obj M) ((restrictScalars g).obj N) m n)).trans
      (restrictScalars_μ_tmul g M N m n)).symm

/-- The lax monoidal structure of restriction of scalars commutes with the braidings. -/
lemma braiding_hom_comp_μ (f : R →+* S) (M N : ModuleCat.{u} S) :
    (β_ ((restrictScalars f).obj M) ((restrictScalars f).obj N)).hom ≫
        Functor.LaxMonoidal.μ (restrictScalars f) N M =
      Functor.LaxMonoidal.μ (restrictScalars f) M N ≫ (restrictScalars f).map (β_ M N).hom := by
  refine MonoidalCategory.tensor_ext fun m n => ?_
  exact (restrictScalars_μ_tmul f N M n m).trans
    (congrArg (β_ M N).hom.hom (restrictScalars_μ_tmul f M N m n)).symm

namespace exteriorPower

/-- The `R`-linear comparison `⋀ⁿ_R (f^* N) ⟶ f^* ⋀ⁿ_S N`, `m₁ ∧ ⋯ ∧ mₙ ↦ m₁ ∧ ⋯ ∧ mₙ`, for a
ring map `f : R →+* S` and an `S`-module `N`. -/
def restrictScalarsMap (f : R →+* S) (N : ModuleCat.{u} S) (n : ℕ) :
    (functor R n).obj ((restrictScalars f).obj N) ⟶ (restrictScalars f).obj ((functor S n).obj N) :=
  desc
    { toFun v := _root_.exteriorPower.ιMulti S n (M := N) v
      map_update_add' m i x y := (_root_.exteriorPower.ιMulti S n (M := N)).map_update_add m i x y
      map_update_smul' m i c x :=
        (_root_.exteriorPower.ιMulti S n (M := N)).map_update_smul m i (f c) x
      map_eq_zero_of_eq' v _ _ h hij :=
        (_root_.exteriorPower.ιMulti S n (M := N)).map_eq_zero_of_eq v h hij }

/-- The comparison `⋀ⁿ_R (f^* N) ⟶ f^* ⋀ⁿ_S N` on wedges. -/
lemma restrictScalarsMap_mk (f : R →+* S) (N : ModuleCat.{u} S) (n : ℕ)
    (v : Fin n → (restrictScalars f).obj N) :
    (restrictScalarsMap f N n).hom (mk v) = mk (M := N) v :=
  desc_mk _ v

/-- The comparison `⋀ⁿ_R (f^* N) ⟶ f^* ⋀ⁿ_S N` is natural in `N`. -/
@[reassoc]
lemma map_comp_restrictScalarsMap (f : R →+* S) {N N' : ModuleCat.{u} S} (g : N ⟶ N') (n : ℕ) :
    (functor R n).map ((restrictScalars f).map g) ≫ restrictScalarsMap f N' n =
      restrictScalarsMap f N n ≫ (restrictScalars f).map ((functor S n).map g) := by
  refine hom_ext (AlternatingMap.ext fun v => ?_)
  exact (congrArg (restrictScalarsMap f N' n).hom (map_mk ((restrictScalars f).map g) v)).trans
    ((restrictScalarsMap_mk f N' n _).trans ((map_mk g v).symm.trans
      (congrArg (map g n).hom (restrictScalarsMap_mk f N n v)).symm))

/-- The comparison for a ring map equal to the identity is the identity, under the identification
`ModuleCat.restrictScalarsId'`. -/
lemma map_restrictScalarsId'_inv_comp_restrictScalarsMap (f : R →+* R) (hf : f = RingHom.id R)
    (N : ModuleCat.{u} R) (n : ℕ) :
    (functor R n).map ((restrictScalarsId' f hf).inv.app N) ≫ restrictScalarsMap f N n =
      (restrictScalarsId' f hf).inv.app ((functor R n).obj N) := by
  refine hom_ext (AlternatingMap.ext fun v => ?_)
  exact (congrArg (restrictScalarsMap f N n).hom (map_mk _ v)).trans
    (restrictScalarsMap_mk f N n _)

/-- The comparison for a composite of ring maps is the composite of the comparisons, under the
identification `ModuleCat.restrictScalarsComp'`. -/
lemma map_restrictScalarsComp'_inv_comp_restrictScalarsMap (f : R →+* S) (g : S →+* T)
    (gf : R →+* T) (hgf : gf = g.comp f) (N : ModuleCat.{u} T) (n : ℕ) :
    (functor R n).map ((restrictScalarsComp' f g gf hgf).inv.app N) ≫ restrictScalarsMap gf N n =
      restrictScalarsMap f ((restrictScalars g).obj N) n ≫
        (restrictScalars f).map (restrictScalarsMap g N n) ≫
          (restrictScalarsComp' f g gf hgf).inv.app ((functor T n).obj N) := by
  refine hom_ext (AlternatingMap.ext fun v => ?_)
  exact ((congrArg (restrictScalarsMap gf N n).hom (map_mk _ v)).trans
    (restrictScalarsMap_mk gf N n _)).trans
      ((congrArg (restrictScalarsMap g N n).hom
        (restrictScalarsMap_mk f ((restrictScalars g).obj N) n v)).trans
          (restrictScalarsMap_mk g N n v)).symm

/-- The wedge product `M ⊗ M ⟶ ⋀² M`, `m ⊗ n ↦ m ∧ n`. -/
def wedgeMul (M : ModuleCat.{u} R) : M ⊗ M ⟶ (functor R 2).obj M :=
  ofHom (Stacks.ExteriorSquare.wedgeLeft LinearMap.id)

/-- The wedge product on pure tensors. -/
lemma wedgeMul_tmul (M : ModuleCat.{u} R) (m n : M) :
    (wedgeMul M).hom (m ⊗ₜ n) = _root_.exteriorPower.ιMulti R 2 ![m, n] :=
  Stacks.ExteriorSquare.wedgeLeft_tmul _ m n

/-- The wedge product is natural. -/
@[reassoc]
lemma tensorHom_comp_wedgeMul {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (f ⊗ₘ f) ≫ wedgeMul N = wedgeMul M ≫ (functor R 2).map f := by
  refine MonoidalCategory.tensor_ext fun m n => ?_
  show (wedgeMul N).hom (f.hom m ⊗ₜ f.hom n) =
    _root_.exteriorPower.map 2 f.hom ((wedgeMul M).hom (m ⊗ₜ n))
  rw [wedgeMul_tmul, wedgeMul_tmul, _root_.exteriorPower.map_apply_ιMulti]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- The wedge product commutes with restriction of scalars. -/
lemma μ_comp_map_wedgeMul (f : R →+* S) (M : ModuleCat.{u} S) :
    Functor.LaxMonoidal.μ (restrictScalars f) M M ≫ (restrictScalars f).map (wedgeMul M) =
      wedgeMul ((restrictScalars f).obj M) ≫ restrictScalarsMap f M 2 := by
  refine MonoidalCategory.tensor_ext fun m n => ?_
  show (wedgeMul M).hom ((Functor.LaxMonoidal.μ (restrictScalars f) M M).hom (m ⊗ₜ n)) =
    (restrictScalarsMap f M 2).hom ((wedgeMul ((restrictScalars f).obj M)).hom (m ⊗ₜ n))
  exact ((congrArg (wedgeMul M).hom (restrictScalars_μ_tmul f M M m n)).trans
    (wedgeMul_tmul M m n)).trans ((congrArg (restrictScalarsMap f M 2).hom
      (wedgeMul_tmul ((restrictScalars f).obj M) m n)).trans
        (restrictScalarsMap_mk f M 2 ![m, n])).symm

/-- For `n ≠ 0`, the `n`-th exterior power of the zero map is zero. -/
lemma functor_map_zero {M N : ModuleCat.{u} R} {n : ℕ} (hn : n ≠ 0) :
    (functor R n).map (0 : M ⟶ N) = 0 := by
  refine hom_ext (AlternatingMap.ext fun v => ?_)
  show map 0 n (mk v) = 0
  rw [map_mk]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact (mk (M := N)).map_coord_zero 0 rfl

end exteriorPower

/-- For `f : M ⟶ N`, the map `M ⊗ M ⟶ coker (⋀² f)`, `m ⊗ m' ↦ [f m ∧ f m']`, vanishes. -/
lemma whiskerLeft_comp_whiskerRight_comp_wedgeMul_comp_π {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (𝟙 M ⊗ₘ f) ≫ (f ⊗ₘ 𝟙 N) ≫ exteriorPower.wedgeMul N ≫
      cokernel.π ((exteriorPower.functor R 2).map f) = 0 := by
  rw [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id,
    exteriorPower.tensorHom_comp_wedgeMul_assoc, cokernel.condition, comp_zero]

/-- For `f : M ⟶ N`, the map `M ⊗ N ⟶ ⋀² (coker f)`, `m ⊗ n ↦ [f m] ∧ [n]`, vanishes. -/
lemma whiskerRight_comp_wedgeMul_comp_map_π {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (f ⊗ₘ 𝟙 N) ≫ exteriorPower.wedgeMul N ≫ (exteriorPower.functor R 2).map (cokernel.π f) = 0 := by
  rw [← exteriorPower.tensorHom_comp_wedgeMul, tensorHom_comp_tensorHom_assoc, cokernel.condition,
    MonoidalPreadditive.zero_tensor, zero_comp]

/-- A morphism of modules and the projection onto its cokernel form an exact sequence. -/
lemma exact_cokernel_π {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    Function.Exact f.hom (cokernel.π f).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (ShortComplex.cokernelSequence_exact f)

/-- The projection onto a cokernel of modules is surjective. -/
lemma surjective_cokernel_π {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    Function.Surjective (cokernel.π f).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- Right exactness of `L ⊗ -`: `L ⊗ M ⟶ L ⊗ N ⟶ L ⊗ coker f` is exact. -/
lemma exact_whiskerLeft_cokernel (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (ShortComplex.mk (𝟙 L ⊗ₘ f) (𝟙 L ⊗ₘ cokernel.π f) (by
      rw [tensorHom_comp_tensorHom, Category.id_comp, cokernel.condition,
        MonoidalPreadditive.tensor_zero])).Exact :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
    (lTensor_exact L (exact_cokernel_π f) (surjective_cokernel_π f))

/-- Right exactness of `L ⊗ -`: `L ⊗ N ⟶ L ⊗ coker f` is an epimorphism. -/
lemma epi_whiskerLeft_cokernel (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    Epi (𝟙 L ⊗ₘ cokernel.π f) :=
  (ModuleCat.epi_iff_surjective _).2 (LinearMap.lTensor_surjective L (surjective_cokernel_π f))

/-- Right exactness of `- ⊗ L`: `M ⊗ L ⟶ N ⊗ L ⟶ coker f ⊗ L` is exact. -/
lemma exact_whiskerRight_cokernel (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (ShortComplex.mk (f ⊗ₘ 𝟙 L) (cokernel.π f ⊗ₘ 𝟙 L) (by
      rw [tensorHom_comp_tensorHom, Category.id_comp, cokernel.condition,
        MonoidalPreadditive.zero_tensor])).Exact :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
    (rTensor_exact L (exact_cokernel_π f) (surjective_cokernel_π f))

/-- Right exactness of `- ⊗ L`: `N ⊗ L ⟶ coker f ⊗ L` is an epimorphism. -/
lemma epi_whiskerRight_cokernel (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    Epi (cokernel.π f ⊗ₘ 𝟙 L) :=
  (ModuleCat.epi_iff_surjective _).2 (LinearMap.rTensor_surjective L (surjective_cokernel_π f))

/-- The adjoint of `S ⊗_R (M ⊗ N) ≅ (S ⊗_R M) ⊗ (S ⊗_R N) ⟶ M' ⊗ N'` is the tensor product of
the adjoints followed by the lax monoidal structure of restriction of scalars. -/
lemma homEquiv_δ_comp_tensorHom (f : R →+* S) {M N : ModuleCat.{u} R} {M' N' : ModuleCat.{u} S}
    (a : (extendScalars f).obj M ⟶ M') (b : (extendScalars f).obj N ⟶ N') :
    (extendRestrictScalarsAdj f).homEquiv _ _
        (Functor.OplaxMonoidal.δ (extendScalars f) M N ≫ (a ⊗ₘ b)) =
      ((extendRestrictScalarsAdj f).homEquiv _ _ a ⊗ₘ (extendRestrictScalarsAdj f).homEquiv _ _ b) ≫
        Functor.LaxMonoidal.μ (restrictScalars f) M' N' := by
  refine MonoidalCategory.tensor_ext fun m n => ?_
  refine (extendRestrictScalarsAdj_homEquiv_apply (M := M ⊗ N) _ (m ⊗ₜ n)).trans ?_
  refine (congrArg (a ⊗ₘ b).hom (extendScalars_δ_tmul f M N m n)).trans ?_
  exact (restrictScalars_μ_tmul f M' N' _ _).symm

/-- The adjoint of `S ⊗_R ⋀ⁿ M ≅ ⋀ⁿ (S ⊗_R M) ⟶ ⋀ⁿ M'` is `⋀ⁿ` of the adjoint followed by the
comparison `⋀ⁿ_R (f^* M') ⟶ f^* ⋀ⁿ_S M'`. -/
lemma exteriorPower.homEquiv_extendScalarsIso_hom_comp (f : R →+* S) {M : ModuleCat.{u} R}
    {M' : ModuleCat.{u} S} (a : (extendScalars f).obj M ⟶ M') (n : ℕ) :
    (extendRestrictScalarsAdj f).homEquiv _ _
        ((exteriorPower.extendScalarsIso f n).hom.app M ≫ (exteriorPower.functor S n).map a) =
      (exteriorPower.functor R n).map ((extendRestrictScalarsAdj f).homEquiv _ _ a) ≫
        exteriorPower.restrictScalarsMap f M' n := by
  refine exteriorPower.hom_ext (AlternatingMap.ext fun v => ?_)
  show (exteriorPower.map a n).hom (((exteriorPower.extendScalarsIso f n).hom.app M).hom
      ((1 : S) ⊗ₜ[R, f] _root_.exteriorPower.ιMulti R n v)) =
    (exteriorPower.restrictScalarsMap f M' n).hom
      ((exteriorPower.map ((extendRestrictScalarsAdj f).homEquiv M M' a) n).hom
        (exteriorPower.mk v))
  rw [exteriorPower.extendScalarsIso_hom_app_tmul_ιMulti, one_smul, exteriorPower.map_mk]
  exact (exteriorPower.map_mk a _).trans (exteriorPower.restrictScalarsMap_mk f M' n _).symm

/-- The map `M ⊗ N ⟶ ⋀² N`, `m ⊗ n ↦ f m ∧ n`, is `Stacks.ExteriorSquare.wedgeLeft f`. -/
lemma whiskerRight_comp_wedgeMul_hom {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ((f ⊗ₘ 𝟙 N) ≫ exteriorPower.wedgeMul N).hom = Stacks.ExteriorSquare.wedgeLeft f.hom := by
  refine TensorProduct.ext' fun m n => ?_
  show (exteriorPower.wedgeMul N).hom (f.hom m ⊗ₜ n) = _
  rw [exteriorPower.wedgeMul_tmul]
  exact (Stacks.ExteriorSquare.wedgeLeft_tmul f.hom m n).symm

/-- **The cross term of the exterior square.** For a split monomorphism `f : M ⟶ N` with
cokernel `C`, the sequence `0 → M ⊗ C → coker (⋀² f) → ⋀² C → 0`, whose maps are
`m ⊗ [n] ↦ [f m ∧ n]` and the map induced by `⋀² (N → C)`, is short exact. The maps are
given through the identities characterizing them. -/
theorem exteriorPower.shortExact_cross {M N : ModuleCat.{u} R} (f : M ⟶ N) (r : N ⟶ M)
    (hr : f ≫ r = 𝟙 M) (c : M ⊗ cokernel f ⟶ cokernel ((functor R 2).map f))
    (hc : (𝟙 M ⊗ₘ cokernel.π f) ≫ c = (f ⊗ₘ 𝟙 N) ≫ wedgeMul N ≫ cokernel.π ((functor R 2).map f))
    (d : cokernel ((functor R 2).map f) ⟶ (functor R 2).obj (cokernel f))
    (hd : cokernel.π ((functor R 2).map f) ≫ d = (functor R 2).map (cokernel.π f)) (w : c ≫ d = 0) :
    (ShortComplex.mk c d w).ShortExact := by
  have hπ := surjective_cokernel_π f
  have hvu : (cokernel.π f).hom ∘ₗ f.hom = 0 := congrArg Hom.hom (cokernel.condition f)
  have hrr : ∃ r' : N →ₗ[R] M, r' ∘ₗ f.hom = LinearMap.id := ⟨r.hom, congrArg Hom.hom hr⟩
  have hc' : ∀ t : M ⊗[R] N, c.hom ((LinearMap.lTensor M (cokernel.π f).hom) t) =
      (cokernel.π ((functor R 2).map f)).hom (Stacks.ExteriorSquare.wedgeLeft f.hom t) := by
    intro t
    rw [← whiskerRight_comp_wedgeMul_hom]
    exact congrArg (fun g => g.hom t) hc
  apply ModuleCat.shortComplex_shortExact
  · intro x
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := surjective_cokernel_π _ x
      have hz : (z : ⋀[R]^2 N) ∈ LinearMap.ker (_root_.exteriorPower.map 2 (cokernel.π f).hom) := by
        exact (congrArg (fun g => g.hom z) hd).symm.trans hx
      rw [Stacks.ExteriorSquare.ker_map_eq_filtration (exact_cokernel_π f) hπ] at hz
      obtain ⟨t, rfl⟩ := hz
      exact ⟨_, hc' t⟩
    · rintro ⟨y, rfl⟩
      exact congrArg (fun g => g.hom y) w
  · intro t₁ t₂ h
    rw [← sub_eq_zero] at h ⊢
    rw [← map_sub] at h
    obtain ⟨t, ht⟩ := LinearMap.lTensor_surjective M hπ (t₁ - t₂)
    rw [← ht] at h ⊢
    rw [hc'] at h
    obtain ⟨y, hy⟩ := (exact_cokernel_π ((functor R 2).map f) _).1 h
    have h₁ := Stacks.ExteriorSquare.filtrationToTensor_apply_wedgeLeft hrr hvu t
    have h₂ : Stacks.ExteriorSquare.filtrationToTensor f.hom (cokernel.π f).hom hrr hvu
        (Stacks.ExteriorSquare.toFiltration f.hom y) = 0 :=
      LinearMap.congr_fun (Stacks.ExteriorSquare.filtrationToTensor_comp_toFiltration hrr hvu) y
    have h₃ : Stacks.ExteriorSquare.toFiltration f.hom y =
        ⟨_, Stacks.ExteriorSquare.wedgeLeft_mem_filtration f.hom t⟩ :=
      Subtype.ext hy
    exact h₁.symm.trans (h₃ ▸ h₂)
  · intro y
    obtain ⟨z, rfl⟩ := _root_.exteriorPower.map_surjective (n := 2) hπ y
    exact ⟨(cokernel.π ((functor R 2).map f)).hom z, congrArg (fun g => g.hom z) hd⟩

/-- **The cross terms of the tensor square.** For a split monomorphism `f : M ⟶ N` with cokernel
`C` and a biproduct `B` of `M ⊗ C` and `C ⊗ M` (given by `i₁, i₂, p₁, p₂` with
`p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙`), the sequence `0 → B → coker (f ⊗ f) → C ⊗ C → 0`, whose maps are
`m ⊗ [n] ↦ [f m ⊗ n]`, `[n] ⊗ m ↦ [n ⊗ f m]` and the map induced by `(N → C) ⊗ (N → C)`, is
short exact. The maps are given through the identities characterizing them. -/
theorem shortExact_tensorCross {M N : ModuleCat.{u} R} (f : M ⟶ N) (r : N ⟶ M)
    (hr : f ≫ r = 𝟙 M) {B : ModuleCat.{u} R} (i₁ : M ⊗ cokernel f ⟶ B)
    (i₂ : cokernel f ⊗ M ⟶ B) (p₁ : B ⟶ M ⊗ cokernel f) (p₂ : B ⟶ cokernel f ⊗ M)
    (htot : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 B) (c : B ⟶ cokernel (f ⊗ₘ f))
    (hc₁ : (𝟙 M ⊗ₘ cokernel.π f) ≫ i₁ ≫ c = (f ⊗ₘ 𝟙 N) ≫ cokernel.π (f ⊗ₘ f))
    (hc₂ : (cokernel.π f ⊗ₘ 𝟙 M) ≫ i₂ ≫ c = (𝟙 N ⊗ₘ f) ≫ cokernel.π (f ⊗ₘ f))
    (d : cokernel (f ⊗ₘ f) ⟶ cokernel f ⊗ cokernel f)
    (hd : cokernel.π (f ⊗ₘ f) ≫ d = cokernel.π f ⊗ₘ cokernel.π f) (w : c ≫ d = 0) :
    (ShortComplex.mk c d w).ShortExact := by
  have hex := exact_cokernel_π f
  have hπ := surjective_cokernel_π f
  have : Epi (𝟙 M ⊗ₘ cokernel.π f) := epi_whiskerLeft_cokernel M f
  have : Epi (cokernel.π f ⊗ₘ 𝟙 M) := epi_whiskerRight_cokernel M f
  let ρ : cokernel (f ⊗ₘ f) ⟶ B := cokernel.desc _ ((r ⊗ₘ cokernel.π f) ≫ i₁ +
    (cokernel.π f ⊗ₘ r) ≫ i₂) (by
      rw [Preadditive.comp_add, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc,
        cokernel.condition, MonoidalPreadditive.tensor_zero, MonoidalPreadditive.zero_tensor,
        zero_comp, zero_comp, add_zero])
  have hρ₁ : i₁ ≫ c ≫ ρ = i₁ := by
    rw [← cancel_epi (𝟙 M ⊗ₘ cokernel.π f), reassoc_of% hc₁, cokernel.π_desc,
      Preadditive.comp_add, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc, hr,
      cokernel.condition, MonoidalPreadditive.zero_tensor, zero_comp, add_zero, Category.id_comp]
  have hρ₂ : i₂ ≫ c ≫ ρ = i₂ := by
    rw [← cancel_epi (cokernel.π f ⊗ₘ 𝟙 M), reassoc_of% hc₂, cokernel.π_desc,
      Preadditive.comp_add, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc, hr,
      cokernel.condition, MonoidalPreadditive.tensor_zero, zero_comp, zero_add, Category.id_comp]
  have hcρ : c ≫ ρ = 𝟙 B := by
    rw [← Category.id_comp (c ≫ ρ), ← htot, Preadditive.add_comp, Category.assoc,
      Category.assoc, hρ₁, hρ₂, htot]
  apply ModuleCat.shortComplex_shortExact
  · intro x
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := surjective_cokernel_π _ x
      have hz : z ∈ LinearMap.ker (TensorProduct.map (cokernel.π f).hom (cokernel.π f).hom) := by
        rw [LinearMap.mem_ker]
        exact (congrArg (fun g => g.hom z) hd).symm.trans hx
      rw [TensorProduct.map_ker hex hπ hex hπ, Submodule.mem_sup] at hz
      obtain ⟨a, ⟨a', rfl⟩, b, ⟨b', rfl⟩, rfl⟩ := hz
      refine ⟨i₂.hom ((LinearMap.rTensor M (cokernel.π f).hom) a') +
        i₁.hom ((LinearMap.lTensor M (cokernel.π f).hom) b'), ?_⟩
      show c.hom _ = _
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) (congrArg (fun g => g.hom a') hc₂) (congrArg (fun g => g.hom b') hc₁)
    · rintro ⟨y, rfl⟩
      exact congrArg (fun g => g.hom y) w
  · exact (ModuleCat.mono_iff_injective c).1 (mono_of_mono_fac hcρ)
  · intro y
    obtain ⟨z, rfl⟩ := TensorProduct.map_surjective hπ hπ y
    exact ⟨(cokernel.π (f ⊗ₘ f)).hom z, congrArg (fun g => g.hom z) hd⟩

end ModuleCat


namespace Stacks.SemilinearArrowFunctor

/-! ### The general constructions -/

/-- Evaluation of an arrow at `i : Fin 2`, as a semilinear functor on arrows: its semilinear
structure is the identity. -/
abbrev eval (i : Fin 2) : SemilinearArrowFunctor.{u} where
  obj A := (evaluation (Fin 2) (ModuleCat.{u} A)).obj i
  map φ := 𝟙 _
  map_id A Y := by ext x; rfl
  map_comp φ ψ Z := by ext x; rfl

/-- The source `X₀` of an arrow `X₀ → X₁`. -/
abbrev left : SemilinearArrowFunctor.{u} := eval 0
/-- The target `X₁` of an arrow `X₀ → X₁`. -/
abbrev right : SemilinearArrowFunctor.{u} := eval 1

/-- The arrow itself, as a morphism `left ⟶ right` of semilinear functors. -/
def leftToRight : left.{u} ⟶ right.{u} where
  app _ := ComposableArrows.evaluationHom
  comm _ := rfl

variable {Φ Ψ Θ : SemilinearArrowFunctor.{u}}

/-- The compatibility of a morphism of semilinear functors with the semilinear structures, on an
arrow. -/
@[reassoc]
lemma comm_app (α : Φ ⟶ Ψ) {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (Y : ComposableArrows (ModuleCat.{u} B) 1) :
    (α.app A).app ((restrictScalarsArrow φ.hom).obj Y) ≫ (Ψ.map φ).app Y =
      (Φ.map φ).app Y ≫ (ModuleCat.restrictScalars φ.hom).map ((α.app B).app Y) :=
  NatTrans.congr_app (α.comm φ) Y

/-- The cokernel of a morphism `α : Φ ⟶ Ψ` of semilinear functors on arrows, computed
objectwise; its semilinear structure is induced by that of `Ψ`, restriction of scalars being
exact. -/
abbrev cokernel (α : Φ ⟶ Ψ) : SemilinearArrowFunctor.{u} where
  obj A := NatTrans.cokernelFunctor (α.app A)
  map {A B} φ :=
    { app Y := Limits.cokernel.desc _ ((Ψ.map φ).app Y ≫
          (ModuleCat.restrictScalars φ.hom).map (Limits.cokernel.π ((α.app B).app Y))) (by
        rw [← Category.assoc, comm_app, Category.assoc, ← Functor.map_comp,
          Limits.cokernel.condition, Functor.map_zero, comp_zero])
      naturality Y Y' g := by
        refine coequalizer.hom_ext ?_
        simp only [Functor.comp_obj, Functor.comp_map, NatTrans.cokernelFunctor_obj,
          cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc]
        rw [← Functor.map_comp, cokernel.π_desc, Functor.map_comp]
        exact (Ψ.map φ).naturality_assoc g _ }
  map_id A Y := by
    refine coequalizer.hom_ext ?_
    simp only [NatTrans.cokernelFunctor_obj, Functor.comp_obj, cokernel.π_desc_assoc,
      Category.assoc, cokernel.π_desc]
    rw [reassoc_of% (Ψ.map_id A Y)]
    exact ((ModuleCat.restrictScalarsId' _ rfl).inv.naturality _).symm
  map_comp φ ψ Z := by
    apply coequalizer.hom_ext
    simp only [NatTrans.cokernelFunctor_obj, Functor.comp_obj, cokernel.π_desc_assoc,
      Category.assoc, cokernel.π_desc]
    rw [reassoc_of% (Ψ.map_comp φ ψ Z), ← Functor.map_comp_assoc, cokernel.π_desc,
      Functor.map_comp]
    congr 2


/-- The tensor product `Φ ⊗ Ψ` of semilinear functors on arrows, computed objectwise; its
semilinear structure is the tensor product of those of `Φ` and `Ψ` followed by the lax monoidal
structure of restriction of scalars. -/
abbrev tensor (Φ Ψ : SemilinearArrowFunctor.{u}) : SemilinearArrowFunctor.{u} where
  obj A := Φ.obj A ⊗ Ψ.obj A
  map φ :=
    { app Y := ((Φ.map φ).app Y ⊗ₘ (Ψ.map φ).app Y) ≫
        Functor.LaxMonoidal.μ (ModuleCat.restrictScalars φ.hom) _ _
      naturality Y Y' g := by
        have h₁ := (Φ.map φ).naturality g
        have h₂ := (Ψ.map φ).naturality g
        dsimp only [Functor.comp_obj, Functor.comp_map, Monoidal.tensorObj_obj,
          Monoidal.tensorObj_map] at h₁ h₂ ⊢
        rw [tensorHom_comp_tensorHom_assoc, h₁, h₂,
          ← tensorHom_comp_tensorHom_assoc, Functor.LaxMonoidal.μ_natural, Category.assoc] }
  map_id A Y := by
    dsimp only [Functor.comp_obj, Monoidal.tensorObj_obj, Monoidal.tensorObj_map]
    rw [tensorHom_comp_tensorHom_assoc, Φ.map_id, Ψ.map_id,
      ModuleCat.restrictScalarsId'_inv_tensorHom_comp_μ]
  map_comp φ ψ Z := by
    have h := Functor.LaxMonoidal.μ_natural (ModuleCat.restrictScalars φ.hom)
      ((Φ.map ψ).app Z) ((Ψ.map ψ).app Z)
    dsimp only [Functor.comp_obj, Monoidal.tensorObj_obj, Monoidal.tensorObj_map] at h ⊢
    rw [tensorHom_comp_tensorHom_assoc, Φ.map_comp, Ψ.map_comp, ← tensorHom_comp_tensorHom_assoc,
      ← tensorHom_comp_tensorHom_assoc, ModuleCat.restrictScalarsComp'_inv_tensorHom_comp_μ,
      reassoc_of% h, Functor.map_comp]
    simp only [Category.assoc]


/-- The `n`-th exterior power `⋀ⁿ ∘ Φ` of a semilinear functor on arrows; its semilinear structure
is `⋀ⁿ` of that of `Φ` followed by the comparison `⋀ⁿ_A (φ^* N) ⟶ φ^* ⋀ⁿ_B N`. -/
abbrev exteriorPower (n : ℕ) (Φ : SemilinearArrowFunctor.{u}) : SemilinearArrowFunctor.{u} where
  obj A := Φ.obj A ⋙ ModuleCat.exteriorPower.functor A n
  map {A B} φ :=
    { app Y := (ModuleCat.exteriorPower.functor A n).map ((Φ.map φ).app Y) ≫
        ModuleCat.exteriorPower.restrictScalarsMap φ.hom ((Φ.obj B).obj Y) n
      naturality Y Y' g := by
        have h := (Φ.map φ).naturality g
        dsimp only [Functor.comp_obj, Functor.comp_map] at h ⊢
        rw [← Functor.map_comp_assoc, h, Functor.map_comp_assoc,
          ModuleCat.exteriorPower.map_comp_restrictScalarsMap, Category.assoc] }
  map_id A Y := by
    dsimp only [Functor.comp_obj, Functor.comp_map]
    rw [← Functor.map_comp_assoc, Φ.map_id,
      ModuleCat.exteriorPower.map_restrictScalarsId'_inv_comp_restrictScalarsMap]
  map_comp {A B C} φ ψ Z := by
    have h := ModuleCat.exteriorPower.map_comp_restrictScalarsMap φ.hom
      ((Φ.map ψ).app Z) n
    dsimp only [Functor.comp_obj, Functor.comp_map] at h ⊢
    rw [← Functor.map_comp_assoc, Φ.map_comp, Functor.map_comp, Functor.map_comp,
      Category.assoc, Category.assoc,
      ModuleCat.exteriorPower.map_restrictScalarsComp'_inv_comp_restrictScalarsMap,
      reassoc_of% h]
    simp only [Functor.map_comp, Category.assoc]

/-- The tensor product of two morphisms of semilinear functors on arrows. -/
def tensorHom {Φ' Ψ' : SemilinearArrowFunctor.{u}} (α : Φ ⟶ Φ') (β : Ψ ⟶ Ψ') :
    tensor Φ Ψ ⟶ tensor Φ' Ψ' where
  app A := α.app A ⊗ₘ β.app A
  comm {A B} φ := by
    ext Y : 2
    have h₁ := comm_app α φ Y
    have h₂ := comm_app β φ Y
    dsimp only [tensor, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Monoidal.tensorHom_app, Functor.comp_obj, Monoidal.tensorObj_obj] at h₁ h₂ ⊢
    rw [tensorHom_comp_tensorHom_assoc, h₁, h₂, ← tensorHom_comp_tensorHom_assoc,
      Functor.LaxMonoidal.μ_natural, Category.assoc]

/-- The `n`-th exterior power of a morphism of semilinear functors on arrows. -/
def exteriorPowerMap (n : ℕ) (α : Φ ⟶ Ψ) : exteriorPower n Φ ⟶ exteriorPower n Ψ where
  app A := Functor.whiskerRight (α.app A) (ModuleCat.exteriorPower.functor A n)
  comm {A B} φ := by
    ext Y : 2
    have h := comm_app α φ Y
    dsimp only [exteriorPower, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.comp_obj] at h ⊢
    rw [← Functor.map_comp_assoc, h, Functor.map_comp_assoc,
      ModuleCat.exteriorPower.map_comp_restrictScalarsMap, Category.assoc]

/-- The projection `Ψ ⟶ cokernel α`. -/
abbrev cokernelπ (α : Φ ⟶ Ψ) : Ψ ⟶ cokernel α where
  app A :=
    { app X := Limits.cokernel.π ((α.app A).app X)
      naturality X Y g := by simp }
  comm {A B} φ := by
    ext Y : 2
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    exact Limits.cokernel.π_desc _ _ _

/-- The morphism `cokernel α ⟶ Θ` induced by a morphism `β : Ψ ⟶ Θ` with `α ≫ β = 0`. -/
abbrev cokernelDesc (α : Φ ⟶ Ψ) (β : Ψ ⟶ Θ) (h : ∀ A, α.app A ≫ β.app A = 0) :
    cokernel α ⟶ Θ where
  app A :=
    { app X := Limits.cokernel.desc _ ((β.app A).app X) (NatTrans.congr_app (h A) X)
      naturality X Y g := by
        apply coequalizer.hom_ext
        simp [cokernel] }
  comm {A B} φ := by
    ext Y : 2
    apply coequalizer.hom_ext
    simp only [cokernel, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      cokernel.π_desc_assoc, Category.assoc]
    rw [← Functor.map_comp, cokernel.π_desc]
    exact comm_app β φ Y



/-- The biproduct `Φ ⊞ Ψ` of semilinear functors on arrows; its semilinear structure is the
diagonal matrix of those of `Φ` and `Ψ`. -/
abbrev biprod (Φ Ψ : SemilinearArrowFunctor.{u}) : SemilinearArrowFunctor.{u} where
  obj A := Φ.obj A ⊞ Ψ.obj A
  map {A B} φ :=
    Functor.whiskerLeft (restrictScalarsArrow φ.hom) Limits.biprod.fst ≫ Φ.map φ ≫
        Functor.whiskerRight Limits.biprod.inl (ModuleCat.restrictScalars φ.hom) +
      Functor.whiskerLeft (restrictScalarsArrow φ.hom) Limits.biprod.snd ≫ Ψ.map φ ≫
        Functor.whiskerRight Limits.biprod.inr (ModuleCat.restrictScalars φ.hom)
  map_id A Y := by
    simp only [NatTrans.app_add, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Preadditive.comp_add]
    have h₁ := (biprod.fst : Φ.obj A ⊞ Ψ.obj A ⟶ Φ.obj A).naturality
      ((restrictScalarsArrowId' (CommRingCat.Hom.hom (𝟙 A)) rfl).inv.app Y)
    have h₂ := (biprod.snd : Φ.obj A ⊞ Ψ.obj A ⟶ Ψ.obj A).naturality
      ((restrictScalarsArrowId' (CommRingCat.Hom.hom (𝟙 A)) rfl).inv.app Y)
    have h₃ := (ModuleCat.restrictScalarsId' (CommRingCat.Hom.hom (𝟙 A)) rfl).inv.naturality
      ((biprod.inl : Φ.obj A ⟶ Φ.obj A ⊞ Ψ.obj A).app Y)
    have h₄ := (ModuleCat.restrictScalarsId' (CommRingCat.Hom.hom (𝟙 A)) rfl).inv.naturality
      ((biprod.inr : Ψ.obj A ⟶ Φ.obj A ⊞ Ψ.obj A).app Y)
    rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% (Φ.map_id A Y),
      reassoc_of% (Ψ.map_id A Y), ← h₃, ← h₄, Functor.id_map, Functor.id_map,
      ← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, ← NatTrans.comp_app,
      ← NatTrans.comp_app, ← NatTrans.app_add, biprod.total, NatTrans.id_app, Category.id_comp]
  map_comp {A B C} φ ψ Z := by
    have h₁ := (biprod.fst : Φ.obj A ⊞ Ψ.obj A ⟶ Φ.obj A).naturality
      ((restrictScalarsArrowComp' φ.hom ψ.hom (CommRingCat.Hom.hom (φ ≫ ψ)) rfl).inv.app Z)
    have h₂ := (biprod.snd : Φ.obj A ⊞ Ψ.obj A ⟶ Ψ.obj A).naturality
      ((restrictScalarsArrowComp' φ.hom ψ.hom (CommRingCat.Hom.hom (φ ≫ ψ)) rfl).inv.app Z)
    have h₃ := (ModuleCat.restrictScalarsComp' φ.hom ψ.hom (CommRingCat.Hom.hom (φ ≫ ψ))
      rfl).inv.naturality ((biprod.inl : Φ.obj C ⟶ Φ.obj C ⊞ Ψ.obj C).app Z)
    have h₄ := (ModuleCat.restrictScalarsComp' φ.hom ψ.hom (CommRingCat.Hom.hom (φ ≫ ψ))
      rfl).inv.naturality ((biprod.inr : Ψ.obj C ⟶ Φ.obj C ⊞ Ψ.obj C).app Z)
    simp only [NatTrans.app_add, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
    rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% (Φ.map_comp φ ψ Z),
      reassoc_of% (Ψ.map_comp φ ψ Z), ← h₃, ← h₄]
    simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp,
      ← Functor.map_comp_assoc, reassoc_of% biprod_inl_fst_app, reassoc_of% biprod_inl_snd_app,
      reassoc_of% biprod_inr_fst_app, reassoc_of% biprod_inr_snd_app, zero_comp,
      add_zero, zero_add, Functor.map_zero, Functor.comp_map]


/-- The morphism `Φ ⊞ Ψ ⟶ Θ` induced by morphisms `Φ ⟶ Θ` and `Ψ ⟶ Θ`. -/
def biprodDesc (f : Φ ⟶ Θ) (g : Ψ ⟶ Θ) : biprod Φ Ψ ⟶ Θ where
  app A := Limits.biprod.desc (f.app A) (g.app A)
  comm {A B} φ := by
    ext Y : 2
    have h₁ := comm_app f φ Y
    have h₂ := comm_app g φ Y
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.app_add, Preadditive.add_comp, Category.assoc]
    rw [← Functor.map_comp, ← Functor.map_comp, biprod.inl_desc_app, biprod.inr_desc_app, ← h₁,
      ← h₂, biprod.desc_app, Preadditive.add_comp, Category.assoc, Category.assoc]

/-- The braiding `Φ ⊗ Ψ ⟶ Ψ ⊗ Φ`. -/
def tensorBraiding (Φ Ψ : SemilinearArrowFunctor.{u}) : tensor Φ Ψ ⟶ tensor Ψ Φ where
  app A :=
    { app X := (β_ ((Φ.obj A).obj X) ((Ψ.obj A).obj X)).hom
      naturality X Y g := BraidedCategory.braiding_naturality _ _ }
  comm {A B} φ := by
    ext Y : 2
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    dsimp only [Monoidal.tensorObj_obj, Functor.comp_obj]
    have h := ModuleCat.braiding_hom_comp_μ φ.hom ((Φ.obj B).obj Y) ((Ψ.obj B).obj Y)
    rw [← BraidedCategory.braiding_naturality_assoc, h, Category.assoc]


/-- The braiding `Φ ⊗ Ψ ≅ Ψ ⊗ Φ`. -/
def tensorBraidingIso (Φ Ψ : SemilinearArrowFunctor.{u}) : tensor Φ Ψ ≅ tensor Ψ Φ where
  hom := tensorBraiding Φ Ψ
  inv := tensorBraiding Ψ Φ
  hom_inv_id := hom_ext fun A => NatTrans.ext (funext fun X =>
    SymmetricCategory.symmetry ((Φ.obj A).obj X) ((Ψ.obj A).obj X))
  inv_hom_id := hom_ext fun A => NatTrans.ext (funext fun X =>
    SymmetricCategory.symmetry ((Ψ.obj A).obj X) ((Φ.obj A).obj X))

/-- The wedge map `Φ ⊗ Ψ ⟶ ⋀² Ψ`, `x ⊗ y ↦ α x ∧ y`, of a morphism `α : Φ ⟶ Ψ`. -/
def wedge (α : Φ ⟶ Ψ) : tensor Φ Ψ ⟶ exteriorPower 2 Ψ :=
  tensorHom α (𝟙 Ψ) ≫
    { app A := { app X := ModuleCat.exteriorPower.wedgeMul ((Ψ.obj A).obj X)
                 naturality X Y g := ModuleCat.exteriorPower.tensorHom_comp_wedgeMul _ }
      comm {A B} φ := by
        ext Y : 2
        have h := ModuleCat.exteriorPower.μ_comp_map_wedgeMul φ.hom ((Ψ.obj B).obj Y)
        have h' := ModuleCat.exteriorPower.tensorHom_comp_wedgeMul ((Ψ.map φ).app Y)
        dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
          Functor.comp_obj, Monoidal.tensorObj_obj] at h h' ⊢
        rw [Category.assoc, h, ← reassoc_of% h'] }


/-- The defining property of `cokernelDesc`. -/
@[reassoc (attr := simp)]
lemma cokernelπ_comp_cokernelDesc (α : Φ ⟶ Ψ) (β : Ψ ⟶ Θ) (h : ∀ A, α.app A ≫ β.app A = 0) :
    cokernelπ α ≫ cokernelDesc α β h = β :=
  hom_ext fun _ => NatTrans.ext (funext fun _ => Limits.cokernel.π_desc _ _ _)

/-- `α ≫ cokernelπ α = 0`, componentwise. -/
lemma comp_cokernelπ_app (α : Φ ⟶ Ψ) (A : CommRingCat.{u}) :
    α.app A ≫ (cokernelπ α).app A = 0 :=
  NatTrans.ext (funext fun _ => Limits.cokernel.condition _)

variable {Ξ : SemilinearArrowFunctor.{u}}

/-- The components of `descOfExact`. -/
def descOfExactApp (α : Φ ⟶ Ψ) (β : Ψ ⟶ Θ) (hαβ : ∀ A, α.app A ≫ β.app A = 0)
    (hβ : ∀ A X, (ShortComplex.mk ((α.app A).app X) ((β.app A).app X)
      (NatTrans.congr_app (hαβ A) X)).Exact)
    (hepi : ∀ A X, Epi ((β.app A).app X)) (γ : Ψ ⟶ Ξ) (hγ : ∀ A, α.app A ≫ γ.app A = 0)
    (A : CommRingCat.{u}) : Θ.obj A ⟶ Ξ.obj A where
  app X := haveI := hepi A X; (hβ A X).desc ((γ.app A).app X) (NatTrans.congr_app (hγ A) X)
  naturality X Y g := by
    have := hepi A X
    have := hepi A Y
    rw [← cancel_epi ((β.app A).app X), ← NatTrans.naturality_assoc,
      (hβ A Y).g_desc, (hβ A X).g_desc_assoc]
    exact (γ.app A).naturality g

/-- The defining property of `descOfExactApp`. -/
@[reassoc (attr := simp)]
lemma app_comp_descOfExactApp_app (α : Φ ⟶ Ψ) (β : Ψ ⟶ Θ) (hαβ : ∀ A, α.app A ≫ β.app A = 0)
    (hβ : ∀ A X, (ShortComplex.mk ((α.app A).app X) ((β.app A).app X)
      (NatTrans.congr_app (hαβ A) X)).Exact)
    (hepi : ∀ A X, Epi ((β.app A).app X)) (γ : Ψ ⟶ Ξ) (hγ : ∀ A, α.app A ≫ γ.app A = 0)
    (A : CommRingCat.{u}) (X : ComposableArrows (ModuleCat.{u} A) 1) :
    (β.app A).app X ≫ (descOfExactApp α β hαβ hβ hepi γ hγ A).app X = (γ.app A).app X := by
  have := hepi A X
  exact (hβ A X).g_desc ((γ.app A).app X) _

/-- **Descent along an objectwise cokernel.** If `Φ ⟶ Ψ ⟶ Θ` is objectwise exact with `Ψ ⟶ Θ`
objectwise an epimorphism, a morphism `γ : Ψ ⟶ Ξ` with `α ≫ γ = 0` factors through `Θ`, as a
morphism of semilinear functors. -/
def descOfExact (α : Φ ⟶ Ψ) (β : Ψ ⟶ Θ) (hαβ : ∀ A, α.app A ≫ β.app A = 0)
    (hβ : ∀ A X, (ShortComplex.mk ((α.app A).app X) ((β.app A).app X)
      (NatTrans.congr_app (hαβ A) X)).Exact)
    (hepi : ∀ A X, Epi ((β.app A).app X)) (γ : Ψ ⟶ Ξ) (hγ : ∀ A, α.app A ≫ γ.app A = 0) :
    Θ ⟶ Ξ where
  app := descOfExactApp α β hαβ hβ hepi γ hγ
  comm {A B} φ := by
    refine NatTrans.ext (funext fun Y => ?_)
    have := hepi A ((restrictScalarsArrow φ.hom).obj Y)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [← cancel_epi ((β.app A).app ((restrictScalarsArrow φ.hom).obj Y)),
      app_comp_descOfExactApp_app_assoc, comm_app γ φ Y, comm_app_assoc β φ Y,
      ← Functor.map_comp, app_comp_descOfExactApp_app]

/-- The defining property of `descOfExact`. -/
@[reassoc (attr := simp)]
lemma comp_descOfExact (α : Φ ⟶ Ψ) (β : Ψ ⟶ Θ) (hαβ : ∀ A, α.app A ≫ β.app A = 0)
    (hβ : ∀ A X, (ShortComplex.mk ((α.app A).app X) ((β.app A).app X)
      (NatTrans.congr_app (hαβ A) X)).Exact)
    (hepi : ∀ A X, Epi ((β.app A).app X)) (γ : Ψ ⟶ Ξ) (hγ : ∀ A, α.app A ≫ γ.app A = 0) :
    β ≫ descOfExact α β hαβ hβ hepi γ hγ = γ :=
  hom_ext fun A => NatTrans.ext (funext fun X =>
    app_comp_descOfExactApp_app α β hαβ hβ hepi γ hγ A X)


/-- `exteriorPowerMap` is functorial. -/
lemma exteriorPowerMap_comp (n : ℕ) (α : Φ ⟶ Ψ) (β : Ψ ⟶ Θ) :
    exteriorPowerMap n (α ≫ β) = exteriorPowerMap n α ≫ exteriorPowerMap n β :=
  hom_ext fun A => NatTrans.ext (funext fun X =>
    (ModuleCat.exteriorPower.functor A n).map_comp ((α.app A).app X) ((β.app A).app X))

/-- `tensorHom` is functorial. -/
lemma tensorHom_comp {Φ' Ψ' Φ'' Ψ'' : SemilinearArrowFunctor.{u}} (α : Φ ⟶ Φ') (α' : Φ' ⟶ Φ'')
    (β : Ψ ⟶ Ψ') (β' : Ψ' ⟶ Ψ'') :
    tensorHom (α ≫ α') (β ≫ β') = tensorHom α β ≫ tensorHom α' β' :=
  hom_ext fun _ => NatTrans.ext (funext fun _ => (tensorHom_comp_tensorHom _ _ _ _).symm)

/-! ### The functors -/

/-- The cokernel `coker (X₀ → X₁)` of an arrow. -/
abbrev coker : SemilinearArrowFunctor.{u} := cokernel leftToRight

/-- The cokernel of arrows over `A` is `CategoryTheory.ComposableArrows.cokernelFunctor`. -/
lemma coker_obj (A : CommRingCat.{u}) : coker.obj A = ComposableArrows.cokernelFunctor := rfl

/-- The projection `X₁ ⟶ coker X` of the target onto the cokernel. -/
abbrev rightToCoker : right.{u} ⟶ coker := cokernelπ leftToRight

/-- The cross term `X₀ ⊗ coker X` of an arrow. -/
abbrev cross : SemilinearArrowFunctor.{u} := tensor left coker

/-- The cross term `coker X ⊗ X₀` of an arrow. -/
abbrev crossRev : SemilinearArrowFunctor.{u} := tensor coker left

/-- `D_Λ(X) = coker (⋀² X₀ → ⋀² X₁)` for an arrow `X₀ → X₁`. -/
abbrev relExteriorSquare : SemilinearArrowFunctor.{u} :=
  cokernel (exteriorPowerMap 2 leftToRight)

/-- `D_T(X) = coker (X₀ ⊗ X₀ → X₁ ⊗ X₁)` for an arrow `X₀ → X₁`. -/
abbrev relTensorSquare : SemilinearArrowFunctor.{u} :=
  cokernel (tensorHom leftToRight leftToRight)

/-- The map `D_Λ ⟶ ⋀² coker` induced by `⋀² (X₁ → coker X)`. -/
def relExteriorSquareToCoker : relExteriorSquare.{u} ⟶ exteriorPower 2 coker :=
  cokernelDesc _ (exteriorPowerMap 2 rightToCoker) fun A => NatTrans.ext (funext fun X => by
    change (ModuleCat.exteriorPower.functor A 2).map X.hom ≫
      (ModuleCat.exteriorPower.functor A 2).map (Limits.cokernel.π X.hom) = 0
    rw [← Functor.map_comp, Limits.cokernel.condition,
      ModuleCat.exteriorPower.functor_map_zero two_ne_zero])

/-- The defining property of `relExteriorSquareToCoker`. -/
lemma cokernelπ_comp_relExteriorSquareToCoker :
    cokernelπ _ ≫ relExteriorSquareToCoker.{u} = exteriorPowerMap 2 rightToCoker := by
  unfold relExteriorSquareToCoker
  exact cokernelπ_comp_cokernelDesc _ _ _

/-- The map `D_T ⟶ coker ⊗ coker` induced by `(X₁ → coker X) ⊗ (X₁ → coker X)`. -/
def relTensorSquareToCoker : relTensorSquare.{u} ⟶ tensor coker coker :=
  cokernelDesc _ (tensorHom rightToCoker rightToCoker) fun A => NatTrans.ext (funext fun X => by
    change (X.hom ⊗ₘ X.hom) ≫ (Limits.cokernel.π X.hom ⊗ₘ Limits.cokernel.π X.hom) = 0
    rw [tensorHom_comp_tensorHom, Limits.cokernel.condition, MonoidalPreadditive.zero_tensor])

/-- The defining property of `relTensorSquareToCoker`. -/
lemma cokernelπ_comp_relTensorSquareToCoker :
    cokernelπ _ ≫ relTensorSquareToCoker.{u} = tensorHom rightToCoker rightToCoker := by
  unfold relTensorSquareToCoker
  exact cokernelπ_comp_cokernelDesc _ _ _

/-- The map `X₀ ⊗ coker X ⟶ D_Λ(X)`, `x ⊗ [y] ↦ [x ∧ y]`. -/
def crossToRelExteriorSquare : cross.{u} ⟶ relExteriorSquare :=
  descOfExact (tensorHom (𝟙 left) leftToRight) (tensorHom (𝟙 left) rightToCoker)
    (fun A => NatTrans.ext (funext fun X => by
      change (𝟙 X.left ⊗ₘ X.hom) ≫ (𝟙 X.left ⊗ₘ Limits.cokernel.π X.hom) = 0
      rw [tensorHom_comp_tensorHom, Category.id_comp, Limits.cokernel.condition,
        MonoidalPreadditive.tensor_zero]))
    (fun A X => ModuleCat.exact_whiskerLeft_cokernel X.left X.hom)
    (fun A X => ModuleCat.epi_whiskerLeft_cokernel X.left X.hom)
    (wedge leftToRight ≫ cokernelπ _)
    (fun A => NatTrans.ext (funext fun X =>
      ModuleCat.whiskerLeft_comp_whiskerRight_comp_wedgeMul_comp_π X.hom))


/-- The defining property of `crossToRelExteriorSquare`: `x ⊗ [y] ↦ [x ∧ y]`. -/
@[reassoc (attr := simp)]
lemma tensorHom_comp_crossToRelExteriorSquare :
    tensorHom (𝟙 left) rightToCoker ≫ crossToRelExteriorSquare.{u} =
      wedge leftToRight ≫ cokernelπ _ := by
  unfold crossToRelExteriorSquare
  exact comp_descOfExact _ _ _ _ _ _ _

/-- A relation `α ≫ β = γ` of morphisms of semilinear functors, componentwise. -/
private lemma app_comp_app_eq {α : Φ ⟶ Ψ} {β : Ψ ⟶ Θ} {γ : Φ ⟶ Θ} (h : α ≫ β = γ)
    (A : CommRingCat.{u}) (X : ComposableArrows (ModuleCat.{u} A) 1) :
    (α.app A).app X ≫ (β.app A).app X = (γ.app A).app X :=
  NatTrans.congr_app (congrArg (fun t => Hom.app t A) h) X

/-- The defining property of `crossToRelExteriorSquare`, componentwise. -/
@[reassoc]
lemma tensorHom_app_comp_crossToRelExteriorSquare_app (A : CommRingCat.{u})
    (X : ComposableArrows (ModuleCat.{u} A) 1) :
    ((tensorHom (𝟙 left) rightToCoker).app A).app X ≫ (crossToRelExteriorSquare.app A).app X =
      ((wedge leftToRight ≫ cokernelπ _).app A).app X :=
  app_comp_app_eq tensorHom_comp_crossToRelExteriorSquare A X

/-- The map `X₀ ⊗ coker X ⟶ D_T(X)`, `x ⊗ [y] ↦ [x ⊗ y]`. -/
def crossToRelTensorSquare : cross.{u} ⟶ relTensorSquare :=
  descOfExact (tensorHom (𝟙 left) leftToRight) (tensorHom (𝟙 left) rightToCoker)
    (fun A => NatTrans.ext (funext fun X => by
      change (𝟙 X.left ⊗ₘ X.hom) ≫ (𝟙 X.left ⊗ₘ Limits.cokernel.π X.hom) = 0
      rw [tensorHom_comp_tensorHom, Category.id_comp, Limits.cokernel.condition,
        MonoidalPreadditive.tensor_zero]))
    (fun A X => ModuleCat.exact_whiskerLeft_cokernel X.left X.hom)
    (fun A X => ModuleCat.epi_whiskerLeft_cokernel X.left X.hom)
    (tensorHom leftToRight (𝟙 right) ≫ cokernelπ _)
    (fun A => by
      rw [← comp_app, ← Category.assoc, ← tensorHom_comp, Category.id_comp, Category.comp_id]
      exact comp_cokernelπ_app _ A)

/-- The map `coker X ⊗ X₀ ⟶ D_T(X)`, `[y] ⊗ x ↦ [y ⊗ x]`. -/
def crossRevToRelTensorSquare : crossRev.{u} ⟶ relTensorSquare :=
  descOfExact (tensorHom leftToRight (𝟙 left)) (tensorHom rightToCoker (𝟙 left))
    (fun A => NatTrans.ext (funext fun X => by
      change (X.hom ⊗ₘ 𝟙 X.left) ≫ (Limits.cokernel.π X.hom ⊗ₘ 𝟙 X.left) = 0
      rw [tensorHom_comp_tensorHom, Category.id_comp, Limits.cokernel.condition,
        MonoidalPreadditive.zero_tensor]))
    (fun A X => ModuleCat.exact_whiskerRight_cokernel X.left X.hom)
    (fun A X => ModuleCat.epi_whiskerRight_cokernel X.left X.hom)
    (tensorHom (𝟙 right) leftToRight ≫ cokernelπ _)
    (fun A => by
      rw [← comp_app, ← Category.assoc, ← tensorHom_comp, Category.id_comp, Category.comp_id]
      exact comp_cokernelπ_app _ A)

/-- The defining property of `crossToRelTensorSquare`: `x ⊗ [y] ↦ [x ⊗ y]`. -/
@[reassoc (attr := simp)]
lemma tensorHom_comp_crossToRelTensorSquare :
    tensorHom (𝟙 left) rightToCoker ≫ crossToRelTensorSquare.{u} =
      tensorHom leftToRight (𝟙 right) ≫ cokernelπ _ := by
  unfold crossToRelTensorSquare
  exact comp_descOfExact _ _ _ _ _ _ _

/-- The defining property of `crossToRelTensorSquare`, componentwise. -/
@[reassoc]
lemma tensorHom_app_comp_crossToRelTensorSquare_app (A : CommRingCat.{u})
    (X : ComposableArrows (ModuleCat.{u} A) 1) :
    ((tensorHom (𝟙 left) rightToCoker).app A).app X ≫ (crossToRelTensorSquare.app A).app X =
      ((tensorHom leftToRight (𝟙 right) ≫ cokernelπ _).app A).app X :=
  app_comp_app_eq tensorHom_comp_crossToRelTensorSquare A X

/-- The defining property of `crossRevToRelTensorSquare`: `[y] ⊗ x ↦ [y ⊗ x]`. -/
@[reassoc (attr := simp)]
lemma tensorHom_comp_crossRevToRelTensorSquare :
    tensorHom rightToCoker (𝟙 left) ≫ crossRevToRelTensorSquare.{u} =
      tensorHom (𝟙 right) leftToRight ≫ cokernelπ _ := by
  unfold crossRevToRelTensorSquare
  exact comp_descOfExact _ _ _ _ _ _ _

/-- The defining property of `crossRevToRelTensorSquare`, componentwise. -/
@[reassoc]
lemma tensorHom_app_comp_crossRevToRelTensorSquare_app (A : CommRingCat.{u})
    (X : ComposableArrows (ModuleCat.{u} A) 1) :
    ((tensorHom rightToCoker (𝟙 left)).app A).app X ≫ (crossRevToRelTensorSquare.app A).app X =
      ((tensorHom (𝟙 right) leftToRight ≫ cokernelπ _).app A).app X :=
  app_comp_app_eq tensorHom_comp_crossRevToRelTensorSquare A X

/-- The map `(X₀ ⊗ coker X) ⊞ (coker X ⊗ X₀) ⟶ D_T(X)`. -/
def crossSumToRelTensorSquare : biprod cross.{u} crossRev ⟶ relTensorSquare :=
  biprodDesc crossToRelTensorSquare crossRevToRelTensorSquare

/-- The braiding `X₀ ⊗ coker X ≅ coker X ⊗ X₀`. -/
def crossIsoCrossRev : cross.{u} ≅ crossRev := tensorBraidingIso left coker

/-! ### The composites vanish -/

/-- The composite `cross ⟶ D_Λ ⟶ ⋀² coker` vanishes. -/
lemma crossToRelExteriorSquare_comp_relExteriorSquareToCoker_app (A : CommRingCat.{u}) :
    crossToRelExteriorSquare.app A ≫ relExteriorSquareToCoker.app A = 0 := by
  refine NatTrans.ext (funext fun X => ?_)
  have : Epi (((tensorHom (𝟙 left) rightToCoker).app A).app X) :=
    ModuleCat.epi_whiskerLeft_cokernel X.left X.hom
  rw [NatTrans.comp_app, NatTrans.app_zero,
    ← cancel_epi (((tensorHom (𝟙 left) rightToCoker).app A).app X), comp_zero,
    tensorHom_app_comp_crossToRelExteriorSquare_app_assoc, ← NatTrans.comp_app, ← comp_app,
    Category.assoc, relExteriorSquareToCoker, cokernelπ_comp_cokernelDesc]
  exact ModuleCat.whiskerRight_comp_wedgeMul_comp_map_π X.hom

/-- The composite `cross ⊞ crossRev ⟶ D_T ⟶ coker ⊗ coker` vanishes. -/
lemma crossSumToRelTensorSquare_comp_relTensorSquareToCoker_app (A : CommRingCat.{u}) :
    crossSumToRelTensorSquare.app A ≫ relTensorSquareToCoker.app A = 0 := by
  refine NatTrans.ext (funext fun X => ?_)
  rw [NatTrans.comp_app, NatTrans.app_zero]
  refine biprod.app_hom_ext X ?_ ?_
  · have : Epi (((tensorHom (𝟙 left) rightToCoker).app A).app X) :=
      ModuleCat.epi_whiskerLeft_cokernel X.left X.hom
    rw [comp_zero, crossSumToRelTensorSquare, biprodDesc, biprod.inl_desc_app_assoc,
      ← cancel_epi (((tensorHom (𝟙 left) rightToCoker).app A).app X), comp_zero,
      tensorHom_app_comp_crossToRelTensorSquare_app_assoc, ← NatTrans.comp_app, ← comp_app,
      Category.assoc, relTensorSquareToCoker, cokernelπ_comp_cokernelDesc]
    show (X.hom ⊗ₘ 𝟙 X.right) ≫ (Limits.cokernel.π X.hom ⊗ₘ Limits.cokernel.π X.hom) = 0
    rw [tensorHom_comp_tensorHom, Limits.cokernel.condition, MonoidalPreadditive.zero_tensor]
  · have : Epi (((tensorHom rightToCoker (𝟙 left)).app A).app X) :=
      ModuleCat.epi_whiskerRight_cokernel X.left X.hom
    rw [comp_zero, crossSumToRelTensorSquare, biprodDesc, biprod.inr_desc_app_assoc,
      ← cancel_epi (((tensorHom rightToCoker (𝟙 left)).app A).app X), comp_zero,
      tensorHom_app_comp_crossRevToRelTensorSquare_app_assoc, ← NatTrans.comp_app, ← comp_app,
      Category.assoc, relTensorSquareToCoker, cokernelπ_comp_cokernelDesc]
    show (𝟙 X.right ⊗ₘ X.hom) ≫ (Limits.cokernel.π X.hom ⊗ₘ Limits.cokernel.π X.hom) = 0
    rw [tensorHom_comp_tensorHom, Limits.cokernel.condition, MonoidalPreadditive.tensor_zero]


/-! ### Short exact sequences on projective arrows -/

/-- `Φ ⟶ Ψ ⟶ cokernel α` is short exact at an arrow where `α` is a monomorphism. -/
theorem shortExact_cokernelπ (α : Φ ⟶ Ψ) (A : CommRingCat.{u})
    (X : ComposableArrows (ModuleCat.{u} A) 1) (hX : Mono ((α.app A).app X)) :
    (ShortComplex.mk ((α.app A).app X) (((cokernelπ α).app A).app X)
      (NatTrans.congr_app (comp_cokernelπ_app α A) X)).ShortExact :=
  { exact := ShortComplex.cokernelSequence_exact _
    mono_f := hX
    epi_g := (inferInstance : Epi (Limits.cokernel.π ((α.app A).app X))) }

/-- **`0 → ⋀² P₀ → ⋀² P₁ → D_Λ(P) → 0`** is short exact for a projective arrow `P`: `P₀ → P₁` is
a split monomorphism. -/
theorem shortExact_exteriorSquare (A : CommRingCat.{u})
    (P : ComposableArrows (ModuleCat.{u} A) 1) (hP : Projective P) :
    (ShortComplex.mk (((exteriorPowerMap 2 leftToRight).app A).app P)
      (((cokernelπ (exteriorPowerMap 2 leftToRight)).app A).app P)
      (NatTrans.congr_app (comp_cokernelπ_app _ A) P)).ShortExact := by
  have := ComposableArrows.isSplitMono_hom P
  refine shortExact_cokernelπ _ A P ?_
  exact (IsSplitMono.mk' ⟨(ModuleCat.exteriorPower.functor A 2).map (retraction P.hom), by
    show (ModuleCat.exteriorPower.functor A 2).map P.hom ≫
      (ModuleCat.exteriorPower.functor A 2).map (retraction P.hom) = 𝟙 _
    rw [← Functor.map_comp, IsSplitMono.id, CategoryTheory.Functor.map_id]⟩).mono

/-- **`0 → P₀ ⊗ P₀ → P₁ ⊗ P₁ → D_T(P) → 0`** is short exact for a projective arrow `P`: `P₀ → P₁`
is a split monomorphism. -/
theorem shortExact_tensorSquare (A : CommRingCat.{u})
    (P : ComposableArrows (ModuleCat.{u} A) 1) (hP : Projective P) :
    (ShortComplex.mk (((tensorHom leftToRight leftToRight).app A).app P)
      (((cokernelπ (tensorHom leftToRight leftToRight)).app A).app P)
      (NatTrans.congr_app (comp_cokernelπ_app _ A) P)).ShortExact := by
  have := ComposableArrows.isSplitMono_hom P
  refine shortExact_cokernelπ _ A P ?_
  exact (IsSplitMono.mk' ⟨retraction P.hom ⊗ₘ retraction P.hom, by
    show (P.hom ⊗ₘ P.hom) ≫ (retraction P.hom ⊗ₘ retraction P.hom) = _
    rw [tensorHom_comp_tensorHom, IsSplitMono.id, tensorHom_id, id_whiskerRight]⟩).mono

/-- **`0 → P₀ ⊗ coker P → D_Λ(P) → ⋀² coker P → 0`** is short exact for a projective arrow `P`. -/
theorem shortExact_relExteriorSquare (A : CommRingCat.{u})
    (P : ComposableArrows (ModuleCat.{u} A) 1) (hP : Projective P) :
    (ShortComplex.mk ((crossToRelExteriorSquare.app A).app P)
      ((relExteriorSquareToCoker.app A).app P)
      (NatTrans.congr_app (crossToRelExteriorSquare_comp_relExteriorSquareToCoker_app A)
        P)).ShortExact := by
  have := ComposableArrows.isSplitMono_hom P
  refine ModuleCat.exteriorPower.shortExact_cross P.hom (retraction P.hom) (IsSplitMono.id _) _
    ?_ _ ?_ _
  · exact tensorHom_app_comp_crossToRelExteriorSquare_app A P
  · exact app_comp_app_eq cokernelπ_comp_relExteriorSquareToCoker A P

/-- **`0 → (P₀ ⊗ coker P) ⊞ (coker P ⊗ P₀) → D_T(P) → coker P ⊗ coker P → 0`** is short exact for a
projective arrow `P`. -/
theorem shortExact_relTensorSquare (A : CommRingCat.{u})
    (P : ComposableArrows (ModuleCat.{u} A) 1) (hP : Projective P) :
    (ShortComplex.mk ((crossSumToRelTensorSquare.app A).app P)
      ((relTensorSquareToCoker.app A).app P)
      (NatTrans.congr_app (crossSumToRelTensorSquare_comp_relTensorSquareToCoker_app A)
        P)).ShortExact := by
  have := ComposableArrows.isSplitMono_hom P
  refine ModuleCat.shortExact_tensorCross P.hom (retraction P.hom) (IsSplitMono.id _)
    ((biprod.inl : cross.obj A ⟶ cross.obj A ⊞ crossRev.obj A).app P)
    ((biprod.inr : crossRev.obj A ⟶ cross.obj A ⊞ crossRev.obj A).app P)
    ((biprod.fst : cross.obj A ⊞ crossRev.obj A ⟶ cross.obj A).app P)
    ((biprod.snd : cross.obj A ⊞ crossRev.obj A ⟶ crossRev.obj A).app P) ?_ _ ?_ ?_ _ ?_ _
  · exact biprod_total_app _ _ P
  · exact (congrArg (fun t => ((tensorHom (𝟙 left) rightToCoker).app A).app P ≫ t)
      (biprod.inl_desc_app P _ _)).trans (tensorHom_app_comp_crossToRelTensorSquare_app A P)
  · exact (congrArg (fun t => ((tensorHom rightToCoker (𝟙 left)).app A).app P ≫ t)
      (biprod.inr_desc_app P _ _)).trans (tensorHom_app_comp_crossRevToRelTensorSquare_app A P)
  · exact app_comp_app_eq cokernelπ_comp_relTensorSquareToCoker A P


/-! ### Flat base change -/

/-- The `B`-linear base change morphism `B ⊗_A Φ_A(P) ⟶ Φ_B(B ⊗_A P)`, adjoint to
`Φ.baseChange φ`. -/
abbrev extendScalarsBaseChange (Φ : SemilinearArrowFunctor.{u}) {A B : CommRingCat.{u}}
    (φ : A ⟶ B) (P : ComposableArrows (ModuleCat.{u} A) 1) :
    (ModuleCat.extendScalars φ.hom).obj ((Φ.obj A).obj P) ⟶
      (Φ.obj B).obj ((extendScalarsArrow φ.hom).obj P) :=
  ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).symm ((Φ.baseChange φ).app P)

/-- The base change morphisms are natural in the semilinear functor. -/
lemma baseChange_app_comp (α : Φ ⟶ Ψ) {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (P : ComposableArrows (ModuleCat.{u} A) 1) :
    (Φ.baseChange φ).app P ≫
        (ModuleCat.restrictScalars φ.hom).map ((α.app B).app ((extendScalarsArrow φ.hom).obj P)) =
      (α.app A).app P ≫ (Ψ.baseChange φ).app P := by
  simp only [baseChange, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc]
  rw [← comm_app, ← NatTrans.naturality_assoc]
  rfl

/-- The linearized base change morphisms are natural in the semilinear functor. -/
@[reassoc]
lemma extendScalarsBaseChange_comp (α : Φ ⟶ Ψ) {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (P : ComposableArrows (ModuleCat.{u} A) 1) :
    extendScalarsBaseChange Φ φ P ≫ (α.app B).app ((extendScalarsArrow φ.hom).obj P) =
      (ModuleCat.extendScalars φ.hom).map ((α.app A).app P) ≫ extendScalarsBaseChange Ψ φ P := by
  rw [← Adjunction.homEquiv_naturality_right_symm, ← Adjunction.homEquiv_naturality_left_symm,
    baseChange_app_comp]

/-- `HasFlatBaseChange` in terms of `extendScalarsBaseChange`. -/
lemma hasFlatBaseChange_iff (Φ : SemilinearArrowFunctor.{u}) :
    Φ.HasFlatBaseChange ↔ ∀ ⦃A B : CommRingCat.{u}⦄ (φ : A ⟶ B), φ.hom.Flat →
      ∀ (P : ComposableArrows (ModuleCat.{u} A) 1), Projective P →
        IsIso (extendScalarsBaseChange Φ φ P) :=
  Iff.rfl

/-- Evaluation commutes with base change. -/
lemma hasFlatBaseChange_eval (i : Fin 2) : (eval.{u} i).HasFlatBaseChange := by
  intro A B φ _ P _
  have : ((eval i).baseChange φ).app P =
      (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (P.obj i) := by
    simp [baseChange, extendRestrictScalarsArrowAdj]
  show IsIso (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv (P.obj i) _).symm
    (((eval i).baseChange φ).app P))
  have h : IsIso (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv (P.obj i) _).symm
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (P.obj i))) := by
    rw [← Adjunction.homEquiv_id, Equiv.symm_apply_apply]
    infer_instance
  rw [this]
  exact h


/-- The cokernel of a morphism of semilinear functors which commute with flat base change on
projective arrows commutes with flat base change on projective arrows: `B ⊗_A -` is right
exact, and the five lemma applies. -/
lemma hasFlatBaseChange_cokernel (α : Φ ⟶ Ψ) (hΦ : Φ.HasFlatBaseChange)
    (hΨ : Ψ.HasFlatBaseChange) : (cokernel α).HasFlatBaseChange := by
  intro A B φ hφ P hP
  have hi₁ := hΦ φ hφ P hP
  have hi₂ := hΨ φ hφ P hP
  have : PreservesColimitsOfSize.{u, u} (ModuleCat.extendScalars.{u, u, u} φ.hom) :=
    (ModuleCat.extendRestrictScalarsAdj φ.hom).leftAdjoint_preservesColimits
  have hS := (ShortComplex.cokernelSequence_exact ((α.app A).app P)).map_of_epi_of_preservesCokernel
    (ModuleCat.extendScalars.{u, u, u} φ.hom) inferInstance inferInstance
  have hf₁ := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS
  have hf₂ : Function.Surjective ((ModuleCat.extendScalars.{u, u, u} φ.hom).map
      (Limits.cokernel.π ((α.app A).app P))).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hc₁ := congrArg ModuleCat.Hom.hom (extendScalarsBaseChange_comp α φ P)
  have hc₂ := congrArg ModuleCat.Hom.hom (extendScalarsBaseChange_comp (cokernelπ α) φ P)
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  exact LinearMap.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _ _ _ _ hc₁ hc₂ hf₁
    (ModuleCat.exact_cokernel_π _) ((ConcreteCategory.isIso_iff_bijective _).1 hi₁).2
    ((ConcreteCategory.isIso_iff_bijective _).1 hi₂) hf₂ (ModuleCat.surjective_cokernel_π _)


/-- The linearized base change morphism of a tensor product is the tensor product of those of the
factors, under `B ⊗_A (M ⊗ N) ≅ (B ⊗_A M) ⊗ (B ⊗_A N)`. -/
lemma extendScalarsBaseChange_tensor (Φ Ψ : SemilinearArrowFunctor.{u}) {A B : CommRingCat.{u}}
    (φ : A ⟶ B) (P : ComposableArrows (ModuleCat.{u} A) 1) :
    extendScalarsBaseChange (tensor Φ Ψ) φ P =
      Functor.OplaxMonoidal.δ (ModuleCat.extendScalars φ.hom) _ _ ≫
        (extendScalarsBaseChange Φ φ P ⊗ₘ extendScalarsBaseChange Ψ φ P) := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).injective
  refine (Equiv.apply_symm_apply _ _).trans
    (Eq.trans ?_ (ModuleCat.homEquiv_δ_comp_tensorHom φ.hom _ _).symm)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  simp only [baseChange, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  dsimp only [Functor.comp_obj, Monoidal.tensorObj_obj, Monoidal.tensorObj_map]
  rw [tensorHom_comp_tensorHom_assoc]

/-- A tensor product of semilinear functors commuting with flat base change on projective arrows
commutes with flat base change on projective arrows. -/
lemma hasFlatBaseChange_tensor (hΦ : Φ.HasFlatBaseChange) (hΨ : Ψ.HasFlatBaseChange) :
    (tensor Φ Ψ).HasFlatBaseChange := by
  intro A B φ hφ P hP
  have := hΦ φ hφ P hP
  have := hΨ φ hφ P hP
  show IsIso (extendScalarsBaseChange (tensor Φ Ψ) φ P)
  rw [extendScalarsBaseChange_tensor]
  have h₁ : IsIso (Functor.OplaxMonoidal.δ (ModuleCat.extendScalars φ.hom) ((Φ.obj A).obj P)
    ((Ψ.obj A).obj P)) := inferInstance
  have h₂ : IsIso (extendScalarsBaseChange Φ φ P ⊗ₘ extendScalarsBaseChange Ψ φ P) :=
    inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂


/-- The linearized base change morphism of `⋀ⁿ ∘ Φ` is `⋀ⁿ` of that of `Φ`, under
`B ⊗_A ⋀ⁿ M ≅ ⋀ⁿ (B ⊗_A M)`. -/
lemma extendScalarsBaseChange_exteriorPower (n : ℕ) (Φ : SemilinearArrowFunctor.{u})
    {A B : CommRingCat.{u}} (φ : A ⟶ B) (P : ComposableArrows (ModuleCat.{u} A) 1) :
    extendScalarsBaseChange (exteriorPower n Φ) φ P =
      (ModuleCat.exteriorPower.extendScalarsIso φ.hom n).hom.app ((Φ.obj A).obj P) ≫
        (ModuleCat.exteriorPower.functor B n).map (extendScalarsBaseChange Φ φ P) := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).injective
  refine (Equiv.apply_symm_apply _ _).trans
    (Eq.trans ?_ (ModuleCat.exteriorPower.homEquiv_extendScalarsIso_hom_comp φ.hom _ n).symm)
  rw [Equiv.apply_symm_apply]
  simp only [baseChange, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  rw [Functor.map_comp_assoc]

/-- `⋀ⁿ ∘ Φ` commutes with flat base change on projective arrows if `Φ` does. -/
lemma hasFlatBaseChange_exteriorPower (n : ℕ) (hΦ : Φ.HasFlatBaseChange) :
    (exteriorPower n Φ).HasFlatBaseChange := by
  intro A B φ hφ P hP
  have := hΦ φ hφ P hP
  show IsIso (extendScalarsBaseChange (exteriorPower n Φ) φ P)
  rw [extendScalarsBaseChange_exteriorPower]
  have h₂ : IsIso ((ModuleCat.exteriorPower.functor B n).map (extendScalarsBaseChange Φ φ P)) :=
    inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance h₂


/-- The linearized base change morphism of a biproduct is the diagonal matrix of those of the
summands. -/
lemma extendScalarsBaseChange_biprod (Φ Ψ : SemilinearArrowFunctor.{u})
    {A B : CommRingCat.{u}} (φ : A ⟶ B) (P : ComposableArrows (ModuleCat.{u} A) 1) :
    extendScalarsBaseChange (biprod Φ Ψ) φ P =
      (ModuleCat.extendScalars φ.hom).map ((biprod.fst : Φ.obj A ⊞ Ψ.obj A ⟶ _).app P) ≫
          extendScalarsBaseChange Φ φ P ≫
            (biprod.inl : Φ.obj B ⟶ Φ.obj B ⊞ Ψ.obj B).app _ +
        (ModuleCat.extendScalars φ.hom).map ((biprod.snd : Φ.obj A ⊞ Ψ.obj A ⟶ _).app P) ≫
          extendScalarsBaseChange Ψ φ P ≫
            (biprod.inr : Ψ.obj B ⟶ Φ.obj B ⊞ Ψ.obj B).app _ := by
  have : (ModuleCat.extendScalars.{u, u, u} φ.hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj φ.hom).left_adjoint_additive
  apply ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_add, Preadditive.comp_add,
    ← Adjunction.homEquiv_unit, ← Adjunction.homEquiv_unit,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have h₁ := (biprod.fst : Φ.obj A ⊞ Ψ.obj A ⟶ Φ.obj A).naturality
    ((extendRestrictScalarsArrowAdj φ.hom).unit.app P)
  have h₂ := (biprod.snd : Φ.obj A ⊞ Ψ.obj A ⟶ Ψ.obj A).naturality
    ((extendRestrictScalarsArrowAdj φ.hom).unit.app P)
  simp only [baseChange, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatTrans.app_add, Preadditive.comp_add]
  rw [reassoc_of% h₁, reassoc_of% h₂]
  simp only [Category.assoc]


/-- A biproduct of semilinear functors commuting with flat base change on projective arrows
commutes with flat base change on projective arrows. -/
lemma hasFlatBaseChange_biprod (hΦ : Φ.HasFlatBaseChange) (hΨ : Ψ.HasFlatBaseChange) :
    (biprod Φ Ψ).HasFlatBaseChange := by
  intro A B φ hφ P hP
  have : (ModuleCat.extendScalars.{u, u, u} φ.hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj φ.hom).left_adjoint_additive
  have := hΦ φ hφ P hP
  have := hΨ φ hφ P hP
  show IsIso (extendScalarsBaseChange (biprod Φ Ψ) φ P)
  rw [extendScalarsBaseChange_biprod]
  refine ⟨(biprod.fst : Φ.obj B ⊞ Ψ.obj B ⟶ Φ.obj B).app _ ≫
      inv (extendScalarsBaseChange Φ φ P) ≫
        (ModuleCat.extendScalars φ.hom).map ((biprod.inl : Φ.obj A ⟶ Φ.obj A ⊞ Ψ.obj A).app P) +
    (biprod.snd : Φ.obj B ⊞ Ψ.obj B ⟶ Ψ.obj B).app _ ≫
      inv (extendScalarsBaseChange Ψ φ P) ≫
        (ModuleCat.extendScalars φ.hom).map ((biprod.inr : Ψ.obj A ⟶ Φ.obj A ⊞ Ψ.obj A).app P),
    ?_, ?_⟩
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      reassoc_of% biprod_inl_fst_app, reassoc_of% biprod_inl_snd_app,
      reassoc_of% biprod_inr_fst_app, reassoc_of% biprod_inr_snd_app, zero_comp, comp_zero,
      add_zero, zero_add,
      IsIso.hom_inv_id_assoc, ← Functor.map_comp, ← Functor.map_add, biprod_total_app,
      CategoryTheory.Functor.map_id]
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      ← Functor.map_comp_assoc, biprod_inl_fst_app, biprod_inl_snd_app, biprod_inr_fst_app,
      biprod_inr_snd_app, Functor.map_zero, zero_comp, comp_zero, add_zero, zero_add,
      CategoryTheory.Functor.map_id, Category.id_comp, IsIso.inv_hom_id_assoc, biprod_total_app]


/-- The source commutes with flat base change. -/
lemma hasFlatBaseChange_left : left.{u}.HasFlatBaseChange := hasFlatBaseChange_eval 0

/-- The target commutes with flat base change. -/
lemma hasFlatBaseChange_right : right.{u}.HasFlatBaseChange := hasFlatBaseChange_eval 1

/-- The cokernel commutes with flat base change. -/
lemma hasFlatBaseChange_coker : coker.{u}.HasFlatBaseChange :=
  hasFlatBaseChange_cokernel _ hasFlatBaseChange_left hasFlatBaseChange_right

/-- The cross term `X₀ ⊗ coker X` commutes with flat base change on projective arrows. -/
lemma hasFlatBaseChange_cross : cross.{u}.HasFlatBaseChange :=
  hasFlatBaseChange_tensor hasFlatBaseChange_left hasFlatBaseChange_coker

/-- The cross term `coker X ⊗ X₀` commutes with flat base change on projective arrows. -/
lemma hasFlatBaseChange_crossRev : crossRev.{u}.HasFlatBaseChange :=
  hasFlatBaseChange_tensor hasFlatBaseChange_coker hasFlatBaseChange_left

/-- `D_Λ` commutes with flat base change on projective arrows. -/
lemma hasFlatBaseChange_relExteriorSquare : relExteriorSquare.{u}.HasFlatBaseChange :=
  hasFlatBaseChange_cokernel _ (hasFlatBaseChange_exteriorPower 2 hasFlatBaseChange_left)
    (hasFlatBaseChange_exteriorPower 2 hasFlatBaseChange_right)

/-- `D_T` commutes with flat base change on projective arrows. -/
lemma hasFlatBaseChange_relTensorSquare : relTensorSquare.{u}.HasFlatBaseChange :=
  hasFlatBaseChange_cokernel _ (hasFlatBaseChange_tensor hasFlatBaseChange_left
    hasFlatBaseChange_left) (hasFlatBaseChange_tensor hasFlatBaseChange_right
      hasFlatBaseChange_right)

/-- The sum of the cross terms `(X₀ ⊗ coker X) ⊞ (coker X ⊗ X₀)` commutes with flat base change
on projective arrows. -/
lemma hasFlatBaseChange_crossSum : (biprod cross.{u} crossRev).HasFlatBaseChange :=
  hasFlatBaseChange_biprod hasFlatBaseChange_cross hasFlatBaseChange_crossRev

end Stacks.SemilinearArrowFunctor
