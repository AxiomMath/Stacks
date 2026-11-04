module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineLocalUnconditional

/-!
# Descent of an adequate module along a flat surjection of affines of the site

Let `F` be an adequate sheaf of modules on the big `τ`-site over `S`, and let `f : X ⟶ Y` be a
morphism of the site between objects whose underlying schemes are affine, whose underlying
morphism is flat and surjective. Then the presheaf of abelian groups underlying `F` satisfies
the sheaf condition for the one-member presieve `{f}`. This is the degree-zero part of
[Stacks, Tag 06VL], and it is the singleton descent hypothesis that the fpqc sheaf criterion
`Stacks.Adequate.IsAffineSingletonSheaf` asks for.

## Main results

* `Stacks.Adequate.isSheafFor_singleton_of_isAdequate` — the singleton sheaf condition for an
  adequate sheaf of modules along a flat surjective morphism between affine objects of the site.

## Implementation notes

This module gives, in the vocabulary of the library, the proof of the affine step of
Stacks 06VL; only the chain ending in `affine_isSheafFor` is reproduced here.

The argument is faithfully flat descent of a module, read through the affine-section functor.
Writing `R = Γ(Y, 𝒪)` and `T = Γ(X, 𝒪)`, flatness and surjectivity of the underlying morphism
make `R → T` faithfully flat
(`AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine`). Adequacy of `F`
gives, by `Stacks.Adequate.isAdequate_affineSectionFunctor` ([Stacks, Tag 06VI]) followed by
`AdequateFunctor.moduleValuedFunctorBaseChangeMap_bijective` ([Stacks, Tag 06UW]), that the
affine-section functor of `F` on the `R`-algebras of the site is the base change of its value at
`R`; the private `extensionOfBaseSection` is that identification in the form used here, a map out
of `C ⊗[R] F(Spec R)`, together with its naturality in `C`. Descent of a section then reduces to
the elementary statement that an element of `A ⊗[R] M` with equal images under the two cofaces
into `(A ⊗[R] A) ⊗[R] M` is `1 ⊗ m` for a unique `m`, which is the private
`existsUnique_tensor_of_equal_cofaces`, proved from faithful flatness through the quotient by the
range of `m ↦ 1 ⊗ m`. Finally the given morphism `f` is identified, by
`CategoryTheory.Presieve.isSheafFor_singleton_iff_of_iso`, with the morphism of spectra that the
functor `Stacks.Adequate.affineSpecOver` produces from the structure morphism `R → T`, using that
an affine scheme is isomorphic to the spectrum of its global functions.

Two places need care when `backward.isDefEq.respectTransparency` is left at its default. The additivity of the map `m ↦ b • F.map g m`
inside `extensionOfBaseSection` and the naturality lemma both compare an element of
`F.obj (op (op C))` with one of `(ModuleCat.restrictScalars _).obj (F.obj (op (op C)))`, which
have the same carrier but are not definitionally equal at `implicit` transparency; the
additivity is proved by an explicit `change` to the bundled `ConcreteCategory.hom`, as
`AdequateFunctor.moduleValuedFunctorBaseChangeMap` itself does, and the naturality is proved
from `PresheafOfModules.map_smul` as a term rather than by rewriting with it, with
`ModuleCat.restrictScalars` made `implicit_reducible` for this file. In
`extensionOfBaseSection_bijective` the `Algebra R C` structure that
`AdequateFunctor.moduleValuedFunctorBaseChangeMap` induces from the structure morphism is the
one `RingHom.toAlgebra` builds from `algebraMap`, propositionally but not definitionally the
ambient one, so the two maps are compared by `congr!` with `typeEqs := true`, which turns the
difference into the instance equality `toAlgebra_algebraMap` together with two heterogeneous
equalities of the induced left module structures, discharged by the private
`heq_leftModule_of_algebra_eq`.

## References

* [Stacks Project, Tag 06VL](https://stacks.math.columbia.edu/tag/06VL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u m

namespace Stacks.Adequate

/-! ### Faithfully flat descent for a module-valued functor -/

/-- For an adequate module-valued functor, the transition map along a faithfully flat morphism of
algebras is injective. -/
private theorem injective_map_of_faithfullyFlat_of_isAdequate
    {A : Type*} [CommRing A] {D : Type*} [Category D]
    (ι : D ⥤ CommAlgCat A) (F : AdequateFunctor.ModuleValuedFunctorOn ι)
    (hF : AdequateFunctor.IsAdequate ι F) {X Y : D} (f : X ⟶ Y)
    (hf : RingHom.FaithfullyFlat (ι.map f).hom.toRingHom) :
    Function.Injective (F.map f.op.op) := by
  let : Algebra (ι.obj X) (ι.obj Y) := (ι.map f).hom.toRingHom.toAlgebra
  let : Module.FaithfullyFlat (ι.obj X) (ι.obj Y) := hf
  intro x y hxy
  apply Module.FaithfullyFlat.tensorProduct_mk_injective
    (A := ι.obj X) (B := ι.obj Y) (F.obj (.op (.op X)))
  apply (AdequateFunctor.moduleValuedFunctorBaseChangeMap_bijective ι F hF f hf.flat).1
  change AdequateFunctor.moduleValuedFunctorBaseChangeMap ι F f (TensorProduct.tmul _ 1 x) =
    AdequateFunctor.moduleValuedFunctorBaseChangeMap ι F f (TensorProduct.tmul _ 1 y)
  rwa [AdequateFunctor.moduleValuedFunctorBaseChangeMap_tmul,
    AdequateFunctor.moduleValuedFunctorBaseChangeMap_tmul, one_smul, one_smul]

/-- An element of `A ⊗[R] M` fixed by the comparison with `A ⊗[R] (A ⊗[R] M)` is `1 ⊗ m` for a
unique `m`, when `A` is faithfully flat over `R`. -/
private theorem existsUnique_tensor_one_of_compatible
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module.FaithfullyFlat R A]
    (x : A ⊗[R] M)
    (hx : (1 : A) ⊗ₜ[R] x =
      LinearMap.lTensor A (TensorProduct.mk R A M 1) x) :
    ∃! m : M, (1 : A) ⊗ₜ[R] m = x := by
  let i : M →ₗ[R] A ⊗[R] M := TensorProduct.mk R A M 1
  let Q := LinearMap.range i
  have hqi : Q.mkQ.comp i = 0 := by
    ext m
    exact (Submodule.Quotient.mk_eq_zero Q).mpr ⟨m, rfl⟩
  have hqx : Q.mkQ x = 0 := by
    apply Module.FaithfullyFlat.tensorProduct_mk_injective
      (A := R) (B := A) ((A ⊗[R] M) ⧸ Q)
    change (1 : A) ⊗ₜ[R] Q.mkQ x = (1 : A) ⊗ₜ[R] (0 : (A ⊗[R] M) ⧸ Q)
    have hz : LinearMap.lTensor A Q.mkQ (LinearMap.lTensor A i x) = 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hqi,
        LinearMap.lTensor_zero, LinearMap.zero_apply]
    simpa only [LinearMap.lTensor_tmul, TensorProduct.tmul_zero] using
      (congrArg (LinearMap.lTensor A Q.mkQ) hx).trans hz
  obtain ⟨m, hm⟩ := (Submodule.Quotient.mk_eq_zero Q).mp hqx
  exact ⟨m, hm, fun n hn =>
    Module.FaithfullyFlat.tensorProduct_mk_injective M (hn.trans hm.symm)⟩

/-- An element of `A ⊗[R] M` with equal images under the two cofaces into `(A ⊗[R] A) ⊗[R] M`
is `1 ⊗ m` for a unique `m`, when `A` is faithfully flat over `R`. -/
private theorem existsUnique_tensor_of_equal_cofaces
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module.FaithfullyFlat R A]
    (x : A ⊗[R] M)
    (hx : TensorProduct.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap
        (LinearMap.id : M →ₗ[R] M) x =
      TensorProduct.map (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toLinearMap
        LinearMap.id x) :
    ∃! m : M, (1 : A) ⊗ₜ[R] m = x := by
  have h : TensorProduct.assoc R A A M
      (TensorProduct.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toLinearMap
        (LinearMap.id : M →ₗ[R] M) x) =
      LinearMap.lTensor A (TensorProduct.mk R A M 1) x ∧
    TensorProduct.assoc R A A M
      (TensorProduct.map (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toLinearMap
        (LinearMap.id : M →ₗ[R] M) x) = (1 : A) ⊗ₜ[R] x := by
    clear hx
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, TensorProduct.tmul_zero, and_self]
    | tmul b m => exact ⟨rfl, rfl⟩
    | add x y hx hy =>
      simp only [map_add, TensorProduct.tmul_add, hx.1, hy.1, hx.2, hy.2, and_self]
  exact existsUnique_tensor_one_of_compatible x (by rw [← h.2, ← hx, h.1])

/-- The left module structure of `A ⊗[R] N` over `A` depends on the `R`-algebra structure of `A`
only through that structure itself. -/
private theorem heq_leftModule_of_algebra_eq {R A N : Type*} [CommRing R] [CommRing A]
    [AddCommGroup N] [Module R N] {i₁ i₂ : Algebra R A} (h : i₁ = i₂) :
    (letI := i₁; (TensorProduct.leftModule : Module A (A ⊗[R] N))) ≍
      (letI := i₂; (TensorProduct.leftModule : Module A (A ⊗[R] N))) := by
  subst h
  rfl

/-! ### The affine-section functor as a base change of its value at the base algebra -/

/-- The canonical map `C ⊗[R] F(R) → F(C)` of a module-valued functor on the `R`-algebras of the
site, for `C` an algebra of the site. -/
@[implicit_reducible]
private noncomputable def extensionOfBaseSection {R : Type*} [CommRing R]
    (P : ObjectProperty Scheme) (hR : P (Spec (CommRingCat.of R)))
    (F : AdequateFunctor.ModuleValuedFunctorOn (AdequateFunctor.siteAlgebraInclusion R P))
    (Y : AdequateFunctor.AlgebrasInSite R P) :
    Y.obj ⊗[R] F.obj (op (op (baseAlgebra P hR))) →ₗ[Y.obj] F.obj (op (op Y)) := by
  letI : Module R (F.obj (op (op Y))) := Module.compHom _ (algebraMap R Y.obj)
  letI : IsScalarTower R Y.obj (F.obj (op (op Y))) :=
    IsScalarTower.of_algebraMap_smul fun _ => congrFun rfl
  exact TensorProduct.AlgebraTensorModule.lift {
    toFun := fun b => {
      toFun := fun m => b • F.map (baseAlgebraHom P hR Y).op.op m
      map_add' := by
        intro x y
        change b • (F.map (baseAlgebraHom P hR Y).op.op).hom (x + y) =
          b • (F.map (baseAlgebraHom P hR Y).op.op).hom x +
            b • (F.map (baseAlgebraHom P hR Y).op.op).hom y
        rw [map_add (F.map (baseAlgebraHom P hR Y).op.op).hom, smul_add]
      map_smul' := by
        intro r m
        rw [F.map_smul]
        change b • ((algebraMap R Y.obj r) • F.map (baseAlgebraHom P hR Y).op.op m) =
          (algebraMap R Y.obj r) • (b • F.map (baseAlgebraHom P hR Y).op.op m)
        exact smul_comm _ _ _ }
    map_add' := fun _ _ => LinearMap.ext fun _ => add_smul _ _ _
    map_smul' := fun _ _ => LinearMap.ext fun _ => mul_smul _ _ _ }

/-- `Stacks.Adequate.extensionOfBaseSection` on a pure tensor. -/
private theorem extensionOfBaseSection_tmul {R : Type*} [CommRing R]
    (P : ObjectProperty Scheme) (hR : P (Spec (CommRingCat.of R)))
    (F : AdequateFunctor.ModuleValuedFunctorOn (AdequateFunctor.siteAlgebraInclusion R P))
    (Y : AdequateFunctor.AlgebrasInSite R P) (b : Y.obj)
    (m : F.obj (op (op (baseAlgebra P hR)))) :
    extensionOfBaseSection P hR F Y (b ⊗ₜ[R] m) =
      b • F.map (baseAlgebraHom P hR Y).op.op m :=
  rfl

/-- For an adequate module-valued functor and a flat algebra `C` of the site, the canonical map
`C ⊗[R] F(R) → F(C)` is bijective. -/
private theorem extensionOfBaseSection_bijective {R : Type*} [CommRing R]
    (P : ObjectProperty Scheme) (hR : P (Spec (CommRingCat.of R)))
    (F : AdequateFunctor.ModuleValuedFunctorOn (AdequateFunctor.siteAlgebraInclusion R P))
    (hF : AdequateFunctor.IsAdequate (AdequateFunctor.siteAlgebraInclusion R P) F)
    (Y : AdequateFunctor.AlgebrasInSite R P) [Module.Flat R Y.obj] :
    Function.Bijective (extensionOfBaseSection P hR F Y) := by
  have hf : RingHom.Flat ((AdequateFunctor.siteAlgebraInclusion R P).map
      (baseAlgebraHom P hR Y)).hom.toRingHom := by
    change RingHom.Flat (algebraMap R Y.obj)
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have e := AdequateFunctor.moduleValuedFunctorBaseChangeMap_bijective
    (AdequateFunctor.siteAlgebraInclusion R P) F hF (baseAlgebraHom P hR Y) hf
  dsimp +instances only [AdequateFunctor.moduleValuedFunctorBaseChangeMap,
    baseAlgebraHom, baseAlgebra, AdequateFunctor.siteAlgebraInclusion,
    ObjectProperty.ι_map, ObjectProperty.ι_obj, ObjectProperty.homMk_hom, CommAlgCat.hom_ofHom,
    Algebra.ofId] at e
  unfold extensionOfBaseSection
  dsimp +instances only [baseAlgebra]
  convert e using 1 <;> congr! (config := { typeEqs := true }) 4 <;>
    first
      | simp +instances only [toAlgebra_algebraMap]
      | exact heq_leftModule_of_algebra_eq toAlgebra_algebraMap
      | exact heq_leftModule_of_algebra_eq toAlgebra_algebraMap.symm

attribute [local implicit_reducible] ModuleCat.restrictScalars

/-- `Stacks.Adequate.extensionOfBaseSection` is natural in the algebra of the site. -/
private theorem extensionOfBaseSection_naturality {R : Type*} [CommRing R]
    (P : ObjectProperty Scheme) (hR : P (Spec (CommRingCat.of R)))
    (F : AdequateFunctor.ModuleValuedFunctorOn (AdequateFunctor.siteAlgebraInclusion R P))
    {Y Z : AdequateFunctor.AlgebrasInSite R P} (f : Y ⟶ Z)
    (x : Y.obj ⊗[R] F.obj (op (op (baseAlgebra P hR)))) :
    F.map f.op.op (extensionOfBaseSection P hR F Y x) =
      extensionOfBaseSection P hR F Z
        (TensorProduct.map f.hom.hom.toLinearMap LinearMap.id x) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero, map_zero]
    exact (map_zero _).symm
  | tmul b m =>
    have e : F.map f.op.op (F.map (baseAlgebraHom P hR Y).op.op m) =
        F.map (baseAlgebraHom P hR Z).op.op m := by
      rw [← F.map_comp_apply, ← op_comp, ← op_comp, baseAlgebraHom_comp]
    exact (F.map_smul f.op.op b (F.map (baseAlgebraHom P hR Y).op.op m)).trans
      (congrArg (fun z => f.hom.hom b • z) e)
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]
    exact (map_add _ _ _).symm

/-- Descent of a section of an adequate module-valued functor along a faithfully flat algebra of
the site whose self-tensor-square also belongs to the site. -/
private theorem existsUnique_descent_of_isAdequate
    {R : Type*} [CommRing R]
    (P : ObjectProperty Scheme) (hR : P (Spec (CommRingCat.of R)))
    (F : AdequateFunctor.ModuleValuedFunctorOn (AdequateFunctor.siteAlgebraInclusion R P))
    (hF : AdequateFunctor.IsAdequate (AdequateFunctor.siteAlgebraInclusion R P) F)
    (Y : AdequateFunctor.AlgebrasInSite R P) [Module.FaithfullyFlat R Y.obj]
    (hYY : P (Spec (CommRingCat.of (Y.obj ⊗[R] Y.obj))))
    (x : F.obj (op (op Y)))
    (hx : F.map (ObjectProperty.homMk
        (CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft : Y.obj →ₐ[R] Y.obj ⊗[R] Y.obj)) :
          Y ⟶ (⟨CommAlgCat.of R (Y.obj ⊗[R] Y.obj), hYY⟩ :
            AdequateFunctor.AlgebrasInSite R P)).op.op x =
      F.map (ObjectProperty.homMk
        (CommAlgCat.ofHom (Algebra.TensorProduct.includeRight : Y.obj →ₐ[R] Y.obj ⊗[R] Y.obj)) :
          Y ⟶ (⟨CommAlgCat.of R (Y.obj ⊗[R] Y.obj), hYY⟩ :
            AdequateFunctor.AlgebrasInSite R P)).op.op x) :
    ∃! m : F.obj (op (op (baseAlgebra P hR))),
      F.map (baseAlgebraHom P hR Y).op.op m = x := by
  let Z : AdequateFunctor.AlgebrasInSite R P := ⟨CommAlgCat.of R (Y.obj ⊗[R] Y.obj), hYY⟩
  let i₁ : Y ⟶ Z := ObjectProperty.homMk (CommAlgCat.ofHom Algebra.TensorProduct.includeLeft)
  let i₂ : Y ⟶ Z := ObjectProperty.homMk (CommAlgCat.ofHom Algebra.TensorProduct.includeRight)
  obtain ⟨z, hz⟩ := (extensionOfBaseSection_bijective P hR F hF Y).2 x
  have hc : TensorProduct.map i₁.hom.hom.toLinearMap LinearMap.id z =
      TensorProduct.map i₂.hom.hom.toLinearMap LinearMap.id z := by
    apply (extensionOfBaseSection_bijective P hR F hF Z).1
    rwa [← extensionOfBaseSection_naturality, ← extensionOfBaseSection_naturality, hz]
  obtain ⟨m, hm, _⟩ := existsUnique_tensor_of_equal_cofaces z hc
  have hm' : F.map (baseAlgebraHom P hR Y).op.op m = x := by
    calc
      _ = extensionOfBaseSection P hR F Y ((1 : Y.obj) ⊗ₜ[R] m) := by
        rw [extensionOfBaseSection_tmul, one_smul]
      _ = x := by rw [hm, hz]
  refine ⟨m, hm', fun m' hm'' => ?_⟩
  have hff : RingHom.FaithfullyFlat ((AdequateFunctor.siteAlgebraInclusion R P).map
      (baseAlgebraHom P hR Y)).hom.toRingHom := by
    change RingHom.FaithfullyFlat (algebraMap R Y.obj)
    exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  exact injective_map_of_faithfullyFlat_of_isAdequate
    (AdequateFunctor.siteAlgebraInclusion R P) F hF _ hff (hm''.trans hm'.symm)

/-! ### The singleton sheaf condition -/

/-- The global functions of a flat surjective morphism of affine objects of the site form a
faithfully flat ring map. -/
theorem faithfullyFlat_appTop_of_bigSite_map
    {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S)
    {X Y : B.category} (f : X ⟶ Y)
    (hX : IsAffine ((B.toOver.obj X).left))
    (hY : IsAffine ((B.toOver.obj Y).left))
    [Flat ((B.toOver.map f).left)] [Surjective ((B.toOver.map f).left)] :
    ((B.toOver.map f).left.appTop).hom.FaithfullyFlat :=
  (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine
    ((B.toOver.map f).left)).mp ⟨inferInstance, inferInstance⟩

/-- A morphism of affine schemes is the spectrum of its map of global functions, conjugated by
the canonical isomorphisms with the spectra of those. -/
private theorem eq_isoSpec_specMap_isoSpec {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) :
    f = X.isoSpec.hom ≫ Spec.map (f.appTop) ≫ Y.isoSpec.inv := by
  rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
  simp

/-- The spectrum of the global functions of an affine object of the site again lies below the
cutoff. -/
private theorem schemeSizeBelow_spec_appTop
    {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) {X : B.category}
    (hX : IsAffine ((B.toOver.obj X).left)) :
    schemeSizeBelow B.cutoff
      (Spec (CommRingCat.of (Γ((B.toOver.obj X).left, ⊤)))) :=
  ObjectProperty.prop_of_iso (schemeSizeBelow B.cutoff)
    (B.toOver.obj X).left.isoSpec X.left.property

/-- The singleton sheaf condition for the morphism of spectra attached to a faithfully flat
algebra of the site. -/
private theorem isSheafFor_singleton_affineSpecOver
    {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (F : SheafOfModules.{max u m} B.structureSheaf)
    (hF : Stacks.Adequate.IsAdequate B F)
    (R : CommRingCat.{u}) (g : Spec R ⟶ S)
    (hR : schemeSizeBelow B.cutoff (Spec R))
    (Y : AdequateFunctor.AlgebrasInSite R (schemeSizeBelow B.cutoff))
    [Module.FaithfullyFlat R Y.obj] :
    Presieve.IsSheafFor (F.val.presheaf ⋙ forget AddCommGrpCat.{max u m})
      (.singleton ((affineSpecOver B R g).map
        (baseAlgebraHom (schemeSizeBelow B.cutoff) hR Y).op)) := by
  let P := schemeSizeBelow B.cutoff
  let G := affineSpecOver B R g
  let F' := affineSectionFunctor B F R g
  have hF' := isAdequate_affineSectionFunctor.{u, m} B F hF R g hR
  have hYY : P (Spec (CommRingCat.of (Y.obj ⊗[R] Y.obj))) :=
    ObjectProperty.prop_of_iso P (pullbackSpecIso R Y.obj Y.obj)
      (Scheme.size_pullback_lt _ _ Y.property Y.property)
  let Z : AdequateFunctor.AlgebrasInSite R P := ⟨CommAlgCat.of R (Y.obj ⊗[R] Y.obj), hYY⟩
  let i₁ : Y ⟶ Z := ObjectProperty.homMk (CommAlgCat.ofHom Algebra.TensorProduct.includeLeft)
  let i₂ : Y ⟶ Z := ObjectProperty.homMk (CommAlgCat.ofHom Algebra.TensorProduct.includeRight)
  rw [Presieve.isSheafFor_singleton]
  intro x hx
  apply existsUnique_descent_of_isAdequate P hR F' hF' Y hYY x
  apply hx (G.map i₁.op) (G.map i₂.op)
  rw [← G.map_comp, ← G.map_comp, ← op_comp, ← op_comp,
    baseAlgebraHom_comp, baseAlgebraHom_comp]

/-- The singleton sheaf condition is invariant under composing the morphism with an isomorphism
of its target. -/
private theorem isSheafFor_singleton_comp_iso
    {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type*)
    {X Y Z : C} (f : X ⟶ Y) (e : Y ≅ Z)
    (hf : Presieve.IsSheafFor P (.singleton f)) :
    Presieve.IsSheafFor P (.singleton (f ≫ e.hom)) := by
  rw [Presieve.isSheafFor_singleton] at hf ⊢
  intro x hx
  obtain ⟨y, hy, hu⟩ := hf x (fun p q hpq => hx p q (by simp [← Category.assoc, hpq]))
  refine ⟨P.map e.inv.op y, ?_, fun z hz => ?_⟩
  · dsimp only
    rw [← Functor.map_comp_apply, ← op_comp]
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hy
  · have hz' : P.map f.op (P.map e.hom.op z) = x := by
      simpa only [op_comp, Functor.map_comp_apply] using hz
    have heq : P.map e.hom.op z = y := (hu _ hz').trans (hu _ hy).symm
    simpa only [← Functor.map_comp_apply, ← op_comp,
      Iso.inv_hom_id, op_id, Functor.map_id_apply] using congrArg (P.map e.inv.op) heq

/-- **The singleton sheaf condition of [Stacks, Tag 06VL].** Let `F` be an adequate sheaf of
modules on a chosen big `τ`-site over `S`, and let `f : X ⟶ Y` be a morphism of the site whose
source and target have affine underlying schemes and whose underlying morphism of schemes is flat
and surjective. Then the presheaf of abelian groups underlying `F` satisfies the sheaf condition
for the one-member presieve `{f}`.

Writing `R = Γ(Y, 𝒪)` and `T = Γ(X, 𝒪)`, the morphism `f` is the spectrum of the faithfully flat
ring map `R → T`, and the conclusion is faithfully flat descent of a module along it, read through
the affine-section functor of `F` by [Stacks, Tag 06VI] and [Stacks, Tag 06UW]. -/
public theorem isSheafFor_singleton_of_isAdequate
    {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) (F : SheafOfModules.{max u m} B.structureSheaf)
    (hF : Stacks.Adequate.IsAdequate B F)
    {X Y : B.category} (f : X ⟶ Y)
    (hX : IsAffine ((B.toOver.obj X).left))
    (hY : IsAffine ((B.toOver.obj Y).left))
    [Flat ((B.toOver.map f).left)] [Surjective ((B.toOver.map f).left)] :
    Presieve.IsSheafFor (F.val.presheaf ⋙ forget AddCommGrpCat.{max u m})
      (.singleton f) := by
  classical
  let φ := ((B.toOver.map f).left.appTop).hom
  let R := Γ((B.toOver.obj Y).left, ⊤)
  let T := Γ((B.toOver.obj X).left, ⊤)
  let : Algebra R T := φ.toAlgebra
  let : Algebra R R := Algebra.id R
  let : Module.FaithfullyFlat R T := faithfullyFlat_appTop_of_bigSite_map B f hX hY
  let P := schemeSizeBelow B.cutoff
  let g : Spec (CommRingCat.of R) ⟶ S :=
    (B.toOver.obj Y).left.isoSpec.inv ≫ (B.toOver.obj Y).hom
  let yAlg : AdequateFunctor.AlgebrasInSite R P :=
    ⟨CommAlgCat.of R R, schemeSizeBelow_spec_appTop B hY⟩
  let xAlg : AdequateFunctor.AlgebrasInSite R P :=
    ⟨CommAlgCat.of R T, schemeSizeBelow_spec_appTop B hX⟩
  let q : yAlg ⟶ xAlg := ObjectProperty.homMk
    (CommAlgCat.ofHom (Algebra.ofId R T))
  let G := affineSpecOver B (CommRingCat.of R) g
  let eY : Y ≅ G.obj (.op yAlg) := Over.isoMk
    (P.isoMk (B.toOver.obj Y).left.isoSpec) (by
      apply ObjectProperty.hom_ext
      change (B.toOver.obj Y).left.isoSpec.hom ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R R)) ≫ g) = (B.toOver.obj Y).hom
      rw [show CommRingCat.ofHom (algebraMap R R) = 𝟙 (CommRingCat.of R) from rfl,
        Spec.map_id]
      simp only [g]
      exact Iso.hom_inv_id_assoc _ _)
  let eX : X ≅ G.obj (.op xAlg) := Over.isoMk
    (P.isoMk (B.toOver.obj X).left.isoSpec) (by
      apply ObjectProperty.hom_ext
      change (B.toOver.obj X).left.isoSpec.hom ≫
        (Spec.map ((B.toOver.map f).left.appTop) ≫ g) = (B.toOver.obj X).hom
      rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
      simp only [g, Category.assoc, Iso.hom_inv_id_assoc]
      exact (B.toOver.map f).w)
  have hw : f = eX.hom ≫ G.map q.op ≫ eY.inv := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact eq_isoSpec_specMap_isoSpec ((B.toOver.map f).left)
  apply (Presieve.isSheafFor_singleton_iff_of_iso f
    (G.map q.op ≫ eY.inv) eX hw.symm).mpr
  apply isSheafFor_singleton_comp_iso _ _ eY.symm
  exact isSheafFor_singleton_affineSpecOver.{u, m} B F hF (CommRingCat.of R) g
    (schemeSizeBelow_spec_appTop B hY) xAlg

end Stacks.Adequate

end
