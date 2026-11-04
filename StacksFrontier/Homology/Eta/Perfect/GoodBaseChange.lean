module

public import StacksFrontier.Homology.Eta.Complex
public import StacksFrontier.Homology.Eta.Derived
public import StacksFrontier.Homology.Eta.Perfect.LocallyFree

/-!
# Base change of the Berthelot--Ogus décalage at the ring level

Let `A → B` be a map of commutative rings, let `f ∈ A` and let `g = algebraMap A B f`.  For a
cochain complex `K` of `A`-modules this file builds the canonical comparison chain map

`B ⊗_A (η_f K) ⟶ η_g (B ⊗_A K)`

and proves it is natural in `K`.

## Main definitions

* `Stacks.Eta.GoodBaseChange.baseChangeComplex`: the complex `B ⊗_A K` of `B`-modules.
* `Stacks.Eta.GoodBaseChange.psiTermMap`: the degreewise comparison attached to a bare
  differential.
* `Stacks.Eta.GoodBaseChange.etaBaseChangeMap`: the comparison chain map.
* `Stacks.Eta.GoodBaseChange.liftTorsionFree`: a complex of `A`-modules with `f`-torsion-free
  terms, read in the full subcategory of `f`-torsion-free modules.

## Main results

* `Stacks.Eta.GoodBaseChange.etaBaseChangeMap_naturality`: naturality in `K`.
* `Stacks.Eta.GoodBaseChange.quasiIso_etaMap`: Tag 0F7Q restated at `EtaComplex.etaObject`.
* `Stacks.Eta.GoodBaseChange.isIso_etaBaseChangeMap_toCochainComplex`: Tag 0F7X — the
  comparison is an isomorphism of complexes on a bounded complex of finite free modules whose
  determinantal ideals are principal.
* `Stacks.Eta.GoodBaseChange.quasiIso_etaBaseChangeMap_comp_of_toCochainComplex`: the good
  base-change lemma at `P = η_f C`, granted that `B ⊗ ψ` is a quasi-isomorphism.

## Implementation notes

The décalage used here is `EtaComplex.etaObject`, which is defined for an arbitrary cochain complex
of `A`-modules. The other packaging in `StacksFrontier.Homology.Eta.Derived`,
`Stacks.Eta.DerivedFunctor.etaComplex`, lives on the full subcategory of complexes of
`f`-torsion-free modules and therefore cannot be applied to a complex of `A`-modules without first
lifting it to that subcategory.

The ambient comparison on localizations is `Stacks.Eta.BaseChange.psiEquiv`, and the fact that
it carries the degree-`i` décalage term into the degree-`i` décalage term of the base change is
`Stacks.Eta.BaseChange.etaBaseChangeTerm_le_fetaTerm`.  No flatness is needed for this.

The base-changed complex is built directly from `B ⊗[A] -` for the ambient `Algebra A B`
instance rather than from `ModuleCat.extendScalars`, so that it matches the spelling of
`Stacks.Eta.BaseChange` verbatim.

## References

* [Stacks Project, Tag 0F7X](https://stacks.math.columbia.edu/tag/0F7X)
* [Stacks Project, Tag 0F7Q](https://stacks.math.columbia.edu/tag/0F7Q)
* [Stacks Project, Tag 0F7W](https://stacks.math.columbia.edu/tag/0F7W)
* [Stacks Project, Tag 0GSR](https://stacks.math.columbia.edu/tag/0GSR)
-/


@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace Stacks.Eta.GoodBaseChange

noncomputable section

open EtaPow Stacks.Eta.BaseChange

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-! ## Base change of a complex -/

/-- The base change `B ⊗_A K` of a cochain complex of `A`-modules, as a cochain complex of
`B`-modules.  Its differentials are the base-changed differentials of `K`. -/
def baseChangeComplex (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    CochainComplex (ModuleCat.{u} B) ℤ where
  X i := ModuleCat.of B (B ⊗[A] (K.X i : Type u))
  d i j := ModuleCat.ofHom (LinearMap.baseChange B (K.d i j).hom)
  shape i j hij := by
    have h : (K.d i j).hom = 0 := by rw [K.shape i j hij]; rfl
    simp [h]
  d_comp_d' i j k _ _ := by
    rw [← ModuleCat.ofHom_comp, ← LinearMap.baseChange_comp,
      Stacks.Eta.BaseChange.d_hom_comp_d_hom K i j k, LinearMap.baseChange_zero,
      ModuleCat.ofHom_zero]

/-- The `i`-th term of `baseChangeComplex K` is `B ⊗_A K^i`. -/
theorem baseChangeComplex_X (K : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (baseChangeComplex (B := B) K).X i = ModuleCat.of B (B ⊗[A] (K.X i : Type u)) := rfl

/-- The differentials of `baseChangeComplex K` are the base changes of the differentials of `K`. -/
theorem baseChangeComplex_d (K : CochainComplex (ModuleCat.{u} A) ℤ) (i j : ℤ) :
    (baseChangeComplex (B := B) K).d i j =
      ModuleCat.ofHom (LinearMap.baseChange B (K.d i j).hom) := rfl

/-- The base change of a map of complexes. -/
def baseChangeMap {K L : CochainComplex (ModuleCat.{u} A) ℤ} (φ : K ⟶ L) :
    baseChangeComplex (B := B) K ⟶ baseChangeComplex (B := B) L where
  f i := ModuleCat.ofHom (LinearMap.baseChange B (φ.f i).hom)
  comm' i j _ := by
    have h : (L.d i j).hom.comp (φ.f i).hom = (φ.f j).hom.comp (K.d i j).hom := by
      ext y
      simpa only [ModuleCat.hom_comp] using ConcreteCategory.congr_hom (φ.comm i j) y
    apply ModuleCat.hom_ext
    change LinearMap.baseChange B (L.d i j).hom ∘ₗ LinearMap.baseChange B (φ.f i).hom =
      LinearMap.baseChange B (φ.f j).hom ∘ₗ LinearMap.baseChange B (K.d i j).hom
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h]

/-- The `i`-th component of `baseChangeMap φ` is the base change of `φ.f i`. -/
theorem baseChangeMap_f {K L : CochainComplex (ModuleCat.{u} A) ℤ} (φ : K ⟶ L) (i : ℤ) :
    (baseChangeMap (B := B) φ).f i = ModuleCat.ofHom (LinearMap.baseChange B (φ.f i).hom) := rfl

/-! ## The ambient comparison intertwines the localized differentials -/

/-- The localization--base-change isomorphism `Stacks.Eta.BaseChange.psiEquiv` intertwines the
base change of a localized map with the localization of its base change. -/
theorem fLoc_psiEquiv (f : A) {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (d : M →ₗ[A] N) (z : B ⊗[A] Loc f M) :
    fLoc (algebraMap A B f) (LinearMap.baseChange B d) (psiEquiv (B := B) f M z) =
      psiEquiv (B := B) f N (LinearMap.baseChange B (fLoc f d) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b z =>
      have hbz : (b ⊗ₜ[A] z : B ⊗[A] Loc f M) = b • ((1 : B) ⊗ₜ[A] z) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hbz, map_smul, map_smul, ← etaBCPsi_eq_psiEquiv, map_smul, ← etaBCPsi_fLoc f d z,
        map_smul, LinearMap.baseChange_tmul, ← etaBCPsi_eq_psiEquiv]
  | add z w hz hw => rw [map_add, map_add, map_add, map_add, hz, hw]

/-- The square comparing a restriction of the localized map `fLoc f d` to submodules with the
same restriction after base change, read through `Stacks.Eta.BaseChange.psiEquiv`. -/
theorem psiEquiv_baseChange_restriction (f : A) {M N : Type u}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (d : M →ₗ[A] N)
    {W : Submodule A (Loc f M)} {V : Submodule A (Loc f N)} (D : W →ₗ[A] V)
    (hD : V.subtype.comp D = (fLoc f d).comp W.subtype) (y : B ⊗[A] W) :
    psiEquiv (B := B) f N
        (LinearMap.baseChange B V.subtype (LinearMap.baseChange B D y)) =
      fLoc (algebraMap A B f) (LinearMap.baseChange B d)
        (psiEquiv (B := B) f M (LinearMap.baseChange B W.subtype y)) := by
  rw [fLoc_psiEquiv]
  congr 1
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
    ← LinearMap.baseChange_comp, hD]

/-! ## The comparison map -/

/-- The bare-differential form of the containment
`Stacks.Eta.BaseChange.etaBaseChangeTerm_le_fetaTerm`: the ambient comparison carries the
degree-`i` décalage term of `d` into the degree-`i` décalage term of its base change. -/
theorem psiEquiv_mem_fetaTerm (f : A) {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (d : M →ₗ[A] N) (i : ℤ) (y : B ⊗[A] (fetaTerm f d i)) :
    psiEquiv (B := B) f M (LinearMap.baseChange B (fetaTerm f d i).subtype y) ∈
      fetaTerm (algebraMap A B f) (LinearMap.baseChange B d) i := by
  have hle : Submodule.span B
        ((etaBCPsi (B := B) f M) '' (fetaTerm f d i : Set (Loc f M))) ≤
      fetaTerm (algebraMap A B f) (LinearMap.baseChange B d) i := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_fetaTerm] at hx
    rw [SetLike.mem_coe, mem_fetaTerm]
    refine ⟨etaBCPsi_mem_fpowSub f M i hx.1, ?_⟩
    rw [← etaBCPsi_fLoc f d x]
    exact etaBCPsi_mem_fpowSub f N (i + 1) hx.2
  rw [span_image_etaBCPsi] at hle
  exact hle (Submodule.mem_map_of_mem (LinearMap.mem_range_self _ y))

/-- The comparison `B ⊗_A (η_f d)^i ⟶ (η_g (B ⊗_A d))^i` attached to a bare differential `d`. -/
def psiTermMap (f : A) {M N : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (d : M →ₗ[A] N) (i : ℤ) :
    (B ⊗[A] (fetaTerm f d i)) →ₗ[B]
      fetaTerm (algebraMap A B f) (LinearMap.baseChange B d) i :=
  LinearMap.codRestrict _
    ((psiEquiv (B := B) f M).toLinearMap.comp
      (LinearMap.baseChange B (fetaTerm f d i).subtype))
    (psiEquiv_mem_fetaTerm f d i)

/-- The degree-`i` comparison `B ⊗_A (η_f K)^i ⟶ (η_g (B ⊗_A K))^i`, the corestriction of the
ambient comparison `Stacks.Eta.BaseChange.psiEquiv` to the décalage terms. -/
def etaBaseChangeTermMap (f : A) (K : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (B ⊗[A] (EtaComplex.term f K i)) →ₗ[B]
      EtaComplex.term (algebraMap A B f) (baseChangeComplex (B := B) K) i :=
  psiTermMap (B := B) f (K.d i (i + 1)).hom i

/-- `etaBaseChangeTermMap f K i` is `psiTermMap` at the differential `K.d i (i + 1)`. -/
theorem etaBaseChangeTermMap_eq (f : A) (K : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    etaBaseChangeTermMap (B := B) f K i = psiTermMap (B := B) f (K.d i (i + 1)).hom i := rfl

/-- The value of `etaBaseChangeTermMap f K i x` in the ambient localization is the image of `x`
under the base change of the inclusion of the décalage term followed by
`Stacks.Eta.BaseChange.psiEquiv`. -/
theorem etaBaseChangeTermMap_val (f : A) (K : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    (x : B ⊗[A] (EtaComplex.term f K i)) :
    (etaBaseChangeTermMap (B := B) f K i x).val =
      psiEquiv (B := B) f (K.X i : Type u)
        (LinearMap.baseChange B (EtaComplex.term f K i).subtype x) := rfl

/-- **The canonical base-change comparison of the décalage.** For a map of commutative rings
`A → B`, an element `f ∈ A` with image `g = algebraMap A B f`, and a cochain complex `K` of
`A`-modules, the canonical chain map `B ⊗_A (η_f K) ⟶ η_g (B ⊗_A K)`. -/
def etaBaseChangeMap (f : A) (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    baseChangeComplex (B := B) (EtaComplex.etaObject f K) ⟶
      EtaComplex.etaObject (algebraMap A B f) (baseChangeComplex (B := B) K) where
  f i := ModuleCat.ofHom (etaBaseChangeTermMap (B := B) f K i)
  comm' i j hij := by
    change i + 1 = j at hij
    subst hij
    have hd2 : (EtaComplex.etaObject f K).d i (i + 1) =
        ModuleCat.ofHom (EtaComplex.etaDifferential f K i) :=
      EtaComplex.etaObject_d _ _ i
    have hd1 : (EtaComplex.etaObject (algebraMap A B f)
          (baseChangeComplex (B := B) K)).d i (i + 1) =
        ModuleCat.ofHom (EtaComplex.etaDifferential (algebraMap A B f)
          (baseChangeComplex (B := B) K) i) :=
      EtaComplex.etaObject_d _ _ i
    have hd3 : (baseChangeComplex (B := B) (EtaComplex.etaObject f K)).d i (i + 1) =
        ModuleCat.ofHom (LinearMap.baseChange B (EtaComplex.etaDifferential f K i)) :=
      congrArg (fun m : (EtaComplex.etaObject f K).X i ⟶ (EtaComplex.etaObject f K).X (i + 1) =>
        ModuleCat.ofHom (LinearMap.baseChange B m.hom)) hd2
    rw [hd1, hd3]
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun x : B ⊗[A] (EtaComplex.term f K i) => Subtype.ext ?_
    exact (psiEquiv_baseChange_restriction (B := B) f (K.d i (i + 1)).hom
      (EtaComplex.etaDifferential f K i) (LinearMap.ext fun _ => rfl) x).symm

/-- The `i`-th component of `etaBaseChangeMap f K` is `etaBaseChangeTermMap f K i`. -/
theorem etaBaseChangeMap_f (f : A) (K : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (etaBaseChangeMap (B := B) f K).f i =
      ModuleCat.ofHom (etaBaseChangeTermMap (B := B) f K i) := rfl

/-- **Naturality of the base-change comparison in the complex.** -/
theorem etaBaseChangeMap_naturality (f : A) {K L : CochainComplex (ModuleCat.{u} A) ℤ}
    (φ : K ⟶ L) :
    baseChangeMap (B := B) (EtaComplex.etaMap f φ) ≫ etaBaseChangeMap (B := B) f L =
      etaBaseChangeMap (B := B) f K ≫
        EtaComplex.etaMap (algebraMap A B f) (baseChangeMap (B := B) φ) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun x : B ⊗[A] (EtaComplex.term f K i) => Subtype.ext ?_
  exact psiEquiv_baseChange_restriction (B := B) f (φ.f i).hom
    (EtaComplex.etaMapLinear f φ i) (LinearMap.ext fun _ => rfl) x

/-! ## Tag 0F7Q in the `EtaComplex.etaObject` spelling

`Stacks.Eta.QuasiIsoPreservation.quasiIso_etaPow_of_quasiIso` is stated on the full subcategory of
`f`-torsion-free modules. A complex of `A`-modules with `f`-torsion-free terms is lifted into that
subcategory and the two décalages are identified, so that the tag can be read directly at
`EtaComplex.etaObject`. -/

open Stacks.Eta.DerivedFunctor in
/-- A cochain complex of `A`-modules with `f`-torsion-free terms, read in the full subcategory
of `f`-torsion-free modules. -/
def liftTorsionFree (f : A) (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (h : EtaComplex.IsTorsionFree f K) :
    CochainComplex (FTorsionFreeModule.{u, u} f) ℤ where
  X i := ⟨K.X i, h i⟩
  d i j := ObjectProperty.homMk (K.d i j)
  shape i j hij := ObjectProperty.hom_ext _ (K.shape i j hij)
  d_comp_d' i j k _ _ := ObjectProperty.hom_ext _ (K.d_comp_d i j k)

open Stacks.Eta.DerivedFunctor in
/-- The underlying complex of `liftTorsionFree f K h` is `K`. -/
theorem underlyingComplex_obj_liftTorsionFree (f : A) (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (h : EtaComplex.IsTorsionFree f K) :
    (underlyingComplex.{u, u} f).obj (liftTorsionFree f K h) = K := rfl

open Stacks.Eta.DerivedFunctor in
/-- A map of complexes of `A`-modules with `f`-torsion-free terms, read in the full
subcategory. -/
def liftTorsionFreeMap (f : A) {K L : CochainComplex (ModuleCat.{u} A) ℤ}
    (hK : EtaComplex.IsTorsionFree f K) (hL : EtaComplex.IsTorsionFree f L) (φ : K ⟶ L) :
    liftTorsionFree f K hK ⟶ liftTorsionFree f L hL where
  f i := ObjectProperty.homMk (φ.f i)
  comm' i j _ := ObjectProperty.hom_ext _ (φ.comm i j)

open Stacks.Eta.DerivedFunctor in
/-- The underlying map of complexes of `liftTorsionFreeMap f hK hL φ` is `φ`. -/
theorem underlyingComplex_map_liftTorsionFreeMap (f : A)
    {K L : CochainComplex (ModuleCat.{u} A) ℤ}
    (hK : EtaComplex.IsTorsionFree f K) (hL : EtaComplex.IsTorsionFree f L) (φ : K ⟶ L) :
    (underlyingComplex.{u, u} f).map (liftTorsionFreeMap f hK hL φ) = φ := rfl

open Stacks.Eta.DerivedFunctor in
private theorem underlyingEta_d (f : A) (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (h : EtaComplex.IsTorsionFree f K) (i : ℤ) :
    ((underlyingComplex.{u, u} f).obj
        ((etaFunctor.{u, u} f).functor.obj (liftTorsionFree f K h))).d i (i + 1) =
      (EtaComplex.etaObject f K).d i (i + 1) := by
  have hof : (Stacks.Eta.DerivedFunctor.etaComplex f (liftTorsionFree f K h)).d i (i + 1) =
      Stacks.Eta.DerivedFunctor.etaDifferential f (liftTorsionFree f K h) i := by
    simp only [Stacks.Eta.DerivedFunctor.etaComplex, CochainComplex.of_d]
  rw [EtaComplex.etaObject_d]
  exact congrArg (fun m => m.hom) hof

open Stacks.Eta.DerivedFunctor in
/-- The décalage computed in the full subcategory of `f`-torsion-free modules is the décalage
`EtaComplex.etaObject`. -/
def underlyingEtaIso (f : A) (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (h : EtaComplex.IsTorsionFree f K) :
    (underlyingComplex.{u, u} f).obj
        ((etaFunctor.{u, u} f).functor.obj (liftTorsionFree f K h)) ≅
      EtaComplex.etaObject f K :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (fun i j hij => by
      obtain rfl : i + 1 = j := hij
      exact (Category.id_comp _).trans
        ((underlyingEta_d f K h i).symm.trans (Category.comp_id _).symm))

open Stacks.Eta.DerivedFunctor in
/-- The décalage `EtaComplex.etaMap f φ` of a quasi-isomorphism `φ` between complexes of
`f`-torsion-free `A`-modules is a quasi-isomorphism. -/
@[stacks 0F7Q "stated for `EtaComplex.etaObject`"]
theorem quasiIso_etaMap (f : A) (hf : f ∈ nonZeroDivisors A)
    {K L : CochainComplex (ModuleCat.{u} A) ℤ}
    (hK : EtaComplex.IsTorsionFree f K) (hL : EtaComplex.IsTorsionFree f L)
    (φ : K ⟶ L) (hφ : QuasiIso φ) :
    QuasiIso (EtaComplex.etaMap f φ) := by
  have hg : QuasiIso ((underlyingComplex.{u, u} f).map (liftTorsionFreeMap f hK hL φ)) := hφ
  have := Stacks.Eta.QuasiIsoPreservation.quasiIso_etaPow_of_quasiIso hf
    (etaFunctor.{u, u} f) (liftTorsionFreeMap f hK hL φ) hg
  refine quasiIso_of_arrow_mk_iso
    ((underlyingComplex.{u, u} f).map
      ((etaFunctor.{u, u} f).functor.map (liftTorsionFreeMap f hK hL φ)))
    (EtaComplex.etaMap f φ)
    (CategoryTheory.Arrow.isoMk (underlyingEtaIso f K hK) (underlyingEtaIso f L hL) ?_)
  apply HomologicalComplex.hom_ext
  intro i
  rfl

/-! ## Torsion-freeness of a termwise flat complex -/

/-- A complex of flat modules is torsion-free for every nonzerodivisor. -/
theorem isTorsionFree_of_flat {R : Type u} [CommRing R] (r : R) (hr : r ∈ nonZeroDivisors R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hflat : ∀ i, Module.Flat R (K.X i)) :
    EtaComplex.IsTorsionFree r K := by
  intro i x hx
  have := hflat i
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors hr (hx.trans (smul_zero r).symm)

/-- The base change of a complex of flat `A`-modules is `g`-torsion-free whenever `g` is a
nonzerodivisor of `B`. -/
theorem isTorsionFree_baseChangeComplex (f : A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (hflat : ∀ i, Module.Flat A (K.X i)) :
    EtaComplex.IsTorsionFree (algebraMap A B f) (baseChangeComplex (B := B) K) := by
  refine isTorsionFree_of_flat _ hg _ fun i => ?_
  have := hflat i
  exact (inferInstance : Module.Flat B (B ⊗[A] (K.X i : Type u)))

/-! ## Tag 0F7X: the comparison on a bounded complex of finite free modules -/

/-- A square of linear maps carries décalage terms into décalage terms. -/
theorem fLoc_mem_fetaTerm_of_square {R : Type u} [CommRing R] (r : R)
    {M N P Q : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (d : M →ₗ[R] N) (d' : P →ₗ[R] Q) (eM : M →ₗ[R] P) (eN : N →ₗ[R] Q)
    (hcomm : d'.comp eM = eN.comp d) (i : ℤ) {x : Loc r M} (hx : x ∈ fetaTerm r d i) :
    fLoc r eM x ∈ fetaTerm r d' i := by
  rw [mem_fetaTerm] at hx
  rw [mem_fetaTerm]
  refine ⟨EtaComplex.localizedMap_mem_power r eM i hx.1, ?_⟩
  rw [EtaComplex.localizedMap_comp_apply, hcomm, ← EtaComplex.localizedMap_comp_apply]
  exact EtaComplex.localizedMap_mem_power r eN (i + 1) hx.2

/-- Localizing a linear equivalence and its inverse composes to the identity. -/
private theorem fLoc_fLoc_symm {R : Type u} [CommRing R] (r : R)
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (e : M ≃ₗ[R] P) (x : Loc r P) :
    fLoc r e.toLinearMap (fLoc r e.symm.toLinearMap x) = x := by
  rw [EtaComplex.localizedMap_comp_apply, e.comp_symm, EtaComplex.localizedMap_id_apply]

/-- Localizing a linear equivalence gives an injective map. -/
private theorem injective_fLoc_of_equiv {R : Type u} [CommRing R] (r : R)
    {M P : Type u} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (e : M ≃ₗ[R] P) : Function.Injective (fLoc r e.toLinearMap) := fun x y hxy =>
  (fLoc_fLoc_symm r e.symm x).symm.trans
    ((congrArg (fLoc r e.symm.toLinearMap) hxy).trans (fLoc_fLoc_symm r e.symm y))

/-- **Bijectivity of the comparison sees the differential only up to isomorphism.**  Let

`d' ∘ eM = eN ∘ d`

be a commuting square of `A`-linear maps whose verticals `eM : M ≃ M'` and `eN : N ≃ N'` are
invertible.  Then the degree-`i` comparison attached to `d'` is bijective as soon as the one
attached to `d` is. -/
theorem bijective_psiTermMap_of_square (r : A) {M N M' N' : Type u}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [AddCommGroup M'] [Module A M'] [AddCommGroup N'] [Module A N']
    (d : M →ₗ[A] N) (d' : M' →ₗ[A] N') (eM : M ≃ₗ[A] M') (eN : N ≃ₗ[A] N')
    (hcomm : d'.comp eM.toLinearMap = eN.toLinearMap.comp d) (i : ℤ)
    (h : Function.Bijective (psiTermMap (B := B) r d i)) :
    Function.Bijective (psiTermMap (B := B) r d' i) := by
  have hback : d.comp eM.symm.toLinearMap = eN.symm.toLinearMap.comp d' :=
    LinearMap.ext fun z => by
      have h1 : d' (eM (eM.symm z)) = eN (d (eM.symm z)) := LinearMap.congr_fun hcomm (eM.symm z)
      rw [eM.apply_symm_apply] at h1
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [h1, eN.symm_apply_apply]
  have hfwd : ∀ x : Loc r M, x ∈ fetaTerm r d i → fLoc r eM.toLinearMap x ∈ fetaTerm r d' i :=
    fun _ hx => fLoc_mem_fetaTerm_of_square r d d' eM.toLinearMap eN.toLinearMap hcomm i hx
  have hbwd : ∀ x : Loc r M', x ∈ fetaTerm r d' i →
      fLoc r eM.symm.toLinearMap x ∈ fetaTerm r d i :=
    fun _ hx =>
      fLoc_mem_fetaTerm_of_square r d' d eM.symm.toLinearMap eN.symm.toLinearMap hback i hx
  let fW : (fetaTerm r d i) →ₗ[A] (fetaTerm r d' i) :=
    LinearMap.codRestrict _ ((fLoc r eM.toLinearMap).comp (fetaTerm r d i).subtype)
      fun x => hfwd x x.2
  let fV : (fetaTerm r d' i) →ₗ[A] (fetaTerm r d i) :=
    LinearMap.codRestrict _ ((fLoc r eM.symm.toLinearMap).comp (fetaTerm r d' i).subtype)
      fun x => hbwd x x.2
  have hWV : ∀ x : (fetaTerm r d' i), fW (fV x) = x := fun x =>
    Subtype.ext (fLoc_fLoc_symm r eM _)
  have hVW : ∀ x : (fetaTerm r d i), fV (fW x) = x := fun x =>
    Subtype.ext (fLoc_fLoc_symm r eM.symm _)
  have hΦsurj : Function.Surjective (LinearMap.baseChange B fW) := fun z =>
    ⟨LinearMap.baseChange B fV z, by
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
        show fW.comp fV = LinearMap.id from LinearMap.ext hWV, LinearMap.baseChange_id]
      rfl⟩
  have hsq : ∀ y : B ⊗[A] (fetaTerm r d i),
      ((psiTermMap (B := B) r d' i) (LinearMap.baseChange B fW y)).val =
        fLoc (algebraMap A B r) (LinearMap.baseChange B eM.toLinearMap)
          ((psiTermMap (B := B) r d i y).val) := by
    intro y
    exact psiEquiv_baseChange_restriction (B := B) r eM.toLinearMap fW
      (LinearMap.ext fun _ => rfl) y
  have hFinj : Function.Injective
      (fLoc (algebraMap A B r) (LinearMap.baseChange B eM.toLinearMap)) :=
    injective_fLoc_of_equiv (algebraMap A B r) (eM.baseChange A B M M')
  have hbcback : (LinearMap.baseChange B d).comp (LinearMap.baseChange B eM.symm.toLinearMap) =
      (LinearMap.baseChange B eN.symm.toLinearMap).comp (LinearMap.baseChange B d') := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hback]
  have hFsymm : ∀ t : Loc (algebraMap A B r) (B ⊗[A] M'),
      t ∈ fetaTerm (algebraMap A B r) (LinearMap.baseChange B d') i →
        fLoc (algebraMap A B r) (LinearMap.baseChange B eM.symm.toLinearMap) t ∈
          fetaTerm (algebraMap A B r) (LinearMap.baseChange B d) i := fun _ ht =>
    fLoc_mem_fetaTerm_of_square (algebraMap A B r) (LinearMap.baseChange B d')
      (LinearMap.baseChange B d) (LinearMap.baseChange B eM.symm.toLinearMap)
      (LinearMap.baseChange B eN.symm.toLinearMap) hbcback i ht
  obtain ⟨hinj, hsurj⟩ := h
  refine ⟨fun z z' hzz' => ?_, fun t => ?_⟩
  · obtain ⟨y, hy⟩ := hΦsurj z
    obtain ⟨y', hy'⟩ := hΦsurj z'
    rw [← hy, ← hy'] at hzz' ⊢
    have h1 : fLoc (algebraMap A B r) (LinearMap.baseChange B eM.toLinearMap)
          ((psiTermMap (B := B) r d i y).val) =
        fLoc (algebraMap A B r) (LinearMap.baseChange B eM.toLinearMap)
          ((psiTermMap (B := B) r d i y').val) := by
      rw [← hsq, ← hsq, hzz']
    exact congrArg (LinearMap.baseChange B fW) (hinj (Subtype.ext (hFinj h1)))
  · obtain ⟨y, hy⟩ := hsurj ⟨_, hFsymm t.val t.2⟩
    refine ⟨LinearMap.baseChange B fW y, Subtype.ext ?_⟩
    have hy' := hsq y
    rw [hy] at hy'
    exact hy'.trans (fLoc_fLoc_symm _ (eM.baseChange A B M M') t.val)

open Stacks.Eta.LocallyFreeTerms in
/-- **Stacks 0F7X, degreewise.** For a bounded complex `C` of finite free `A`-modules all of
whose determinantal ideals `I_i(C, f)` are principal, the comparison attached to the
differential matrix of `C` is bijective. -/
theorem bijective_psiTermMap_mulVecLin (C : BoundedComplex A) (f : A) (hf : IsRegular f)
    (hg : IsRegular (algebraMap A B f)) (hI : ∀ i : ℤ, (idealI C f i).IsPrincipal) (i : ℤ) :
    Function.Bijective (psiTermMap (B := B) f (C.d i).mulVecLin i) := by
  have hE : ∀ x : B ⊗[A] (fetaTerm f (C.d i).mulVecLin i),
      (etaTermBaseChangeMap (B := B) C f hf hg hI i x).val =
        fLoc (algebraMap A B f)
          (TensorProduct.piScalarRight A B B (Fin (C.rank i))).toLinearMap
          ((psiTermMap (B := B) f (C.d i).mulVecLin i x).val) := fun _ => rfl
  have hinjE := injective_fLoc_of_equiv (algebraMap A B f)
    (TensorProduct.piScalarRight A B B (Fin (C.rank i)))
  constructor
  · intro x y hxy
    refine injective_etaTermBaseChangeMap C f hf hg hI i (Subtype.ext ?_)
    rw [hE, hE, congrArg Subtype.val hxy]
  · intro y
    have hmem : fLoc (algebraMap A B f)
        (TensorProduct.piScalarRight A B B (Fin (C.rank i))).toLinearMap y.val ∈
          fetaTerm (algebraMap A B f) ((C.d i).map (algebraMap A B)).mulVecLin i :=
      fLoc_mem_fetaTerm_of_square (algebraMap A B f)
        (LinearMap.baseChange B (C.d i).mulVecLin)
        ((C.d i).map (algebraMap A B)).mulVecLin
        (TensorProduct.piScalarRight A B B (Fin (C.rank i))).toLinearMap
        (TensorProduct.piScalarRight A B B (Fin (C.rank (i + 1)))).toLinearMap
        (piScalarRight_mulVec (C.d i)).symm i y.2
    obtain ⟨x, hx⟩ := surjective_etaTermBaseChangeMap C f hf hg hI i ⟨_, hmem⟩
    refine ⟨x, Subtype.ext (hinjE ?_)⟩
    rw [← hE]
    exact congrArg Subtype.val hx

/-- For a bounded complex `C` of finite free `A`-modules all of whose determinantal ideals
`I_i(C, f)` are principal, the canonical base-change comparison `B ⊗_A (η_f C) ⟶ η_g (B ⊗_A C)` is
an isomorphism of complexes. -/
@[stacks 0F7X "the comparison chain map of this file is an isomorphism"]
theorem isIso_etaBaseChangeMap_toCochainComplex (C : BoundedComplex A) (f : A) (hf : IsRegular f)
    (hg : IsRegular (algebraMap A B f)) (hI : ∀ i : ℤ, (idealI C f i).IsPrincipal) :
    IsIso (etaBaseChangeMap (B := B) f C.toCochainComplex) := by
  have hcomp : ∀ i : ℤ, IsIso ((etaBaseChangeMap (B := B) f C.toCochainComplex).f i) := by
    intro i
    have hbij : Function.Bijective
        (psiTermMap (B := B) f (C.toCochainComplex.d i (i + 1)).hom i) := by
      rw [show (C.toCochainComplex.d i (i + 1)).hom = (C.d i).mulVecLin from
        congrArg ModuleCat.Hom.hom (C.toCochainComplex_d i)]
      exact bijective_psiTermMap_mulVecLin C f hf hg hI i
    exact (ConcreteCategory.isIso_iff_bijective
      ((etaBaseChangeMap (B := B) f C.toCochainComplex).f i)).mpr hbij
  have := hcomp
  exact HomologicalComplex.Hom.isIso_of_components _

/-! ## The comparison at a presentation by a bounded complex of finite free modules -/

/-- **The good base-change lemma at `P = η_f C`.**  Let `A → B` be a ring map, `f ∈ A` with
`f` and its image `g` nonzerodivisors, `C` a bounded complex of finite free `A`-modules all of
whose determinantal ideals `I_i(C, f)` are principal, and `𝒦` a complex of flat `A`-modules
with a map `ψ : C ⟶ 𝒦` whose base change is a quasi-isomorphism.  Then the composite

`B ⊗_A (η_f C) ⟶ B ⊗_A (η_f 𝒦) ⟶ η_g (B ⊗_A 𝒦)`

is a quasi-isomorphism. -/
theorem quasiIso_etaBaseChangeMap_comp_of_toCochainComplex
    (C : BoundedComplex A) (f : A) (hf : IsRegular f) (hg : IsRegular (algebraMap A B f))
    (hI : ∀ i : ℤ, (idealI C f i).IsPrincipal)
    (𝒦 : CochainComplex (ModuleCat.{u} A) ℤ) (hflat : ∀ i, Module.Flat A (𝒦.X i))
    (ψ : C.toCochainComplex ⟶ 𝒦) (hψ : QuasiIso (baseChangeMap (B := B) ψ)) :
    QuasiIso (baseChangeMap (B := B) (EtaComplex.etaMap f ψ) ≫
      etaBaseChangeMap (B := B) f 𝒦) := by
  have hgnzd : algebraMap A B f ∈ nonZeroDivisors B := isRegular_iff_mem_nonZeroDivisors.mp hg
  have hCflat : ∀ i : ℤ, Module.Flat A (C.toCochainComplex.X i) := fun i =>
    (inferInstance : Module.Flat A (Fin (C.rank i) → A))
  rw [etaBaseChangeMap_naturality]
  have := isIso_etaBaseChangeMap_toCochainComplex (B := B) C f hf hg hI
  have : QuasiIso (EtaComplex.etaMap (algebraMap A B f) (baseChangeMap (B := B) ψ)) :=
    quasiIso_etaMap (algebraMap A B f) hgnzd
      (isTorsionFree_baseChangeComplex f hgnzd C.toCochainComplex hCflat)
      (isTorsionFree_baseChangeComplex f hgnzd 𝒦 hflat) _ hψ
  infer_instance

end

end Stacks.Eta.GoodBaseChange
