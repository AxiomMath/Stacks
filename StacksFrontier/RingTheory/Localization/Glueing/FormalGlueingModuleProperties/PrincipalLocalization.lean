module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.MilnorPatching.ModuleCategory
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Projective
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence
public import StacksFrontier.RingTheory.AdicCompletion.QuotientBijective

/-!
# Formal glueing along a principal localization, and the properties it detects

This file specializes formal glueing to a single element and records what it preserves.

Let `R → S` be flat and `f : R`. If the map is an isomorphism modulo the principal ideal `(f)`,
then the category of `R`-modules is equivalent to the category of an `S`-module together with an
`R[1/f]`-module identified over `S[1/f]`. For a Noetherian ring `R` this applies to the `f`-adic
completion of `R`, so a finitely generated `R`-module is equivalent to a finitely generated module
over the completion together with a finitely generated module over `R[1/f]`, compatibly identified
after localizing the completion at `f`.

Finally, formal glueing detects finite generation, finite presentation, flatness and projectivity
on the generic and local pieces, its tensor product is computed piecewise, and the equivalence
therefore induces an equivalence on commutative algebra objects.

This file treats the principal localization; the adic completion, the tensor products and the
detected properties are in the sibling files `AdicCompletion`, `MonoidalStructure` and
`Properties`.

## Main definitions

* `FormalGlueing.PrincipalModuleGlueingData`: the category of triples consisting of an
  `S`-module, an `R[1/f]`-module, and an `S[1/f]`-linear comparison isomorphism.

## Main results

* `FormalGlueing.exists_canonicalModuleGlueingEquivalence`: for a principal localization the
  canonical functor is an equivalence of categories.

## Implementation notes

The fiber product of module categories is modeled by `CategoricalPullback`. Extension of scalars
along `R[1/f] → S[1/f]` makes its structural isomorphism genuinely `S[1/f]`-linear, and the
structural isomorphism of the canonical functor is characterized on pure tensors, which also pins
the canonical equality of the two ways to extend scalars from `R` to `S[1/f]`.

## References

* [Stacks Project, Tag 05ES](https://stacks.math.columbia.edu/tag/05ES)
-/

/-! ### Formal glueing of modules along a principal localization -/

section

@[expose] public section

namespace FormalGlueing

universe u v w

open CategoryTheory CategoryTheory.Limits

/-- The canonical map `R[1/f] → S[1/f]` induced by a ring map `R → S`. -/
public noncomputable abbrev principalLocalizationMap
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] (f : R) :
    Localization.Away f →+* Localization.Away (algebraMap R S f) :=
  IsLocalization.Away.map (Localization.Away f)
    (Localization.Away (algebraMap R S f)) (algebraMap R S) f

/-- The category of an `S`-module, an `R[1/f]`-module, and an `S[1/f]`-linear isomorphism
between their scalar extensions. -/
public noncomputable abbrev PrincipalModuleGlueingData
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] (f : R) :=
  CategoricalPullback
    (ModuleCat.extendScalars.{v, v, w}
      (algebraMap S (Localization.Away (algebraMap R S f))))
    (ModuleCat.extendScalars.{u, v, w} (principalLocalizationMap R S f))

end FormalGlueing
end

end

section

namespace FormalGlueing

open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped ChangeOfRings
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

private theorem restrictScalarsTower {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (M : ModuleCat.{w} A) :
    IsScalarTower R A ((ModuleCat.restrictScalars (algebraMap R A)).obj M) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
attribute [local instance] restrictScalarsTower

private theorem eqToIso_extendScalars_tmul
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {a b : R →+* S} (h : a = b) (M : ModuleCat.{max u v w} R) (s : S) (m : M) :
    (eqToIso (congrArg (ModuleCat.extendScalars.{u, v, max u v w}) h)).hom.app M
      (s ⊗ₜ[R,a] m) = s ⊗ₜ[R,b] m := by
  subst b
  rfl

section Square
variable {R : Type u} {S : Type v} {A : Type u} {B : Type v}
  [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  (a : R →+* S) (b : R →+* A) (c : S →+* B) (d : A →+* B)
  (h : c.comp a = d.comp b)
private noncomputable def squareComparison :
    ModuleCat.extendScalars.{u, v, max u v w} a ⋙ ModuleCat.extendScalars c ≅
    ModuleCat.extendScalars.{u, u, max u v w} b ⋙ ModuleCat.extendScalars d :=
  (ModuleGlueing.extendScalarsComp.{max u v w} a c).symm ≪≫
    eqToIso (congrArg (ModuleCat.extendScalars.{u, v, max u v w}) h) ≪≫
    ModuleGlueing.extendScalarsComp.{max u v w} b d

private theorem squareComparison_one_tmul (M : ModuleCat.{max u v w} R) (m : M) :
    (squareComparison a b c d h).hom.app M
      ((1 : B) ⊗ₜ[S,c] ((1 : S) ⊗ₜ[R,a] m)) =
      (1 : B) ⊗ₜ[A,d] ((1 : A) ⊗ₜ[R,b] m) := by
  have hi : (ModuleGlueing.extendScalarsComp.{max u v w} a c).inv.app M
      ((1 : B) ⊗ₜ[S,c] ((1 : S) ⊗ₜ[R,a] m)) = (1 : B) ⊗ₜ[R,c.comp a] m := by
    rw [← ModuleGlueing.extendScalarsComp_hom_app_one_tmul.{max u v w} a c M m]
    exact ConcreteCategory.congr_hom
      ((ModuleGlueing.extendScalarsComp.{max u v w} a c).hom_inv_id_app M) _
  show (ModuleGlueing.extendScalarsComp.{max u v w} b d).hom.app M
    ((eqToIso (congrArg (ModuleCat.extendScalars.{u, v, max u v w}) h)).hom.app M
      ((ModuleGlueing.extendScalarsComp.{max u v w} a c).inv.app M _)) = _
  rw [hi, eqToIso_extendScalars_tmul h M (1 : B) m,
    ModuleGlueing.extendScalarsComp_hom_app_one_tmul]
end Square

private noncomputable def restrictLinearEquiv
    (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {M : ModuleCat.{w} B} {N : Type*} [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] (e : M ≃ₗ[B] N) :
    (ModuleCat.restrictScalars (algebraMap A B)).obj M ≃ₗ[A] N := by
  letI : Module A M := Module.compHom M (algebraMap A B)
  letI : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact e.restrictScalars A

open FormalGlueing
variable {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S] (f : R)

private noncomputable abbrev localizationAlgebra :
    Algebra (Localization.Away f) (Localization.Away (algebraMap R S f)) :=
  (principalLocalizationMap R S f).toAlgebra
attribute [local instance] localizationAlgebra

private theorem localizationMap_comm :
    (algebraMap S (Localization.Away (algebraMap R S f))).comp (algebraMap R S) =
      (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))).comp
        (algebraMap R (Localization.Away f)) := by
  ext x
  exact (IsLocalization.map_eq (M := Submonoid.powers f)
    (S := Localization.Away f) (Q := Localization.Away (algebraMap R S f))
    (g := algebraMap R S) (T := Submonoid.powers (algebraMap R S f))
    (by rintro y ⟨n, rfl⟩; exact ⟨n, (map_pow (algebraMap R S) f n).symm⟩) x).symm

private theorem localizationTower :
    IsScalarTower R (Localization.Away f) (Localization.Away (algebraMap R S f)) := by
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  exact (IsScalarTower.algebraMap_apply R S _ x).trans
    (congrArg (fun h : R →+* Localization.Away (algebraMap R S f) => h x)
      (localizationMap_comm S f))
attribute [local instance] localizationTower

private theorem localizationPushout :
    Algebra.IsPushout R S (Localization.Away f) (Localization.Away (algebraMap R S f)) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers f))
      (Localization.Away (algebraMap R S f)) := by
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization.Away (algebraMap R S f)
        (Localization.Away (algebraMap R S f)))
  exact Algebra.isPushout_of_isLocalization (Submonoid.powers f) (Localization.Away f) S
    (Localization.Away (algebraMap R S f))
attribute [local instance] localizationPushout

private noncomputable def overlapToTensor
    (N : ModuleCat.{max u v w} (Localization.Away f)) :
    (ModuleCat.restrictScalars (algebraMap S (Localization.Away (algebraMap R S f)))).obj
      ((ModuleCat.extendScalars (algebraMap (Localization.Away f)
        (Localization.Away (algebraMap R S f)))).obj N) ≃ₗ[S]
      S ⊗[R] (restrictFromAway (fun _ : Fin 1 => f) 0 N) :=
  (restrictLinearEquiv S (extendScalarsEquiv (Localization.Away (algebraMap R S f)) N)).trans
    (Algebra.IsPushout.cancelBaseChange R S (Localization.Away f)
      (Localization.Away (algebraMap R S f))
      (restrictFromAway (fun _ : Fin 1 => f) 0 N))

private noncomputable def genericToOverlap (M : ModuleCat.{max u v w} S) :
    LocalizedModule.Away (algebraMap R S f) M ≃ₗ[S]
      (ModuleCat.restrictScalars (algebraMap S (Localization.Away (algebraMap R S f)))).obj
        ((ModuleCat.extendScalars (algebraMap S
          (Localization.Away (algebraMap R S f)))).obj M) :=
  ((LocalizedModule.equivTensorProduct
    (Submonoid.powers (algebraMap R S f)) M).restrictScalars S).trans
    (restrictLinearEquiv S (extendScalarsEquiv (Localization.Away (algebraMap R S f)) M)).symm

private noncomputable def pullbackAlpha
    (X : PrincipalModuleGlueingData.{u, v, max u v w} R S f) :
    LocalizedModule.Away (algebraMap R S f) X.fst ≃ₗ[S]
      S ⊗[R] (restrictFromAway (fun _ : Fin 1 => f) 0 X.snd) :=
  (genericToOverlap S f X.fst).trans
    (((ModuleCat.restrictScalars (algebraMap S
      (Localization.Away (algebraMap R S f)))).mapIso X.iso).toLinearEquiv.trans
        (overlapToTensor S f X.snd))

private theorem genericToOverlap_mk (M : ModuleCat.{max u v w} S) (m : M) :
    genericToOverlap S f M (LocalizedModule.mkLinearMap _ _ m) =
      (1 : Localization.Away (algebraMap R S f)) ⊗ₜ[S,algebraMap S _] m := by
  show (extendScalarsEquiv _ M).symm
    (LocalizedModule.equivTensorProduct _ M (LocalizedModule.mk m 1)) = _
  rw [LocalizedModule.equivTensorProduct_apply_mk]
  simp only [Localization.mk_one]
  rfl

private theorem overlapToTensor_one_tmul
    (N : ModuleCat.{max u v w} (Localization.Away f)) (n : N) :
    overlapToTensor S f N
      ((1 : Localization.Away (algebraMap R S f)) ⊗ₜ[Localization.Away f,algebraMap _ _] n) =
      (1 : S) ⊗ₜ[R] (show restrictFromAway (fun _ : Fin 1 => f) 0 N from n) := by
  show Algebra.IsPushout.cancelBaseChange R S (Localization.Away f)
    (Localization.Away (algebraMap R S f)) (restrictFromAway (fun _ : Fin 1 => f) 0 N)
    (1 ⊗ₜ[Localization.Away f] (show restrictFromAway (fun _ : Fin 1 => f) 0 N from n)) = _
  exact Algebra.IsPushout.cancelBaseChange_tmul R S (Localization.Away f)
    (Localization.Away (algebraMap R S f)) (restrictFromAway (fun _ : Fin 1 => f) 0 N) n

private theorem overlapToTensor_symm_tmul
    (N : ModuleCat.{max u v w} (Localization.Away f))
    (s : S) (n : restrictFromAway (fun _ : Fin 1 => f) 0 N) :
    (overlapToTensor S f N).symm (s ⊗ₜ[R] n) =
      (algebraMap S (Localization.Away (algebraMap R S f)) s) ⊗ₜ[Localization.Away f,algebraMap _ _]
        (show N from n) := by
  show (extendScalarsEquiv _ N).symm
    ((Algebra.IsPushout.cancelBaseChange R S (Localization.Away f)
      (Localization.Away (algebraMap R S f))
      (restrictFromAway (fun _ : Fin 1 => f) 0 N)).symm (s ⊗ₜ[R] n)) = _
  rw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
  rfl

private theorem overlapToTensor_naturality
    {N N' : ModuleCat.{max u v w} (Localization.Away f)} (g : N ⟶ N')
    (z : (ModuleCat.restrictScalars (algebraMap S (Localization.Away (algebraMap R S f)))).obj
      ((ModuleCat.extendScalars (algebraMap (Localization.Away f)
        (Localization.Away (algebraMap R S f)))).obj N)) :
    overlapToTensor S f N' ((ModuleCat.extendScalars (algebraMap (Localization.Away f)
      (Localization.Away (algebraMap R S f)))).map g z) =
    TensorProduct.map LinearMap.id
      (((ModuleCat.restrictScalars (algebraMap R (Localization.Away f))).map g).hom)
      (overlapToTensor S f N z) := by
  obtain ⟨t, rfl⟩ := (overlapToTensor S f N).symm.surjective z
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul s n =>
    rw [overlapToTensor_symm_tmul]
    show overlapToTensor S f N'
      ((algebraMap S (Localization.Away (algebraMap R S f)) s)
        ⊗ₜ[Localization.Away f,algebraMap _ _]
        (g n)) = _
    rw [← overlapToTensor_symm_tmul, LinearEquiv.apply_symm_apply,
      ← overlapToTensor_symm_tmul, LinearEquiv.apply_symm_apply]
    rfl
  | add t t' ht ht' => simpa only [map_add] using congrArg₂ (· + ·) ht ht'

private theorem pullbackAlpha_mk
    (X : PrincipalModuleGlueingData.{u, v, max u v w} R S f) (m : X.fst) :
    pullbackAlpha S f X (LocalizedModule.mkLinearMap _ _ m) =
    overlapToTensor S f X.snd
      (X.iso.hom ((1 : Localization.Away (algebraMap R S f)) ⊗ₜ[S,algebraMap S _] m)) := by
  show overlapToTensor S f X.snd (X.iso.hom (genericToOverlap S f X.fst _)) = _
  rw [genericToOverlap_mk]

private theorem cechModCongr_refl {r : ℕ} (f : Fin r → R)
    (M : Type*) [AddCommGroup M] [Module R M] (s : Finset (Fin r)) (h : s = s) :
    cechModCongr f (M := M) h = LinearEquiv.refl R _ := rfl

private noncomputable def singletonDatum (M : ModuleCat.{max u v w} S)
    (N : ModuleCat.{max u v w} (Localization.Away f))
    (a : LocalizedModule.Away (algebraMap R S f) M ≃ₗ[S]
      S ⊗[R] (restrictFromAway (fun _ : Fin 1 => f) 0 N)) :
    ModuleGlueingDatum.{u, v, w} S (fun _ : Fin 1 => f)
      (localizationComparisons (fun _ : Fin 1 => f)) where
  generic := M
  localPiece _ := N
  alpha _ := a
  alphaIJ i j := by
    cases Fin.fin_one_eq_zero i
    cases Fin.fin_one_eq_zero j
    exact LinearEquiv.refl R _
  alpha_compatibility i j m := by
    cases Fin.fin_one_eq_zero i
    cases Fin.fin_one_eq_zero j
    simp
  cocycle i j k := by
    cases Fin.fin_one_eq_zero i
    cases Fin.fin_one_eq_zero j
    cases Fin.fin_one_eq_zero k
    simp [cechModCongr_refl]

attribute [local instance] moduleGlueingCategory

private noncomputable def singletonMap
    {M M' : ModuleCat.{max u v w} S}
    {N N' : ModuleCat.{max u v w} (Localization.Away f)}
    (a : LocalizedModule.Away (algebraMap R S f) M ≃ₗ[S]
      S ⊗[R] (restrictFromAway (fun _ : Fin 1 => f) 0 N))
    (b : LocalizedModule.Away (algebraMap R S f) M' ≃ₗ[S]
      S ⊗[R] (restrictFromAway (fun _ : Fin 1 => f) 0 N'))
    (p : M ⟶ M') (q : N ⟶ N')
    (h : ∀ m : M, b (LocalizedModule.mkLinearMap _ _ (p m)) =
      TensorProduct.map LinearMap.id
        (((ModuleCat.restrictScalars (algebraMap R (Localization.Away f))).map q).hom)
        (a (LocalizedModule.mkLinearMap _ _ m))) :
    singletonDatum S f M N a ⟶ singletonDatum S f M' N' b where
  generic := p
  localPiece _ := q
  alpha_compatibility _ m := h m
  alphaIJ_compatibility i j m := by
    cases Fin.fin_one_eq_zero i
    cases Fin.fin_one_eq_zero j
    exact (localizedMap_mk (fun _ : Fin 1 => f) {0}
      (((ModuleCat.restrictScalars (algebraMap R (Localization.Away f))).map q).hom) m).symm

private noncomputable def pullbackToGlue :
    PrincipalModuleGlueingData.{u, v, max u v w} R S f ⥤
      ModuleGlueingDatum.{u, v, w} S (fun _ : Fin 1 => f)
        (localizationComparisons (fun _ : Fin 1 => f)) where
  obj X := singletonDatum S f X.fst X.snd (pullbackAlpha S f X)
  map {X Y} g := singletonMap S f (pullbackAlpha S f X) (pullbackAlpha S f Y)
    g.fst g.snd (fun m => by
      rw [pullbackAlpha_mk, pullbackAlpha_mk, ← overlapToTensor_naturality]
      apply congrArg (overlapToTensor S f Y.snd)
      exact ConcreteCategory.congr_hom g.w
        ((1 : Localization.Away (algebraMap R S f)) ⊗ₜ[S,algebraMap S _] m))
  map_id X := by apply ModuleGlueingMap.ext <;> rfl
  map_comp g h := by apply ModuleGlueingMap.ext <;> rfl

private theorem pullbackToGlue_faithful : (pullbackToGlue.{u, v, w} S f).Faithful where
  map_injective {X Y} g h e := by
    apply CategoricalPullback.hom_ext
    · exact congrArg ModuleGlueingMap.generic e
    · exact congrArg (fun q => ModuleGlueingMap.localPiece q 0) e

private theorem pullbackToGlue_full : (pullbackToGlue.{u, v, w} S f).Full where
  map_surjective {X Y} g := by
    let p : X ⟶ Y :=
      { fst := g.generic
        snd := g.localPiece 0
        w := by
          apply ModuleCat.ExtendScalars.hom_ext
          intro m
          apply (overlapToTensor S f Y.snd).injective
          have h := g.alpha_compatibility 0 m
          change pullbackAlpha S f Y (LocalizedModule.mkLinearMap _ _ (g.generic m)) =
            TensorProduct.map LinearMap.id
              (((ModuleCat.restrictScalars (algebraMap R (Localization.Away f))).map
                (g.localPiece 0)).hom)
              (pullbackAlpha S f X (LocalizedModule.mkLinearMap _ _ m)) at h
          rw [pullbackAlpha_mk, pullbackAlpha_mk] at h
          exact h.trans (overlapToTensor_naturality.{u, v, w} S f
            (N := X.snd) (N' := Y.snd) (g.localPiece 0) _).symm }
    refine ⟨p, ?_⟩
    apply ModuleGlueingMap.ext
    · rfl
    · funext i
      cases Fin.fin_one_eq_zero i
      rfl

private noncomputable abbrev canonicalPullbackComparison :
    ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S) ⋙
      ModuleCat.extendScalars (algebraMap S (Localization.Away (algebraMap R S f))) ≅
    ModuleCat.extendScalars.{u, u, max u v w} (algebraMap R (Localization.Away f)) ⋙
      ModuleCat.extendScalars (algebraMap (Localization.Away f)
        (Localization.Away (algebraMap R S f))) :=
  squareComparison _ _ _ _ (localizationMap_comm S f)

private noncomputable abbrev canonicalPullbackFunctor :
    ModuleCat.{max u v w} R ⥤ PrincipalModuleGlueingData.{u, v, max u v w} R S f :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    (ModuleCat.extendScalars (algebraMap S (Localization.Away (algebraMap R S f))))
    (ModuleCat.extendScalars (principalLocalizationMap R S f)) (ModuleCat.{max u v w} R)).obj
    { fst := ModuleCat.extendScalars (algebraMap R S)
      snd := ModuleCat.extendScalars (algebraMap R (Localization.Away f))
      iso := canonicalPullbackComparison S f }

private noncomputable def localExtensionEquiv (M : ModuleCat.{w} R) :
    (ModuleCat.extendScalars (algebraMap R (Localization.Away f))).obj M ≃ₗ[Localization.Away f]
      canonicalLocalPiece (fun _ : Fin 1 => f) M 0 :=
  (extendScalarsEquiv (Localization.Away f) M).trans
    (LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm

private theorem localExtensionEquiv_one_tmul (M : ModuleCat.{w} R) (m : M) :
    localExtensionEquiv f M ((1 : Localization.Away f) ⊗ₜ[R,algebraMap R _] m) =
      canonicalLocalMk (fun _ : Fin 1 => f) M 0 m := by
  show (LocalizedModule.equivTensorProduct _ M).symm (1 ⊗ₜ[R] m) = _
  rw [LocalizedModule.equivTensorProduct_symm_apply_tmul_one]
  rfl

private theorem canonicalAlphaIJ_self {r : ℕ} (fs : Fin r → R)
    (M : ModuleCat.{w} R) (i : Fin r) :
    canonicalAlphaIJ fs M i i = LinearEquiv.refl R _ := by
  simp [canonicalAlphaIJ, IsLocalizedModule.linearEquiv]

private theorem pullbackAlpha_canonical_one_tmul (M : ModuleCat.{max u v w} R) (m : M) :
    pullbackAlpha S f ((canonicalPullbackFunctor S f).obj M)
      (LocalizedModule.mkLinearMap _ _ ((1 : S) ⊗ₜ[R,algebraMap R S] m)) =
    (1 : S) ⊗ₜ[R]
      (show restrictFromAway (fun _ : Fin 1 => f) 0
        ((ModuleCat.extendScalars (algebraMap R (Localization.Away f))).obj M) from
        (1 : Localization.Away f) ⊗ₜ[R,algebraMap R _] m) := by
  rw [pullbackAlpha_mk]
  show overlapToTensor S f _ ((canonicalPullbackComparison S f).hom.app M _) = _
  rw [squareComparison_one_tmul, overlapToTensor_one_tmul]

set_option maxHeartbeats 800000 in
-- Elaborating the two scalar-restriction compatibility diagrams needs a larger budget.
private noncomputable def canonicalDatumComparison (M : ModuleCat.{max u v w} R) :
    (pullbackToGlue S f).obj ((canonicalPullbackFunctor S f).obj M) ⟶
      canonicalDatum S (fun _ : Fin 1 => f) M where
  generic := ModuleCat.ofHom (extendScalarsEquiv S M).toLinearMap
  localPiece i := ModuleCat.ofHom (localExtensionEquiv f M).toLinearMap
  alpha_compatibility i m := by
    cases Fin.fin_one_eq_zero i
    let e := extendScalarsEquiv S M
    obtain ⟨z, rfl⟩ := e.symm.surjective m
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      change canonicalAlpha S (fun _ : Fin 1 => f) M 0
        (LocalizedModule.mkLinearMap _ _ (e (e.symm (s ⊗ₜ[R] m)))) = _
      rw [LinearEquiv.apply_symm_apply, canonicalAlpha_mk]
      have hs : e.symm (s ⊗ₜ[R] m) = s • e.symm ((1 : S) ⊗ₜ[R] m) := by
        rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      change _ = TensorProduct.map LinearMap.id _
        (pullbackAlpha S f ((canonicalPullbackFunctor S f).obj M)
          (LocalizedModule.mkLinearMap _ _ (e.symm (s ⊗ₜ[R] m))))
      rw [hs, map_smul, map_smul]
      change _ = TensorProduct.map LinearMap.id _
        (s • pullbackAlpha S f ((canonicalPullbackFunctor S f).obj M)
          (LocalizedModule.mkLinearMap _ _ ((1 : S) ⊗ₜ[R,algebraMap R S] m)))
      rw [pullbackAlpha_canonical_one_tmul]
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.map_tmul,
        LinearMap.id_apply]
      exact congrArg (TensorProduct.mk R S _ s) (localExtensionEquiv_one_tmul f M m).symm
    | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  alphaIJ_compatibility i j m := by
    cases Fin.fin_one_eq_zero i
    cases Fin.fin_one_eq_zero j
    change canonicalAlphaIJ (fun _ : Fin 1 => f) M 0 0 _ = _
    rw [canonicalAlphaIJ_self]
    exact (localizedMap_mk (fun _ : Fin 1 => f) {0}
      (((ModuleCat.restrictScalars (algebraMap R (Localization.Away f))).map
        (ModuleCat.ofHom (localExtensionEquiv f M).toLinearMap)).hom) m).symm

-- The inverse compares tensor products with several restricted scalar structures.
private theorem localExtensionEquiv_naturality
    {M N : ModuleCat.{w} R} (g : M ⟶ N) :
    (ModuleCat.extendScalars (algebraMap R (Localization.Away f))).map g ≫
      ModuleCat.ofHom (localExtensionEquiv f N).toLinearMap =
    ModuleCat.ofHom (localExtensionEquiv f M).toLinearMap ≫
      canonicalLocalMap (fun _ : Fin 1 => f) g 0 := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  show localExtensionEquiv f N
    ((1 : Localization.Away f) ⊗ₜ[R,algebraMap R _] (g m)) =
    canonicalLocalMap (fun _ : Fin 1 => f) g 0
      (localExtensionEquiv f M ((1 : Localization.Away f) ⊗ₜ[R,algebraMap R _] m))
  rw [localExtensionEquiv_one_tmul, localExtensionEquiv_one_tmul, canonicalLocalMap_mk]

private noncomputable def canonicalComparison :
    canonicalPullbackFunctor.{u, v, w} S f ⋙ pullbackToGlue.{u, v, w} S f ≅
      canonicalFunctor.{u, v, w} S (fun _ : Fin 1 => f) := by
  let t : canonicalPullbackFunctor.{u, v, w} S f ⋙ pullbackToGlue.{u, v, w} S f ⟶
      canonicalFunctor.{u, v, w} S (fun _ : Fin 1 => f) :=
    { app := canonicalDatumComparison S f
      naturality := by
        intro M N g
        apply ModuleGlueingMap.ext
        · apply ModuleCat.ExtendScalars.hom_ext
          intro m
          rfl
        · funext i
          cases Fin.fin_one_eq_zero i
          exact localExtensionEquiv_naturality f g }
  have ht : ∀ M, IsIso (t.app M) := fun M =>
    glueingMap_isIso_of_bijective S (fun _ : Fin 1 => f) (canonicalDatumComparison S f M)
      (extendScalarsEquiv S M).bijective (fun _ => (localExtensionEquiv f M).bijective)
  letI : IsIso t := (NatTrans.isIso_iff_isIso_app t).2 ht
  exact asIso t

private theorem canonicalPullbackFunctor_isEquivalence (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap ((Ideal.span {f}).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map)) :
    (canonicalPullbackFunctor.{u, v, w} S f).IsEquivalence := by
  obtain ⟨e, he, _⟩ := FormalGlueing.canonicalFunctor_sections_areQuasiInverse.{u, v, w}
    R S (r := 1) (fun _ : Fin 1 => f) hflat (by rwa [Set.range_const])
  have hc : (canonicalFunctor.{u, v, w} S (fun _ : Fin 1 => f)).IsEquivalence := by
    change e.functor = canonicalFunctor.{u, v, w} S (fun _ : Fin 1 => f) at he
    rw [← he]
    infer_instance
  have : (canonicalPullbackFunctor.{u, v, w} S f ⋙ pullbackToGlue.{u, v, w} S f).IsEquivalence :=
    Functor.isEquivalence_of_iso (canonicalComparison S f).symm
  have := pullbackToGlue_full.{u, v, w} S f
  have := pullbackToGlue_faithful.{u, v, w} S f
  have := Functor.Full.of_comp_faithful (canonicalPullbackFunctor.{u, v, w} S f)
    (pullbackToGlue.{u, v, w} S f)
  have := Functor.Faithful.of_comp (canonicalPullbackFunctor.{u, v, w} S f)
    (pullbackToGlue.{u, v, w} S f)
  have := Functor.essSurj_of_comp_fully_faithful (canonicalPullbackFunctor.{u, v, w} S f)
    (pullbackToGlue.{u, v, w} S f)
  exact {}

/-- **Stacks 05ES.** For a flat ring map inducing an isomorphism modulo `(f)`, the canonical
functor from modules over the source to pairs of modules identified after localization is an
equivalence of categories. -/
@[stacks 05ES]
public theorem exists_canonicalModuleGlueingEquivalence
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (f : R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap
        ((Ideal.span {f}).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map)) :
    let Rf := Localization.Away f
    let Sf := Localization.Away (algebraMap R S f)
    let ρ := principalLocalizationMap R S f
    letI : Algebra Rf Sf := ρ.toAlgebra
    let generic := ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S)
    let localPiece := ModuleCat.extendScalars.{u, u, max u v w} (algebraMap R Rf)
    let genericOverlap := ModuleCat.extendScalars.{v, v, max u v w} (algebraMap S Sf)
    let localOverlap := ModuleCat.extendScalars.{u, v, max u v w} (algebraMap Rf Sf)
    ∃ comparison : generic ⋙ genericOverlap ≅ localPiece ⋙ localOverlap,
      (∀ (M : ModuleCat.{max u v w} R) (m : M),
        comparison.hom.app M
            ((ModuleCat.extendRestrictScalarsAdj.{max u v w, v, v}
              (algebraMap S Sf)).unit.app
              (generic.obj M)
              ((ModuleCat.extendRestrictScalarsAdj.{max u v w, u, v}
                (algebraMap R S)).unit.app M m)) =
          (ModuleCat.extendRestrictScalarsAdj.{max u v w, u, v}
            (algebraMap Rf Sf)).unit.app
            (localPiece.obj M)
            ((ModuleCat.extendRestrictScalarsAdj.{max u v w, u, u}
              (algebraMap R Rf)).unit.app M m)) ∧
      ((CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
        genericOverlap localOverlap (ModuleCat.{max u v w} R)).obj
        { fst := generic
          snd := localPiece
          iso := comparison }).IsEquivalence := by
  dsimp only
  refine ⟨canonicalPullbackComparison S f, ?_, ?_⟩
  · intro M m
    exact squareComparison_one_tmul _ _ _ _ (localizationMap_comm S f) M m
  · exact canonicalPullbackFunctor_isEquivalence S f hflat hq

end FormalGlueing


end
