module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.HomComplex.Basic
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Homology.HomComplex.DerivedInternalHom
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.TensorComplex.ExactFunctor
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.HomComplex.Currying
public import StacksFrontier.Homology.HomComplex.DerivedTensorHom
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.TorAmplitude.KFlatRepresentative
public import StacksFrontier.Homology.TensorComplex.TensorUnitIso
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange.HomComplexChangeOfRings
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.HomComplexChangeOfRings

/-!
# The change-of-rings isomorphism for derived Hom

For `f : R → A`, `Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso` (Stacks 0E1W) is
the canonical isomorphism of bifunctors on `D(R)ᵒᵖ × D(A)` whose components are the isomorphisms
`RHom_R(K, M) ≅ RHom_A(K ⊗ᴸ_R A, M)` regarded in `D(R)`, in independent ring and module
universes; `F` may be any total left-derived model of extension of scalars. It is the scalar
transport of `Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso`, the descent along the
localization of the homotopy categories of the comparison
`Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso` on K-flat and K-injective
representatives; `Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_hom_app_eq_homComplex`
computes it there by the localized Hom-complex comparison.

## References

* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

open StacksDraft.DerivedHom.Construction (KInjectiveObjects Q_map_surjective_of_isKInjective
    postcomp_bijective postcomp_quasiIso_of_homotopyEquivalence precomp_bijective
    precomp_quasiIso_of_homotopyEquivalence)

section DerivedHomChangeOfRings

open CategoryTheory CategoryTheory.Limits StacksDraft.DerivedHom

namespace Stacks.DerivedHom.BaseChange

universe uR uA uM

attribute [local instance] HasDerivedCategory.standard

open CochainComplex HomComplex

section DerivedHomModels

universe u

/-- From `eK : X ≅ Q K` and `eI : Y ≅ Q I` with `I` K-injective, the derived internal Hom of
`X` and `Y` is isomorphic to the image in the derived category of the Hom complex of `K` and
`I`. -/
@[expose]
public noncomputable def homModelIso
    {R : Type u} [CommRing R] {X Y : DerivedCategory (ModuleCat.{u} R)}
    (K I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective] (eK : X ≅ DerivedCategory.Q.obj K)
    (eI : Y ≅ DerivedCategory.Q.obj I) :
    (DerivedInternalHom.Model.hom R).obj (Opposite.op X, Y) ≅
      DerivedCategory.Q.obj (HomComplexR R K I) :=
  (DerivedInternalHom.Model.hom R).mapIso (eK.symm.op.prod eI) ≪≫
    _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.Model.homComplexIso K I

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

/-- Restriction of scalars along `f` is a right adjoint, with left adjoint extension of scalars. -/
local instance : (ModuleCat.restrictScalars.{u, u, u} f).IsRightAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).isRightAdjoint
/-- Restriction of scalars along `f` is a left adjoint, with right adjoint coextension of
scalars. -/
local instance : (ModuleCat.restrictScalars.{u, u, u} f).IsLeftAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} f).isLeftAdjoint

set_option backward.isDefEq.respectTransparency false in
/-- The canonical change-of-rings isomorphism on K-flat and K-injective representatives. -/
@[expose]
public noncomputable def derivedHomChangeOfRingsModelIso
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (α : DerivedCategory.Q ⋙ F ⟶ CochainComplex.extendScalarsLarge.{u, u, u} f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I)
    [J.IsKInjective] [I.IsKInjective] [QuasiIso q] (hK : K.KFlat) :
    (DerivedInternalHom.Model.hom R).obj
        (Opposite.op (DerivedCategory.Q.obj K),
          (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategory.obj
            (DerivedCategory.Q.obj J)) ≅
      (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategory.obj
        ((DerivedInternalHom.Model.hom A).obj
          (Opposite.op (F.obj (DerivedCategory.Q.obj K)), DerivedCategory.Q.obj J)) := by
  let U := (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategory
  let β := (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors
  have : IsIso (α.app K) := isIso_extendScalarsCounit_app_of_kFlat f F α K hK
  have := quasiIso_homComplexChangeOfRingsMap_of_kFlat.{u, u, u} f K J I q F α hK
  let eR := homModelIso K I (Iso.refl _)
    (β.app J ≪≫ asIso (DerivedCategory.Q.map q))
  let eA := homModelIso ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J
    (asIso (α.app K)) (Iso.refl _)
  exact eR ≪≫ (asIso (DerivedCategory.Q.map
      (homComplexChangeOfRingsMap.{u, u, u} f K J I q))).symm ≪≫
    (β.app (HomComplexR A ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J)).symm ≪≫
    (U.mapIso eA).symm

end DerivedHomModels

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition commutes with a commuting square of postcomposition maps. -/
private theorem homComplex_precomp_postcomp_naturality
    {R : Type*} [CommRing R]
    {K K' L L' I I' : CochainComplex (ModuleCat.{uM} R) ℤ}
    (a : K' ⟶ K) (b : L ⟶ L') (c : I ⟶ I') (q : L ⟶ I) (q' : L' ⟶ I')
    (h : b ≫ q' = q ≫ c) :
    (Stacks.HomComplex.TensorHomMap.precomp R K' K L a ≫ Stacks.HomComplex.TensorHomMap.postcomp R
      K' L L' b) ≫
        Stacks.HomComplex.TensorHomMap.postcomp R K' L' I' q' =
      Stacks.HomComplex.TensorHomMap.postcomp R K L I q ≫
        (Stacks.HomComplex.TensorHomMap.precomp R K' K I a ≫ Stacks.HomComplex.TensorHomMap.postcomp
          R K' I I' c) := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p r hpr
  show (((Cochain.ofHom a).comp z (zero_add n)).comp (Cochain.ofHom b)
      (add_zero n) |>.comp (Cochain.ofHom q') (add_zero n)).v p r hpr =
    (((Cochain.ofHom a).comp (z.comp (Cochain.ofHom q) (add_zero n)) (zero_add n)).comp
      (Cochain.ofHom c) (add_zero n)).v p r hpr
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Category.assoc]
  have hr := congrArg (fun w : L ⟶ I' => w.f r) h
  change b.f r ≫ q'.f r = q.f r ≫ c.f r at hr
  rw [hr]

set_option backward.isDefEq.respectTransparency false in
/-- The change-of-rings comparison is natural in all representative maps. -/
private theorem homComplexChangeOfRingsMap_naturality
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    {K K' : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ}
    {J J' : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ}
    {I I' : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ}
    (a : K' ⟶ K) (b : J ⟶ J') (c : I ⟶ I')
    (q : (CochainComplex.restrictScalarsLarge.{uM, uR, uA} f).obj J ⟶ I)
    (q' : (CochainComplex.restrictScalarsLarge.{uM, uR, uA} f).obj J' ⟶ I')
    (h : (CochainComplex.restrictScalarsLarge.{uM, uR, uA} f).map b ≫ q' = q ≫ c) :
    (CochainComplex.restrictScalarsLarge.{uM, uR, uA} f).map
        (Stacks.HomComplex.TensorHomMap.precomp A _ _ _
            ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).map a) ≫
          Stacks.HomComplex.TensorHomMap.postcomp A _ _ _ b) ≫
      homComplexChangeOfRingsMap.{uR, uA, uM} f K' J' I' q' =
    homComplexChangeOfRingsMap.{uR, uA, uM} f K J I q ≫
      (Stacks.HomComplex.TensorHomMap.precomp R K' K I a ≫ Stacks.HomComplex.TensorHomMap.postcomp R
        K' I I' c) := by
  dsimp only [homComplexChangeOfRingsMap]
  rw [← Category.assoc, homComplexExtendRestrictScalarsMap_naturality,
    Category.assoc, homComplex_precomp_postcomp_naturality a _ c q q' h,
    Category.assoc]

/-- Equality after localization into a K-injective target is equality up to homotopy. -/
private noncomputable def homotopyOfDerivedMapEq
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {K I : CochainComplex C ℤ} [I.IsKInjective] {f g : K ⟶ I}
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) : Homotopy f g := by
  apply HomotopyCategory.homotopyOfEq
  apply (homotopyToDerivedEquiv K I).injective
  simpa only [homotopyToDerivedEquiv_map] using h

noncomputable section Descent

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory.Functor

private abbrev C (R : Type u) [CommRing R] := CochainComplex (ModuleCat.{u} R) ℤ
private abbrev KC (R : Type u) [CommRing R] := HomotopyCategory (ModuleCat.{u} R) (.up ℤ)
private abbrev homotopyEquivalences (R : Type u) [CommRing R] :=
  HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (.up ℤ)

private noncomputable abbrev kInjectiveQ (R : Type u) [CommRing R] :
    (KInjectiveObjects R).FullSubcategory ⥤ DerivedCategory (ModuleCat.{u} R) :=
  (KInjectiveObjects R).ι ⋙ DerivedCategory.Qh

private lemma kInjectiveQ_map_bijective (R : Type u) [CommRing R]
    (X Y : (KInjectiveObjects R).FullSubcategory) :
    Function.Bijective ((kInjectiveQ R).map : (X ⟶ Y) → _) := by
  let : CochainComplex.IsKInjective Y.obj.as := Y.property
  exact (CochainComplex.IsKInjective.Qh_map_bijective X.obj Y.obj.as).comp
    (Functor.FullyFaithful.ofFullyFaithful (KInjectiveObjects R).ι).homEquiv.bijective

private lemma kInjectiveQ_full (R : Type u) [CommRing R] : (kInjectiveQ R).Full where
  map_surjective := (kInjectiveQ_map_bijective R _ _).surjective

private lemma kInjectiveQ_faithful (R : Type u) [CommRing R] : (kInjectiveQ R).Faithful where
  map_injective h := (kInjectiveQ_map_bijective R _ _).injective h

private lemma kInjectiveQ_essSurj (R : Type u) [CommRing R] : (kInjectiveQ R).EssSurj := by
  refine ⟨fun X => ?_⟩
  obtain ⟨I, f, hf, hI⟩ := CochainComplex.exists_quasiIso_isKInjective
    (DerivedCategory.Q.objPreimage X)
  let := hf
  refine ⟨⟨(HomotopyCategory.quotient _ _).obj I, hI⟩, ⟨?_⟩⟩
  exact (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app I ≪≫
    (asIso (DerivedCategory.Q.map f)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso X

attribute [local instance] kInjectiveQ_full kInjectiveQ_faithful kInjectiveQ_essSurj

private lemma homClassesMap_precomp {R : Type u} [CommRing R] {K K' L : C R}
    (f : K' ⟶ K) (n : ℤ) (z : Cocycle K L n) :
    StacksDraft.DerivedHom.Construction.homClassesMap
        (Stacks.HomComplex.TensorHomMap.precomp R K' K L f) n (CohomologyClass.mk z) =
      CohomologyClass.mk (z.precomp f) := rfl

private lemma homClassesMap_precomp_toHom {R : Type u} [CommRing R] {K K' L : C R}
    (f : K' ⟶ K) (n : ℤ) (z : CohomologyClass K L n) :
    CohomologyClass.toHom (StacksDraft.DerivedHom.Construction.homClassesMap
        (Stacks.HomComplex.TensorHomMap.precomp R K' K L f) n z) =
      (HomotopyCategory.quotient _ _).map f ≫ CohomologyClass.toHom z := by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  rw [homClassesMap_precomp, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_precomp, Functor.map_comp]
  rfl

private lemma homClassesMap_precomp_bijective {R : Type u} [CommRing R] {K K' I : C R}
    (f : K' ⟶ K) (n : ℤ)
    (hf : Function.Bijective (fun g : (HomotopyCategory.quotient _ _).obj K ⟶
        (HomotopyCategory.quotient _ _).obj (I⟦n⟧) =>
      (HomotopyCategory.quotient _ _).map f ≫ g)) :
    Function.Bijective (StacksDraft.DerivedHom.Construction.homClassesMap
        (Stacks.HomComplex.TensorHomMap.precomp R K' K I f) n) := by
  apply (Function.Bijective.of_comp_iff' (CohomologyClass.toHom_bijective K' I n) _).1
  simpa only [Function.comp_def, homClassesMap_precomp_toHom] using
    hf.comp (CohomologyClass.toHom_bijective K I n)

private noncomputable abbrev complexHomToDerived (R : Type u) [CommRing R] :
    (C R)ᵒᵖ ⥤ C R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  curry.obj (StacksDraft.DerivedHom.Model.homComplexFunctor R ⋙
    (DerivedCategory.Q (C := ModuleCat.{u} R)))

private lemma complexHomToDerived_inverts (R : Type u) [CommRing R] :
    MorphismProperty.IsInvertedBy₂ (homotopyEquivalences R).op (homotopyEquivalences R)
      (complexHomToDerived R) := by
  rintro ⟨K, I⟩ ⟨K', I'⟩ ⟨f, g⟩ ⟨hf, hg⟩
  have := precomp_quasiIso_of_homotopyEquivalence (I := I) f.unop hf
  have := postcomp_quasiIso_of_homotopyEquivalence (K := K'.unop) g hg
  apply (NatIso.isIso_map_iff
    (currying.counitIso.app
      (StacksDraft.DerivedHom.Model.homComplexFunctor R ⋙ DerivedCategory.Q)) (f, g)).2
  show IsIso (DerivedCategory.Q.map
    (Stacks.HomComplex.TensorHomMap.precomp R K'.unop K.unop I f.unop ≫
      Stacks.HomComplex.TensorHomMap.postcomp R K'.unop I I' g))
  infer_instance

private noncomputable def homotopyHom (R : Type u) [CommRing R] :
    (KC R)ᵒᵖ ⥤ KC R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Localization.lift₂ (complexHomToDerived R) (complexHomToDerived_inverts R)
    (HomotopyCategory.quotient _ _).op (HomotopyCategory.quotient _ _)

@[instance_reducible]
private noncomputable def homotopyHomLifting (R : Type u) [CommRing R] :
    Localization.Lifting₂ (HomotopyCategory.quotient _ _).op (HomotopyCategory.quotient _ _)
      (homotopyEquivalences R).op (homotopyEquivalences R)
      (complexHomToDerived R) (homotopyHom R) := by
  unfold homotopyHom
  infer_instance

attribute [local instance] homotopyHomLifting

private noncomputable def homotopyHomComparison (R : Type u) [CommRing R] :=
  Localization.Lifting₂.iso (HomotopyCategory.quotient _ _).op (HomotopyCategory.quotient _ _)
    (homotopyEquivalences R).op (homotopyEquivalences R)
    (complexHomToDerived R) (homotopyHom R)

/-- Homotopic maps induce the same localized maps of Hom complexes. -/
private theorem homComplex_map_eq_of_homotopy
    {R : Type u} [CommRing R]
    {K K' I I' : C R} {a a' : K' ⟶ K} {b b' : I ⟶ I'}
    (ha : Homotopy a a') (hb : Homotopy b b') :
    DerivedCategory.Q.map ((StacksDraft.DerivedHom.Model.homComplexFunctor R).map
        (CategoryTheory.Prod.mkHom a.op b)) =
      DerivedCategory.Q.map ((StacksDraft.DerivedHom.Model.homComplexFunctor R).map
        (CategoryTheory.Prod.mkHom a'.op b')) := by
  let e := uncurry.mapIso (homotopyHomComparison R)
  have h₁ := e.hom.naturality (show (Opposite.op K, I) ⟶ (Opposite.op K', I') from (a.op, b))
  have h₂ := e.hom.naturality (show (Opposite.op K, I) ⟶ (Opposite.op K', I') from (a'.op, b'))
  have ha' := HomotopyCategory.eq_of_homotopy a a' ha
  have hb' := HomotopyCategory.eq_of_homotopy b b' hb
  dsimp at h₁ h₂
  rw [ha', hb'] at h₁
  apply (cancel_epi (e.hom.app (Opposite.op K, I))).1
  simpa only [← Functor.map_comp_assoc, ← Functor.map_comp,
    CategoryTheory.Prod.mkHom, CategoryTheory.prod_comp, Category.comp_id, Category.id_comp] using
      h₁.symm.trans h₂

private theorem homComplexFunctor_map_id_left
    {R : Type u} [CommRing R] (K : C R) {I I' : C R} (a : I ⟶ I') :
    (StacksDraft.DerivedHom.Model.homComplexFunctor R).map
        (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op K)) a) =
      Stacks.HomComplex.TensorHomMap.postcomp R K I I' a := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p q hpq
  simp [StacksDraft.DerivedHom.Model.homComplexFunctor, Stacks.HomComplex.TensorHomMap.precomp,
    Stacks.HomComplex.TensorHomMap.postcomp]
  rfl

private theorem homComplexChangeOfRingsMap_naturality_localized
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    {K K' : C R} {J J' : C A} {I I' : C R}
    (a : K' ⟶ K) (b : J ⟶ J') (c : I ⟶ I')
    (q : (CochainComplex.restrictScalarsLarge f).obj J ⟶ I)
    (q' : (CochainComplex.restrictScalarsLarge f).obj J' ⟶ I')
    (h : Homotopy ((CochainComplex.restrictScalarsLarge f).map b ≫ q') (q ≫ c)) :
    DerivedCategory.Q.map ((CochainComplex.restrictScalarsLarge f).map
        (Stacks.HomComplex.TensorHomMap.precomp A _ _ _ ((CochainComplex.extendScalarsLarge f).map
          a) ≫
          Stacks.HomComplex.TensorHomMap.postcomp A _ _ _ b)) ≫
      DerivedCategory.Q.map (homComplexChangeOfRingsMap f K' J' I' q') =
    DerivedCategory.Q.map (homComplexChangeOfRingsMap f K J I q) ≫
      DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.precomp R K' K I a ≫
        Stacks.HomComplex.TensorHomMap.postcomp R K' I I' c) := by
  let H := StacksDraft.DerivedHom.Model.homComplexFunctor R
  have hn := congrArg DerivedCategory.Q.map
    (homComplexExtendRestrictScalarsMap_naturality f a b)
  rw [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp] at hn
  dsimp only [homComplexChangeOfRingsMap]
  rw [DerivedCategory.Q.map_comp (homComplexExtendRestrictScalarsMap f K' J') _,
    ← Category.assoc, hn, Category.assoc,
    DerivedCategory.Q.map_comp (homComplexExtendRestrictScalarsMap f K J) _]
  rw [← homComplexFunctor_map_id_left K' q', ← homComplexFunctor_map_id_left K q]
  show DerivedCategory.Q.map (homComplexExtendRestrictScalarsMap f K J) ≫
      DerivedCategory.Q.map (H.map
        (CategoryTheory.Prod.mkHom a.op ((CochainComplex.restrictScalarsLarge f).map b))) ≫
      DerivedCategory.Q.map (H.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op K')) q')) =
    (DerivedCategory.Q.map (homComplexExtendRestrictScalarsMap f K J) ≫
      DerivedCategory.Q.map (H.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op K)) q))) ≫
      DerivedCategory.Q.map (H.map (CategoryTheory.Prod.mkHom a.op c))
  simp only [Category.assoc, ← Functor.map_comp, CategoryTheory.Prod.mkHom,
    CategoryTheory.prod_comp, Category.comp_id, Category.id_comp]
  simpa only [Functor.map_comp] using congrArg
    (fun z => DerivedCategory.Q.map (homComplexExtendRestrictScalarsMap f K J) ≫ z)
    (homComplex_map_eq_of_homotopy (Homotopy.refl a) h)
set_option backward.isDefEq.respectTransparency false in
private theorem homModelIso_naturality
    {R : Type u} [CommRing R] {X X' Y Y' : DerivedCategory (ModuleCat.{u} R)}
    {K K' I I' : C R} [I.IsKInjective] [I'.IsKInjective]
    (eK : X ≅ DerivedCategory.Q.obj K) (eK' : X' ≅ DerivedCategory.Q.obj K')
    (eI : Y ≅ DerivedCategory.Q.obj I) (eI' : Y' ≅ DerivedCategory.Q.obj I')
    (a : K' ⟶ K) (b : I ⟶ I') (g : X' ⟶ X) (h : Y ⟶ Y')
    (hg : g ≫ eK.hom = eK'.hom ≫ DerivedCategory.Q.map a)
    (hh : h ≫ eI'.hom = eI.hom ≫ DerivedCategory.Q.map b) :
    (DerivedInternalHom.Model.hom R).map (CategoryTheory.Prod.mkHom g.op h) ≫
      (homModelIso K' I' eK' eI').hom =
    (homModelIso K I eK eI).hom ≫
      DerivedCategory.Q.map ((StacksDraft.DerivedHom.Model.homComplexFunctor R).map
        (CategoryTheory.Prod.mkHom a.op b)) := by
  have hg' : eK'.inv ≫ g = DerivedCategory.Q.map a ≫ eK.inv := by
    apply (cancel_mono eK.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hg, Iso.inv_hom_id_assoc]
  dsimp only [homModelIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Functor.map_comp_assoc]
  have hp : (g.op, h) ≫ (eK'.symm.op.prod eI').hom =
      (eK.symm.op.prod eI).hom ≫ ((DerivedCategory.Q.map a).op, DerivedCategory.Q.map b) :=
    Prod.ext (congrArg Quiver.Hom.op hg') hh
  rw [hp, Functor.map_comp_assoc]
  simpa only [Category.assoc, DerivedInternalHom.Model.hom,
    _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.Model.homComplexIso,
      StacksDraft.DerivedHom.Model.homComplexFunctor,
    CategoryTheory.Prod.mkHom, Quiver.Hom.unop_op] using
    congrArg (fun z => (DerivedInternalHom.Model.hom R).map
    (eK.symm.op.prod eI).hom ≫ z)
    ((DerivedInternalHom.Model.adjunction R).homIso_naturality a b)

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
/-- Restriction of scalars along `f` is a right adjoint, with left adjoint extension of scalars. -/
local instance : (ModuleCat.restrictScalars.{u,u,u} f).IsRightAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u,u,u} f).isRightAdjoint
/-- Restriction of scalars along `f` is a left adjoint, with right adjoint coextension of
scalars. -/
local instance : (ModuleCat.restrictScalars.{u,u,u} f).IsLeftAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{u,u,u} f).isLeftAdjoint

variable (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (α : DerivedCategory.Q ⋙ F ⟶ CochainComplex.extendScalarsLarge f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))]

/-- The bifunctor `(X, Y) ↦ RHom_R(X, Y)` on `D(R)ᵒᵖ × D(A)`, where `Y` is viewed over `R` by
restriction of scalars along `f`. -/
public abbrev homRestrictSource :=
  (Functor.id (DerivedCategory (ModuleCat.{u} R))ᵒᵖ).prod
    (ModuleCat.restrictScalars.{u,u,u} f).mapDerivedCategory ⋙ DerivedInternalHom.Model.hom R
/-- The bifunctor `(X, Y) ↦ RHom_A(F X, Y)` on `D(R)ᵒᵖ × D(A)`, followed by restriction of
scalars along `f`. -/
public abbrev homRestrictTarget :=
  F.op.prod (Functor.id (DerivedCategory (ModuleCat.{u} A))) ⋙
    DerivedInternalHom.Model.hom A ⋙ (ModuleCat.restrictScalars.{u,u,u} f).mapDerivedCategory

set_option backward.isDefEq.respectTransparency false in
private theorem modelIso_inv_naturality
    {K K' : C R} {J J' : C A} {I I' : C R}
    [J.IsKInjective] [J'.IsKInjective] [I.IsKInjective] [I'.IsKInjective]
    (q : (CochainComplex.restrictScalarsLarge f).obj J ⟶ I)
    (q' : (CochainComplex.restrictScalarsLarge f).obj J' ⟶ I') [QuasiIso q] [QuasiIso q']
    (hK : K.KFlat) (hK' : K'.KFlat) (a : K' ⟶ K) (b : J ⟶ J') (c : I ⟶ I')
    (hc : DerivedCategory.Q.map ((CochainComplex.restrictScalarsLarge f).map b) ≫
        DerivedCategory.Q.map q' = DerivedCategory.Q.map q ≫ DerivedCategory.Q.map c) :
    (homRestrictTarget f F).map
        (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map a).op (DerivedCategory.Q.map b)) ≫
      (derivedHomChangeOfRingsModelIso f F α K' J' I' q' hK').inv =
    (derivedHomChangeOfRingsModelIso f F α K J I q hK).inv ≫
      (homRestrictSource f).map
        (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map a).op (DerivedCategory.Q.map b)) := by
  let U := (ModuleCat.restrictScalars.{u,u,u} f).mapDerivedCategory
  let β := (ModuleCat.restrictScalars.{u,u,u} f).mapDerivedCategoryFactors
  have : IsIso (α.app K) := isIso_extendScalarsCounit_app_of_kFlat f F α K hK
  have : IsIso (α.app K') := isIso_extendScalarsCounit_app_of_kFlat f F α K' hK'
  let eR := homModelIso K I (Iso.refl _) (β.app J ≪≫ asIso (DerivedCategory.Q.map q))
  let eR' := homModelIso K' I' (Iso.refl _) (β.app J' ≪≫ asIso (DerivedCategory.Q.map q'))
  let eA := homModelIso ((CochainComplex.extendScalarsLarge f).obj K) J
    (asIso (α.app K)) (Iso.refl _)
  let eA' := homModelIso ((CochainComplex.extendScalarsLarge f).obj K') J'
    (asIso (α.app K')) (Iso.refl _)
  let r := Stacks.HomComplex.TensorHomMap.precomp R K' K I a ≫
    Stacks.HomComplex.TensorHomMap.postcomp R K' I I' c
  let t := Stacks.HomComplex.TensorHomMap.precomp A _ _ _ ((CochainComplex.extendScalarsLarge f).map
    a) ≫
    Stacks.HomComplex.TensorHomMap.postcomp A _ _ _ b
  have hr : (homRestrictSource f).map
        (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map a).op (DerivedCategory.Q.map b)) ≫
      eR'.hom = eR.hom ≫ DerivedCategory.Q.map r := by
    apply homModelIso_naturality _ _ _ _ a c _ _ (by simp)
    dsimp only [Iso.trans_hom, Iso.app_hom, asIso_hom]
    rw [← Category.assoc, mapDerivedCategoryFactors_hom_naturality, Category.assoc]
    simpa only [Category.assoc, CochainComplex.restrictScalarsLarge] using
      congrArg (fun z => β.hom.app J ≫ z) hc
  have ht : (DerivedInternalHom.Model.hom A).map
      (CategoryTheory.Prod.mkHom (F.map (DerivedCategory.Q.map a)).op
        (DerivedCategory.Q.map b)) ≫ eA'.hom =
      eA.hom ≫ DerivedCategory.Q.map t := by
    apply homModelIso_naturality _ _ _ _ ((CochainComplex.extendScalarsLarge f).map a) b _ _
    · exact α.naturality a
    · simp
  have hn := homComplexChangeOfRingsMap_naturality_localized f a b c q q'
    (homotopyOfDerivedMapEq (by simpa only [Functor.map_comp] using hc))
  suffices hn' : U.map ((DerivedInternalHom.Model.hom A).map
      (CategoryTheory.Prod.mkHom (F.map (DerivedCategory.Q.map a)).op (DerivedCategory.Q.map b))) ≫
      (U.map eA'.hom ≫ β.hom.app _ ≫
        DerivedCategory.Q.map (homComplexChangeOfRingsMap f K' J' I' q') ≫ eR'.inv) =
    U.map eA.hom ≫ β.hom.app _ ≫
        DerivedCategory.Q.map (homComplexChangeOfRingsMap f K J I q) ≫ eR.inv ≫
      (homRestrictSource f).map
        (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map a).op (DerivedCategory.Q.map b)) by
    simpa only [eA, eA', eR, eR', derivedHomChangeOfRingsModelIso,
      Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.trans_hom,
      Functor.mapIso_hom, Iso.symm_hom, asIso_hom, Category.assoc,
      homRestrictTarget, homRestrictSource, U, β,
      Functor.comp_map, Functor.prod_map, Functor.op_map, Functor.id_map,
      CategoryTheory.Prod.mkHom, Quiver.Hom.unop_op, Iso.app_hom] using hn'
  apply (cancel_mono eR'.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hr]
  simp only [Iso.inv_hom_id_assoc]
  rw [← U.map_comp_assoc, ht, U.map_comp_assoc]
  rw [mapDerivedCategoryFactors_hom_naturality_assoc]
  simpa only [Functor.comp_map, Functor.comp_obj, Category.assoc, r, t,
    CochainComplex.restrictScalarsLarge] using
    congrArg (fun z => U.map eA.hom ≫ β.hom.app _ ≫ z) hn

private abbrev HomotopyModels (R A : Type u) [CommRing R] [CommRing A] :=
  (CochainComplex.DerivedTensor.kFlatHomotopyObjects R).FullSubcategoryᵒᵖ ×
    (KInjectiveObjects A).FullSubcategory

private noncomputable abbrev homotopyModelsQ (R A : Type u) [CommRing R] [CommRing A] :=
  (CochainComplex.DerivedTensor.kFlatHomotopyQ R).op.prod (kInjectiveQ A)

private abbrev homotopyModelsW (R A : Type u) [CommRing R] [CommRing A] :=
  (CochainComplex.DerivedTensor.kFlatHomotopyQuasiIso R).op.prod
    (MorphismProperty.isomorphisms (KInjectiveObjects A).FullSubcategory)

private theorem homotopyModelsQ_isLocalization (R A : Type u) [CommRing R] [CommRing A] :
    (homotopyModelsQ R A).IsLocalization (homotopyModelsW R A) := by
  have := CochainComplex.DerivedTensor.kFlatHomotopyQ_isLocalization R
  have : (kInjectiveQ A).IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  have : (kInjectiveQ A).IsLocalization
      (MorphismProperty.isomorphisms (KInjectiveObjects A).FullSubcategory) :=
    Functor.IsLocalization.of_isEquivalence _ _ le_rfl
  infer_instance

private noncomputable def homotopyModelsIso (X : HomotopyModels R A) :
    (homotopyModelsQ R A).obj X ≅
      (Opposite.op (DerivedCategory.Q.obj X.1.unop.obj.as), DerivedCategory.Q.obj X.2.obj.as) :=
  ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app X.1.unop.obj.as).symm.op.prod
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app X.2.obj.as)

private theorem homotopyModelsIso_naturality {X Y : HomotopyModels R A} (g : X ⟶ Y) :
    (homotopyModelsQ R A).map g ≫ (homotopyModelsIso Y).hom =
      (homotopyModelsIso X).hom ≫
        (CategoryTheory.Prod.mkHom
          (DerivedCategory.Q.map g.1.unop.hom.out).op (DerivedCategory.Q.map g.2.hom.out)) := by
  apply Prod.ext
  · apply Quiver.Hom.unop_inj
    show (DerivedCategory.quotientCompQhIso _).inv.app Y.1.unop.obj.as ≫
        DerivedCategory.Qh.map g.1.unop.hom =
      DerivedCategory.Q.map g.1.unop.hom.out ≫
        (DerivedCategory.quotientCompQhIso _).inv.app X.1.unop.obj.as
    simpa only [Functor.comp_map, HomotopyCategory.quotient_map_out] using
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.naturality g.1.unop.hom.out).symm
  · show DerivedCategory.Qh.map g.2.hom ≫
        (DerivedCategory.quotientCompQhIso _).hom.app Y.2.obj.as =
      (DerivedCategory.quotientCompQhIso _).hom.app X.2.obj.as ≫
        DerivedCategory.Q.map g.2.hom.out
    simpa only [Functor.comp_map, HomotopyCategory.quotient_map_out] using
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).hom.naturality g.2.hom.out

-- Elaborating the two-variable localization diagram requires a larger heartbeat budget.
/-- The scalar-adjunction comparison descends in both derived variables. -/
public noncomputable def modelRestrictScalarsNatIso :
    homRestrictSource f ≅ homRestrictTarget f F := by
  let Uc := CochainComplex.restrictScalarsLarge.{u,u,u} f
  choose I q hq hI using fun X : HomotopyModels R A =>
    CochainComplex.exists_quasiIso_isKInjective (Uc.obj X.2.obj.as)
  have (X : HomotopyModels R A) : QuasiIso (q X) := hq X
  have (X : HomotopyModels R A) : (I X).IsKInjective := hI X
  have (X : HomotopyModels R A) : CochainComplex.IsKInjective X.2.obj.as := X.2.property
  let e (X : HomotopyModels R A) :=
    (derivedHomChangeOfRingsModelIso f F α X.1.unop.obj.as X.2.obj.as
      (I X) (q X) X.1.unop.property).symm
  let E : homotopyModelsQ R A ⋙ homRestrictTarget f F ≅
      homotopyModelsQ R A ⋙ homRestrictSource f := NatIso.ofComponents
    (fun X => (homRestrictTarget f F).mapIso (homotopyModelsIso X) ≪≫ e X ≪≫
      ((homRestrictSource f).mapIso (homotopyModelsIso X)).symm) (by
      intro X Y g
      let a := g.1.unop.hom.out
      let b := g.2.hom.out
      obtain ⟨c, hc⟩ :=
        StacksDraft.DerivedHom.Construction.Q_map_surjective_of_isKInjective (I X) (I Y)
        (inv (DerivedCategory.Q.map (q X)) ≫ DerivedCategory.Q.map (Uc.map b) ≫
          DerivedCategory.Q.map (q Y))
      apply StacksDraft.DerivedHom.Construction.naturality_transport (homRestrictTarget f F)
          (homRestrictSource f)
        (homotopyModelsIso X) (homotopyModelsIso Y) (e X) (e Y)
        ((homotopyModelsQ R A).map g)
        (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map a).op (DerivedCategory.Q.map b))
        (homotopyModelsIso_naturality g)
      apply modelIso_inv_naturality f F α (q X) (q Y) X.1.unop.property Y.1.unop.property a b c
      rw [hc, IsIso.hom_inv_id_assoc])
  haveI := homotopyModelsQ_isLocalization R A
  exact (Localization.liftNatIso (homotopyModelsQ R A) (homotopyModelsW R A)
    (homotopyModelsQ R A ⋙ homRestrictTarget f F)
    (homotopyModelsQ R A ⋙ homRestrictSource f) (homRestrictTarget f F)
    (homRestrictSource f) E).symm

set_option backward.isDefEq.respectTransparency false in
/-- The representative comparison does not depend on the chosen K-injective target. -/
public theorem derivedHomChangeOfRingsModelIso_hom_eq
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I I' : CochainComplex (ModuleCat.{u} R) ℤ) [J.IsKInjective] [I.IsKInjective] [I'.IsKInjective]
    (q : (CochainComplex.restrictScalarsLarge f).obj J ⟶ I)
    (q' : (CochainComplex.restrictScalarsLarge f).obj J ⟶ I') [QuasiIso q] [QuasiIso q']
    (hK : K.KFlat) :
    (derivedHomChangeOfRingsModelIso f F α K J I q hK).hom =
      (derivedHomChangeOfRingsModelIso f F α K J I' q' hK).hom := by
  obtain ⟨c, hc⟩ := StacksDraft.DerivedHom.Construction.Q_map_surjective_of_isKInjective I I'
    (inv (DerivedCategory.Q.map q) ≫ DerivedCategory.Q.map q')
  have h := modelIso_inv_naturality f F α q q' hK hK (𝟙 K) (𝟙 J) c
    (by rw [hc]; simp)
  have h' : (derivedHomChangeOfRingsModelIso f F α K J I' q' hK).inv =
      (derivedHomChangeOfRingsModelIso f F α K J I q hK).inv := by
    have e : CategoryTheory.Prod.mkHom (DerivedCategory.Q.map (𝟙 K)).op
        (DerivedCategory.Q.map (𝟙 J)) = 𝟙 _ := by
      apply Prod.ext <;> simp
    rw [e] at h
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id] at h
    exact h
  rw [← Iso.inv_eq_inv]
  exact h'.symm

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 200000 in
/-- On a K-flat representative and a K-injective representative, the descended comparison is
the canonical comparison of Hom complexes, for any K-injective resolution of the restriction. -/
public theorem modelRestrictScalarsNatIso_hom_app
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [J.IsKInjective] [I.IsKInjective]
    (q : (CochainComplex.restrictScalarsLarge f).obj J ⟶ I) [QuasiIso q] (hK : K.KFlat) :
    (modelRestrictScalarsNatIso f F α).hom.app
        (Opposite.op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj J) =
      (derivedHomChangeOfRingsModelIso f F α K J I q hK).hom := by
  let X : HomotopyModels R A :=
    (Opposite.op ⟨(HomotopyCategory.quotient _ _).obj K, hK⟩,
      ⟨(HomotopyCategory.quotient _ _).obj J, ‹J.IsKInjective›⟩)
  have h1 := (modelRestrictScalarsNatIso f F α).hom.naturality (homotopyModelsIso X).hom
  rw [← cancel_epi ((homRestrictSource f).map (homotopyModelsIso X).hom)]
  refine h1.trans ?_
  have := homotopyModelsQ_isLocalization R A
  rw [← Functor.mapIso_hom, ← Iso.eq_comp_inv]
  dsimp only [modelRestrictScalarsNatIso, Iso.symm_hom, Localization.liftNatIso]
  rw [Localization.liftNatTrans_app]
  simp only [Localization.Lifting.iso, Iso.refl_hom,
    Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id,
    NatIso.ofComponents_inv_app, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Functor.mapIso_hom, Category.assoc]
  congr 2
  obtain ⟨_, _⟩ := Classical.choose_spec (Classical.choose_spec
    (CochainComplex.exists_quasiIso_isKInjective ((CochainComplex.restrictScalarsLarge f).obj J)))
  exact derivedHomChangeOfRingsModelIso_hom_eq f F α K J _ I _ q hK

set_option backward.isDefEq.respectTransparency false in
/-- On a K-flat representative and a K-injective representative, the descended comparison is
the Hom-complex localization formula: the canonical representative isomorphism, the inverse of
the localized scalar-adjunction comparison, the inverse restriction factor, and the restricted
inverse model isomorphism over the larger ring. -/
public theorem modelRestrictScalarsNatIso_hom_app_eq_homComplex
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) [J.IsKInjective] [I.IsKInjective]
    (q : (CochainComplex.restrictScalarsLarge f).obj J ⟶ I) [QuasiIso q] (hK : K.KFlat) :
    letI : IsIso (α.app K) := isIso_extendScalarsCounit_app_of_kFlat f F α K hK
    letI := quasiIso_homComplexChangeOfRingsMap_of_kFlat.{u, u, u} f K J I q F α hK
    (modelRestrictScalarsNatIso f F α).hom.app
        (Opposite.op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj J) =
      (homModelIso K I (Iso.refl _)
        ((ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.app J ≪≫
          asIso (DerivedCategory.Q.map q))).hom ≫
      inv (DerivedCategory.Q.map (homComplexChangeOfRingsMap.{u, u, u} f K J I q)) ≫
      ((ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategoryFactors.app
        (HomComplexR A ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J)).inv ≫
      (ModuleCat.restrictScalars.{u, u, u} f).mapDerivedCategory.map
        (homModelIso ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J
          (asIso (α.app K)) (Iso.refl _)).inv := by
  rw [modelRestrictScalarsNatIso_hom_app f F α K J I q hK]
  rfl

end Descent

noncomputable section ScalarTransport
open CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false

/-- An isomorphism between exact composites induces the corresponding derived comparison. -/
private def derivedFunctorCompIso
    {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₁ ⥤ C₃)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : F ⋙ G ≅ H) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C₁ (.up ℤ))
    (DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ G.mapDerivedCategory))
    (DerivedCategory.Q ⋙ H.mapDerivedCategory)
    (F.mapDerivedCategory ⋙ G.mapDerivedCategory) H.mapDerivedCategory
    ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (Functor.mapHomologicalComplexCompIso e (.up ℤ)) DerivedCategory.Q ≪≫
      H.mapDerivedCategoryFactors.symm)

/-- Scalar lifts commute with restriction, with the underlying module carrier fixed. -/
public def scalarRestrictionIso
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM,uR,uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM,uR,uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA,max uR uA uM}
      A).inverse ⋙
        (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory ≅
      (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory ⋙
        (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,max uR uA uM}
          R).inverse := by
  intro f'
  let upR := (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).symm.toRingHom
  let upA := (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom
  let U := ModuleCat.restrictScalars.{max uR uA uM} f
  let U' := ModuleCat.restrictScalars.{max uR uA uM} f'
  let RA := ModuleCat.restrictScalars.{max uR uA uM} upA
  let RR := ModuleCat.restrictScalars.{max uR uA uM} upR
  let H := ModuleCat.restrictScalars.{max uR uA uM} (upA.comp f)
  haveI : U.IsRightAdjoint := (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f).isRightAdjoint
  haveI : U.IsLeftAdjoint := (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f).isLeftAdjoint
  haveI : U'.IsRightAdjoint := (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
  haveI : U'.IsLeftAdjoint := (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
  haveI : H.IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} (upA.comp f)).isRightAdjoint
  haveI : H.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} (upA.comp f)).isLeftAdjoint
  exact derivedFunctorCompIso RA U H (ModuleCat.restrictScalarsComp f upA).symm ≪≫
    (derivedFunctorCompIso U' RR H
      (ModuleCat.restrictScalarsComp' upR f' (upA.comp f) (by ext r; rfl)).symm).symm

/-- **Stacks 0E1W.** The canonical change-of-rings isomorphism for derived Hom, natural in
the object of `D(R)` in the contravariant variable and the object of `D(A)` in the covariant
variable. Its right-hand side uses any total left-derived extension-of-scalars functor; such a
functor is left adjoint to derived restriction of scalars by Stacks 0GMT. -/
@[stacks 0E1V "the change-of-rings isomorphism for derived hom", stacks 0E1W, expose]
public noncomputable def derivedHomRestrictScalarsNatIso
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))],
    Functor.prod
        (Functor.id (DerivedCategory (ModuleCat.{max uR uA uM} R))ᵒᵖ)
        (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory ⋙
        _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR, max uR uA uM} R ≅
      Functor.prod F.op (Functor.id (DerivedCategory (ModuleCat.{max uR uA uM} A))) ⋙
        _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uA, max uR uA uM} A ⋙
        (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory := by
  intro F comparison hF
  letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
  letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
  letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
  let a := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
    f F comparison
  letI := a.isLeftAdjoint
  letI := a.isRightAdjoint
  letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
  let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,max uR uA uM}
    R
  let S := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA,max uR uA uM}
    A
  let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
    (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
  let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
  letI : (ModuleCat.extendScalars.{max uR uA uM,max uR uA uM,max uR uA uM} f').IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isLeftAdjoint
  letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
  letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
  let V := (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
    (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
      (ULift.{max uR uA uM} A)) ℤ)
  let a' := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction f' T.B T.alphaB
  let δ : S.inverse ⋙ U ≅ V ⋙ E.inverse := scalarRestrictionIso.{uR,uA,uM} f
  let τ : U ⋙ E.functor ≅ S.functor ⋙ V :=
    Iso.compInverseIso (H := E.symm)
      ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
        (Functor.associator _ _ _).symm)
  let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
    (E.toAdjunction.comp a').leftAdjointUniq ((a.comp S.toAdjunction).ofNatIsoRight δ)
  let HR := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
  let HA := DerivedInternalHom.Model.hom (ULift.{max uR uA uM} A)
  let e₁ := Functor.isoWhiskerRight (NatIso.prod (Iso.refl E.functor.op) τ) (HR ⋙ E.inverse)
  let e₂ := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (E.functor.op.prod S.functor)
      (modelRestrictScalarsNatIso f' T.B T.alphaB)) E.inverse
  let e₃ := Functor.isoWhiskerRight
    (NatIso.prod (NatIso.op eF.symm) (Iso.refl S.functor)) (HA ⋙ V ⋙ E.inverse)
  let e₄ := Functor.isoWhiskerLeft (((F ⋙ S.functor).op.prod S.functor) ⋙ HA) δ.symm
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

end ScalarTransport

end Stacks.DerivedHom.BaseChange

end DerivedHomChangeOfRings
