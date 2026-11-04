module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSmoothModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisActionFibreCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralSelfMapCohomologyEndo
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportActionNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapTwistRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactUnitSingle

/-!
# The Galois action on the smooth projective model of `X_k̄`

Let `X` be a geometrically connected smooth curve over a field `k`, `j : X ⟶ X̄` a
compactification over `k` and `k̄` an algebraically closed extension of `k`.  The smooth projective
model `C = Stacks.EtaleCohomology.geometricSmoothModel f j k̄` of `X_k̄` is the base change
`C' ×_{k'} k̄` of the smooth projective model `C'` of `X_{k'}` over the perfect closure `k'` of `k`
in `k̄`.  Every `σ ∈ Aut_k(k̄)` fixes `k'`, so `s̃_σ = id_{C'} × Spec σ` is an automorphism of `C`;
it lies over the automorphism `s_σ = id_{X̄} × Spec σ` of `X̄_k̄`
(`Stacks.Frobenius.galoisBaseChange`), restricts to `id_X × Spec σ` on `X_k̄`, and lies over
`Spec σ` on `Spec k̄`.  Like `s_σ`, it is contravariant in `σ`: `s̃_{στ} = s̃_σ ≫ s̃_τ`.

## Main definitions

* `Stacks.EtaleCohomology.geometricSmoothModelGaloisAut` — the automorphism `s̃_σ` of `C`, with
  `_fb`, `_j`, `_q`, `_one`, `_mul` and its `IsIso` instance.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-! ### Galois automorphisms and the base change maps -/

section General

variable {k : Type u} [Field k] (K : Type u) [Field K] [Algebra k K]

/-- `id_Y × Spec σ` over `Y`, with the structure morphism of `Over.mk g` unfolded. -/
private lemma galoisBaseChange_mk_comp_fst {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
    (σ : K ≃ₐ[k] K) :
    galoisBaseChange (Over.mk g) K σ ≫ pullback.fst g (specAlgebraMap k K) =
      pullback.fst g (specAlgebraMap k K) :=
  galoisBaseChange_comp_fst (Over.mk g) K σ

/-- `id_Y × Spec σ` is `Spec σ` on the second factor, with `Over.mk g` unfolded. -/
private lemma galoisBaseChange_mk_comp_snd {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
    (σ : K ≃ₐ[k] K) :
    galoisBaseChange (Over.mk g) K σ ≫ pullback.snd g (specAlgebraMap k K) =
      pullback.snd g (specAlgebraMap k K) ≫ Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) :=
  galoisBaseChange_comp_snd (Over.mk g) K σ

/-- **The base change of a compactification commutes with the Galois action**:
`j' ∘ (id_X × Spec σ) = (id_{X̄} × Spec σ) ∘ j'`. -/
@[reassoc]
public lemma compactificationFieldBaseChangeImmersion_comp_galoisBaseChange {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f)) (σ : K ≃ₐ[k] K) :
    compactificationFieldBaseChangeImmersion f j K ≫ galoisBaseChange (Over.mk j.toBase) K σ =
      galoisBaseChange (Over.mk f) K σ ≫ compactificationFieldBaseChangeImmersion f j K := by
  refine pullback.hom_ext (f := j.toBase) (g := specAlgebraMap k K) ?_ ?_
  · rw [Category.assoc, Category.assoc, galoisBaseChange_mk_comp_fst,
      compactificationFieldBaseChange_immersion_comp_fst,
      reassoc_of% galoisBaseChange_mk_comp_fst K f σ]
  · rw [Category.assoc, Category.assoc, galoisBaseChange_mk_comp_snd,
      compactificationFieldBaseChange_immersion_comp_snd_assoc,
      compactificationFieldBaseChange_immersion_comp_snd, galoisBaseChange_mk_comp_snd]

end General

section PerfectClosure

variable {k : Type u} [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **A `k`-automorphism of `k̄` fixes the perfect closure of `k` in `k̄`**: the perfect closure
is purely inseparable over `k`, so it has a unique `k`-embedding into the reduced ring `k̄`. -/
public lemma algEquiv_apply_perfectClosure (σ : kbar ≃ₐ[k] kbar) (x : perfectClosure k kbar) :
    σ x = x :=
  congrArg (fun φ : perfectClosure k kbar →ₐ[k] kbar => φ x)
    (Subsingleton.elim (σ.toAlgHom.comp (perfectClosure k kbar).val) (perfectClosure k kbar).val)

/-- `Spec σ` lies over `Spec k'` for the perfect closure `k'` of `k` in `k̄`. -/
@[reassoc (attr := simp)]
public lemma specMap_algEquiv_comp_specAlgebraMap_perfectClosure (σ : kbar ≃ₐ[k] kbar) :
    Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫
        specAlgebraMap (perfectClosure k kbar) kbar =
      specAlgebraMap (perfectClosure k kbar) kbar := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact algEquiv_apply_perfectClosure kbar σ x

/-- **`id_Y × Spec σ` lies over `Y_{k'}`** for the perfect closure `k'` of `k` in `k̄`. -/
@[reassoc (attr := simp)]
public lemma galoisBaseChange_comp_fieldTowerBaseChangeMap {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) (σ : kbar ≃ₐ[k] kbar) :
    galoisBaseChange (Over.mk g) kbar σ ≫ fieldTowerBaseChangeMap (perfectClosure k kbar) kbar g =
      fieldTowerBaseChangeMap (perfectClosure k kbar) kbar g := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, fieldTowerBaseChangeMap_fst,
      galoisBaseChange_mk_comp_fst]
  · rw [Category.assoc, fieldTowerBaseChangeMap_snd,
      reassoc_of% galoisBaseChange_mk_comp_snd kbar g σ,
      specMap_algEquiv_comp_specAlgebraMap_perfectClosure]

end PerfectClosure

/-! ### The counit of `f̄^{-1} ⊣ f̄_*` on extensions by zero -/

section Counit

variable (Λ : Type) [Ring Λ]

/-- A morphism between zero objects is an isomorphism. -/
private lemma isIso_of_isZero_of_isZero' {D : Type*} [Category D] [HasZeroMorphisms D] {P Q : D}
    (g : P ⟶ Q) (hP : IsZero P) (hQ : IsZero Q) : IsIso g :=
  ⟨⟨0, hP.eq_of_src _ _, hQ.eq_of_src _ _⟩⟩

/-- In a commutative square whose other three sides are isomorphisms, so is the fourth. -/
private lemma isIso_of_comp_eq_comp_comp {D : Type*} [Category D] {P Q R S U : D} (a : P ⟶ Q)
    (b : Q ⟶ U) (c : P ⟶ R) (d : R ⟶ S) (x : S ⟶ U) [IsIso a] [IsIso b] [IsIso c] [IsIso d]
    (h : a ≫ b = c ≫ d ≫ x) : IsIso x := by
  have : IsIso (c ≫ d ≫ x) := h ▸ inferInstance
  have := IsIso.of_isIso_comp_left c (d ≫ x)
  exact IsIso.of_isIso_comp_left d x

/-- **Inverse image along `g'` of the counit of an integral `i`** is invertible as soon as the
counit along `i'` is, for a cartesian square: after `i'^{-1}`, the invertible base change map
followed by the counit of `i'` is `g'^{-1}` of the counit of `i` up to the comparison
isomorphisms (`Stacks.EtaleCohomology.inverseImage_map_etaleModuleBaseChange_comp_counit`). -/
private theorem isIso_inverseImage_map_counit {Z Z' A A' : Scheme.{u}} (i : Z ⟶ A)
    [IsIntegralHom i] (i' : Z' ⟶ A') (g : A' ⟶ A) (g' : Z' ⟶ Z) (sq : IsPullback i' g' g i)
    (K : EtaleModules.{u, 0} Λ Z)
    [IsIso ((etaleModuleInverseImageAdj.{u, 0} Λ i').counit.app
      ((etaleModuleInverseImage.{u, 0} Λ g').obj K))] :
    IsIso ((etaleModuleInverseImage.{u, 0} Λ g').map
      ((etaleModuleInverseImageAdj.{u, 0} Λ i).counit.app K)) := by
  have := isIso_etaleModuleBaseChange_app_of_isIntegralHom Λ i i' g g' sq K
  exact isIso_of_comp_eq_comp_comp _ _ _ _ _
    (inverseImage_map_etaleModuleBaseChange_comp_counit Λ i i' g g' sq.w K)

/-- **The counit `f̄^{-1} f̄_* (j_{C!} G) ⟶ j_{C!} G` is an isomorphism**: on `X_k̄` it is the
integral base change isomorphism, and on the closed complement both sides vanish. -/
public theorem isIso_geometricSmoothModel_counit {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [GeometricallyConnected f]
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosed kbar] (G : EtaleModules.{u, 0} Λ (pullback f (specAlgebraMap k kbar))) :
    IsIso ((etaleModuleInverseImageAdj.{u, 0} Λ (geometricSmoothModel f j kbar).fb).counit.app
      ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).obj G)) := by
  let C := geometricSmoothModel f j kbar
  let ι := (Scheme.IdealSheafData.vanishingIdeal
      ⟨(Set.range (compactificationFieldBaseChangeImmersion f j kbar).base)ᶜ,
        (compactificationFieldBaseChangeImmersion f j kbar).isOpenEmbedding.isOpen_range
          |>.isClosed_compl⟩).subschemeι
  have hij : Set.range C.j.base = (Set.range (pullback.snd ι C.fb).base)ᶜ := by
    rw [Scheme.Pullback.range_snd, Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_mk,
        Set.preimage_compl, compl_compl]
    exact range_geometricSmoothModel_j f j kbar
  have : (etaleModuleDirectImage.{u, 0} Λ (𝟙 (pullback f (specAlgebraMap k kbar)))).Full :=
    Functor.Full.of_iso (etaleModuleDirectImageIdIso Λ _).symm
  have : (etaleModuleDirectImage.{u, 0} Λ (𝟙 (pullback f (specAlgebraMap k kbar)))).Faithful :=
    Functor.Faithful.of_iso (etaleModuleDirectImageIdIso Λ _).symm
  have := isIso_inverseImage_map_counit Λ C.fb (𝟙 _)
    (compactificationFieldBaseChangeImmersion f j kbar) C.j C.isPullback.flip
    ((etaleModuleExtensionByZero.{u, 0} Λ C.j).obj G)
  have hZ0 : IsZero ((etaleModuleInverseImage.{u, 0} Λ (pullback.snd ι C.fb)).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ C.j).obj G)) :=
    isZero_etaleModuleInverseImage_extensionByZero Λ (pullback.snd ι C.fb) C.j hij G
  have : IsIso ((etaleModuleInverseImageAdj.{u, 0} Λ (pullback.fst ι C.fb)).counit.app
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.snd ι C.fb)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ C.j).obj G))) :=
    isIso_of_isZero_of_isZero' _
      (Functor.map_isZero (etaleModuleInverseImage.{u, 0} Λ (pullback.fst ι C.fb))
        (Functor.map_isZero (etaleModuleDirectImage.{u, 0} Λ (pullback.fst ι C.fb)) hZ0)) hZ0
  have := isIso_inverseImage_map_counit Λ C.fb (pullback.fst ι C.fb) ι
    (pullback.snd ι C.fb) (IsPullback.of_hasPullback ι C.fb)
    ((etaleModuleExtensionByZero.{u, 0} Λ C.j).obj G)
  exact isIso_of_isIso_etaleModuleInverseImage Λ (pullback.snd ι C.fb) C.j hij _

end Counit

/-! ### The automorphism of the smooth projective model -/

section GaloisAut

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar]

/-- **The automorphism `s̃_σ = id_{C'} × Spec σ` of the smooth projective model `C` of `X_k̄`**,
for `σ ∈ Aut_k(k̄)`: on `C = C' ×_{X̄_{k'}} X̄_k̄` it is the identity on the first factor and the
automorphism `s_σ = id_{X̄} × Spec σ` of `X̄_k̄` on the second, which lies over `X̄_{k'}` because
`σ` fixes the perfect closure `k'` of `k` in `k̄`. -/
public def geometricSmoothModelGaloisAut (σ : kbar ≃ₐ[k] kbar) :
    (geometricSmoothModel f j kbar).Vb ⟶ (geometricSmoothModel f j kbar).Vb :=
  (pullback.lift
    (pullback.fst (perfectClosureSmoothModel f j kbar).fb
      (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase))
    (pullback.snd (perfectClosureSmoothModel f j kbar).fb
        (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase) ≫
      galoisBaseChange (Over.mk j.toBase) kbar σ)
    (by
      rw [Category.assoc, galoisBaseChange_comp_fieldTowerBaseChangeMap]
      exact pullback.condition) :
    pullback (perfectClosureSmoothModel f j kbar).fb
        (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase) ⟶
      pullback (perfectClosureSmoothModel f j kbar).fb
        (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase))

/-- `s̃_σ` is the identity on the factor `C'`. -/
@[reassoc (attr := simp)]
public lemma geometricSmoothModelGaloisAut_fst (σ : kbar ≃ₐ[k] kbar) :
    geometricSmoothModelGaloisAut f j kbar σ ≫ geometricSmoothModelFst f j kbar =
      geometricSmoothModelFst f j kbar :=
  pullback.lift_fst _ _ _

/-- **`s̃_σ` lies over `s_σ`**: `f̄ ∘ s̃_σ = s_σ ∘ f̄`. -/
@[reassoc]
public lemma geometricSmoothModelGaloisAut_fb (σ : kbar ≃ₐ[k] kbar) :
    geometricSmoothModelGaloisAut f j kbar σ ≫ (geometricSmoothModel f j kbar).fb =
      (geometricSmoothModel f j kbar).fb ≫ galoisBaseChange (Over.mk j.toBase) kbar σ :=
  pullback.lift_snd _ _ _

/-- **`s̃_σ` restricts to `id_X × Spec σ` on `X_k̄`**: `s̃_σ ∘ j_C = j_C ∘ (id_X × Spec σ)`. -/
@[reassoc]
public lemma geometricSmoothModelGaloisAut_j (σ : kbar ≃ₐ[k] kbar) :
    (geometricSmoothModel f j kbar).j ≫ geometricSmoothModelGaloisAut f j kbar σ =
      galoisBaseChange (Over.mk f) kbar σ ≫ (geometricSmoothModel f j kbar).j := by
  refine geometricSmoothModel_hom_ext f j kbar ?_ ?_
  · rw [Category.assoc, geometricSmoothModelGaloisAut_fst, geometricSmoothModel_j_fst,
      Category.assoc, geometricSmoothModel_j_fst,
      galoisBaseChange_comp_fieldTowerBaseChangeMap_assoc]
  · rw [Category.assoc, geometricSmoothModelGaloisAut_fb, geometricSmoothModel_j_fb_assoc,
      Category.assoc, geometricSmoothModel_j_fb,
      compactificationFieldBaseChangeImmersion_comp_galoisBaseChange]

/-- **`s̃_σ` lies over `Spec σ`**: `q ∘ s̃_σ = Spec σ ∘ q` for the structure morphism
`q : C ⟶ Spec k̄`. -/
@[reassoc]
public lemma geometricSmoothModelGaloisAut_q (σ : kbar ≃ₐ[k] kbar) :
    geometricSmoothModelGaloisAut f j kbar σ ≫ (geometricSmoothModel f j kbar).q =
      (geometricSmoothModel f j kbar).q ≫ Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) := by
  rw [geometricSmoothModel_q, geometricSmoothModelGaloisAut_fb_assoc, Category.assoc]
  exact congrArg ((geometricSmoothModel f j kbar).fb ≫ ·)
    (galoisBaseChange_comp_snd (Over.mk j.toBase) kbar σ)

/-- `s̃_1` is the identity. -/
@[simp]
public lemma geometricSmoothModelGaloisAut_one :
    geometricSmoothModelGaloisAut f j kbar 1 = 𝟙 _ := by
  refine geometricSmoothModel_hom_ext f j kbar ?_ ?_
  · rw [geometricSmoothModelGaloisAut_fst, Category.id_comp]
  · rw [geometricSmoothModelGaloisAut_fb, galoisBaseChange_one]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **The group law**: `s̃_{στ} = s̃_σ ≫ s̃_τ`, contravariant like `s_σ`
(`Stacks.Frobenius.galoisBaseChange_mul`). -/
public lemma geometricSmoothModelGaloisAut_mul (σ τ : kbar ≃ₐ[k] kbar) :
    geometricSmoothModelGaloisAut f j kbar (σ * τ) =
      geometricSmoothModelGaloisAut f j kbar σ ≫ geometricSmoothModelGaloisAut f j kbar τ := by
  refine geometricSmoothModel_hom_ext f j kbar ?_ ?_
  · rw [geometricSmoothModelGaloisAut_fst, Category.assoc, geometricSmoothModelGaloisAut_fst,
      geometricSmoothModelGaloisAut_fst]
  · rw [geometricSmoothModelGaloisAut_fb, Category.assoc, geometricSmoothModelGaloisAut_fb,
      geometricSmoothModelGaloisAut_fb_assoc, galoisBaseChange_mul]

/-- `s̃_σ` is an automorphism, with inverse `s̃_{σ⁻¹}`. -/
public instance isIso_geometricSmoothModelGaloisAut (σ : kbar ≃ₐ[k] kbar) :
    IsIso (geometricSmoothModelGaloisAut f j kbar σ) :=
  ⟨⟨geometricSmoothModelGaloisAut f j kbar σ⁻¹,
    by rw [← geometricSmoothModelGaloisAut_mul, mul_inv_cancel, geometricSmoothModelGaloisAut_one],
    by rw [← geometricSmoothModelGaloisAut_mul, inv_mul_cancel, geometricSmoothModelGaloisAut_one]⟩⟩

end GaloisAut

/-! ### The twist on a complex concentrated in degree zero -/

section Single

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B] (P : A ⥤ B) (S : B ⥤ B)
  [P.Additive] [S.Additive] (τ : P ⟶ P ⋙ S)

/-- The degreewise action of a transformation `τ : P ⟶ P ⋙ S` on `P(M[0])` is `τ_M` placed in
degree zero, through the identifications `P(M[0]) ≅ (P M)[0]` and `S((P M)[0]) ≅ (S P M)[0]`. -/
theorem mapHomologicalComplex_singlePlus_comp (M : A) :
    ObjectProperty.homMk (X := P.mapCochainComplexPlus.obj
        ((Stacks.DerivedIndexing.singlePlusFunctor A 0).obj M))
      (Y := S.mapCochainComplexPlus.obj (P.mapCochainComplexPlus.obj
        ((Stacks.DerivedIndexing.singlePlusFunctor A 0).obj M)))
      ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
        ((Stacks.DerivedIndexing.singlePlusFunctor A 0).obj M).obj) ≫
        S.mapCochainComplexPlus.map (mapCochainComplexPlusSinglePlusIso P M).hom ≫
        (mapCochainComplexPlusSinglePlusIso S (P.obj M)).hom =
      (mapCochainComplexPlusSinglePlusIso P M).hom ≫
        (Stacks.DerivedIndexing.singlePlusFunctor B 0).map (τ.app M) := by
  rw [← cancel_epi (mapCochainComplexPlusSinglePlusIso P M).inv, Iso.inv_hom_id_assoc]
  refine ObjectProperty.hom_ext _ ?_
  show (HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) 0).inv.app M ≫
      (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M) ≫
      (S.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) 0).hom.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex S (ComplexShape.up ℤ) 0).hom.app (P.obj M) =
    (HomologicalComplex.single B (ComplexShape.up ℤ) 0).map (τ.app M)
  refine HomologicalComplex.from_single_hom_ext ?_
  have hτ := τ.naturality (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom
  dsimp only [Functor.comp_map, Functor.comp_obj] at hτ
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self, Category.assoc, Functor.map_comp]
  rw [← reassoc_of% hτ]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rfl

end Single

/-! ### The Galois action on the cohomology of the smooth model -/

section GaloisAction

attribute [local instance] HasDerivedCategory.standard
attribute [local instance high] etaleModules_hasSheafify

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] (Λ : Type) [Ring Λ]

/-- The Galois base change `id × Spec σ` of the compactification is integral, being an
isomorphism. -/
instance (σ : kbar ≃ₐ[k] kbar) : IsIntegralHom (galoisBaseChange (Over.mk j.toBase) kbar σ) :=
  haveI : IsIso (galoisBaseChange (Over.mk j.toBase) kbar σ) :=
    ⟨⟨galoisBaseChange (Over.mk j.toBase) kbar σ⁻¹,
      by rw [← galoisBaseChange_mul, mul_inv_cancel, galoisBaseChange_one],
      by rw [← galoisBaseChange_mul, inv_mul_cancel, galoisBaseChange_one]⟩⟩
  inferInstance

/-- The Galois automorphism of the geometric smooth model is integral. -/
instance (σ : kbar ≃ₐ[k] kbar) : IsIntegralHom (geometricSmoothModelGaloisAut f j kbar σ) :=
  inferInstance

/-- **The structure morphism `q : C ⟶ X̄`** of the smooth model over the compactification:
`f̄ : C ⟶ X̄_k̄` followed by the projection `X̄_k̄ ⟶ X̄`. -/
public abbrev geometricSmoothModelProj :=
  (geometricSmoothModel f j kbar).fb ≫ pullback.fst j.toBase (specAlgebraMap k kbar)

/-- `s̃_σ` lies over `X̄`. -/
public lemma geometricSmoothModelGaloisAut_comp_proj (σ : kbar ≃ₐ[k] kbar) :
    geometricSmoothModelGaloisAut f j kbar σ ≫ geometricSmoothModelProj f j kbar =
      geometricSmoothModelProj f j kbar := by
  rw [geometricSmoothModelProj, geometricSmoothModelGaloisAut_fb_assoc]
  exact congrArg ((geometricSmoothModel f j kbar).fb ≫ ·)
    (galoisBaseChange_comp_fst (Over.mk j.toBase) kbar σ)

/-- The middle of `galoisCompactSupportSmoothModelIso`:
`(j_! F)|_{X̄_k̄} ≅ j'_!(F|_{X_k̄}) ≅ f̄_* j_{C!}(F|_{X_k̄})`. -/
public def geometricSmoothModelRestrictionIso (F : EtaleModules.{u, 0} Λ X) :
    (etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F) ≅
      (etaleModuleDirectImage.{u, 0} Λ (geometricSmoothModel f j kbar).fb).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).obj
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F)) :=
  (compactificationFieldBaseChangeExtensionByZeroIso Λ f j kbar).symm.app F ≪≫
    extensionByZeroGeometricSmoothModelIso f j kbar Λ _

/-- The restriction map `(j_! F)|_{X̄_k̄} ⟶ f̄_* q^{-1}(j_! F)` of the smooth model. -/
public abbrev geometricSmoothModelRestriction (F : EtaleModules.{u, 0} Λ X) :=
  (selfMapRestriction.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))
    (geometricSmoothModel f j kbar).fb (geometricSmoothModelProj f j kbar) rfl).app
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)

/-- **`q^{-1}(j_! F) ≅ j_{C!}(F|_{X_k̄})`**: the adjoint, under `f̄^{-1} ⊣ f̄_*`, of
`Stacks.EtaleCohomology.geometricSmoothModelRestrictionIso`, read through
`q^{-1} = f̄^{-1} ∘ pr^{-1}`.  It is invertible because the counit of `f̄` is invertible on
`j_{C!}(F|_{X_k̄})`. -/
public def geometricSmoothModelInverseImageIso (F : EtaleModules.{u, 0} Λ X) :
    (etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F) ≅
      (etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F) :=
  haveI := isIso_geometricSmoothModel_counit Λ f j kbar
    ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F)
  haveI : IsIso (((etaleModuleInverseImageAdj.{u, 0} Λ (geometricSmoothModel f j kbar).fb).homEquiv
      _ _).symm (geometricSmoothModelRestrictionIso f j kbar Λ F).hom) := by
    rw [Adjunction.homEquiv_counit]
    infer_instance
  (selfMapRestrictionIso.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))
      (geometricSmoothModel f j kbar).fb (geometricSmoothModelProj f j kbar) rfl).symm.app
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F) ≪≫
    asIso (((etaleModuleInverseImageAdj.{u, 0} Λ (geometricSmoothModel f j kbar).fb).homEquiv
      _ _).symm (geometricSmoothModelRestrictionIso f j kbar Λ F).hom)

/-- **The restriction map followed by `f̄_*` of `q^{-1}(j_! F) ≅ j_{C!}(F|_{X_k̄})` is the middle
of `galoisCompactSupportSmoothModelIso`.** -/
public theorem geometricSmoothModelRestriction_comp_inverseImageIso (F : EtaleModules.{u, 0} Λ X) :
    geometricSmoothModelRestriction f j kbar Λ F ≫
        (etaleModuleDirectImage.{u, 0} Λ (geometricSmoothModel f j kbar).fb).map
          (geometricSmoothModelInverseImageIso f j kbar Λ F).hom =
      (geometricSmoothModelRestrictionIso f j kbar Λ F).hom := by
  have hk : (selfMapRestrictionIso.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))
        (geometricSmoothModel f j kbar).fb (geometricSmoothModelProj f j kbar) rfl).hom.app
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F) ≫
        (geometricSmoothModelInverseImageIso f j kbar Λ F).hom =
      ((etaleModuleInverseImageAdj.{u, 0} Λ (geometricSmoothModel f j kbar).fb).homEquiv
        _ _).symm (geometricSmoothModelRestrictionIso f j kbar Λ F).hom :=
    Iso.hom_inv_id_app_assoc _ _ _
  dsimp only [geometricSmoothModelRestriction]
  rw [selfMapRestriction_app, Category.assoc, ← Functor.map_comp, hk, ← Adjunction.homEquiv_unit,
    Equiv.apply_symm_apply]

/-- **The action of `σ ∈ Aut_k(k̄)` on `H^i(C, j_{C!}(F|_{X_k̄}))`**: pullback along the
automorphism `s̃_σ = id_{C'} × Spec σ` of the smooth model.  The sheaf
`j_{C!}(F|_{X_k̄}) ≅ q^{-1}(j_! F)` is pulled back along `q : C ⟶ X̄` and `s̃_σ` lies over `X̄`,
so it carries the canonical `s̃_σ`-linearization, the twist
`q^{-1}(j_! F) ⟶ (s̃_σ)_* q^{-1}(j_! F)` adjoint to `s̃_σ^{-1} q^{-1} ≅ q^{-1}`
(`Stacks.EtaleCohomology.selfMapTwist`); the action is `H^i(C, -)` of it followed by
`H^i(C, (s̃_σ)_* -) ≅ H^i(C, -)` (`Stacks.EtaleCohomology.integralSelfMapCohomologyEndo`),
transported along `q^{-1}(j_! F) ≅ j_{C!}(F|_{X_k̄})`. -/
public def geometricSmoothModelGaloisAction (σ : kbar ≃ₐ[k] kbar) (F : EtaleModules.{u, 0} Λ X)
    (i : ℤ) :
    ((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
        i).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F)) ⟶
    ((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
        i).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F)) :=
  ((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
      i).map (geometricSmoothModelInverseImageIso f j kbar Λ F).inv ≫
    integralSelfMapCohomologyEndo Λ (geometricSmoothModelGaloisAut f j kbar σ) _
      ((selfMapTwist.{u, 0} Λ (geometricSmoothModelProj f j kbar)
        (geometricSmoothModelGaloisAut f j kbar σ)
        (geometricSmoothModelGaloisAut_comp_proj f j kbar σ)).app
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) i ≫
    ((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
      i).map (geometricSmoothModelInverseImageIso f j kbar Λ F).hom

end GaloisAction

end Stacks.EtaleCohomology

end
