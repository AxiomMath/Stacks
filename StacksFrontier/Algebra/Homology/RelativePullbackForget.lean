module

public import StacksFrontier.Algebra.Homology.RelativePullbackMap
public import StacksFrontier.AlgebraicGeometry.AffineMorphismCohomology.ResolutionDesc
public import StacksFrontier.AlgebraicGeometry.AffineMorphismCohomology.AcyclicQuasiIso

/-!
# Right derived functors along an exact functor, on resolutions

Let `U : 𝒳 ⥤ 𝒴` be an exact additive functor and `Q : 𝒴 ⥤ ℬ` an additive functor. For an
object `X` of `𝒳` with injective resolution `I`, the complex `U I` is a resolution of `U X`, not
in general by injective objects, and a comparison `κ : U I ⟶ J` with an injective resolution `J`
of `U X` induces

`Rⁿ(U ⋙ Q)(X) = Hⁿ(Q (U I)) ⟶ Hⁿ(Q J) = Rⁿ Q (U X)`.

This map is invertible when `U` carries injective objects to `Q`-acyclic ones.

This map is compatible with the maps of `Stacks.Cohomology.RelativePullback.map`: for
`H : 𝒳₂ ⥤ 𝒳₁` and `H' : 𝒴₂ ⥤ 𝒴₁` preserving injective objects with `H ⋙ U₁ ≅ U₂ ⋙ H'`, the map
attached to `ψ : M ⟶ H N` on the `𝒳` side corresponds to the map attached to `U₁ ψ` on the `𝒴`
side, which is the composite of `Rⁿ Q (U₁ ψ)` with the edge morphism of `H' ⋙ Q`.

## Main definitions

* `Stacks.ResolutionDesc.homotopyToComplex`: a homotopy between two comparisons from a resolution
  into a complex with injective terms which agree on the augmentation.
* `Stacks.Cohomology.RelativePullback.forgetComparison`: the comparison `U I ⟶ J`.
* `Stacks.Cohomology.RelativePullback.forgetMap`: the induced map
  `Rⁿ(U ⋙ Q)(X) ⟶ Rⁿ Q (U X)`.

## Main results

* `Stacks.Cohomology.RelativePullback.isIso_forgetMap`: `forgetMap` is invertible when `U`
  carries injective objects to `Q`-acyclic objects.
* `Stacks.Cohomology.RelativePullback.map_comp_forgetMap`: the compatibility with `map` and the
  edge morphism described above.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 01FA](https://stacks.math.columbia.edu/tag/01FA)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits HomologicalComplex

namespace Stacks.ResolutionDesc

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {B : C} {K : CochainComplex C ℕ}
  (ι : (CochainComplex.single₀ C).obj B ⟶ K) [QuasiIso ι]
  {T : CochainComplex C ℕ} [∀ n, Injective (T.X n)]

/-! ### Uniqueness of comparisons into a complex with injective terms -/

/-- Auxiliary construction for `Stacks.ResolutionDesc.homotopyZeroToComplex`. -/
def homotopyZeroZeroToComplex (φ : K ⟶ T) (comm : ι.f 0 ≫ φ.f 0 = 0) : K.X 1 ⟶ T.X 0 :=
  (exact₀ ι).descToInjective (φ.f 0) comm

/-- The differential `K⁰ ⟶ K¹` followed by `homotopyZeroZeroToComplex` is `φ⁰`. -/
@[reassoc (attr := simp)]
lemma d_comp_homotopyZeroZeroToComplex (φ : K ⟶ T) (comm : ι.f 0 ≫ φ.f 0 = 0) :
    K.d 0 1 ≫ homotopyZeroZeroToComplex ι φ comm = φ.f 0 :=
  (exact₀ ι).comp_descToInjective _ _

/-- The differential `K⁰ ⟶ K¹` kills `φ¹ - h⁰ ≫ d`, where `h⁰ = homotopyZeroZeroToComplex`. -/
lemma d_comp_homotopyZeroOneToComplex_aux (φ : K ⟶ T) (comm : ι.f 0 ≫ φ.f 0 = 0) :
    K.d 0 1 ≫ (φ.f 1 - homotopyZeroZeroToComplex ι φ comm ≫ T.d 0 1) = 0 := by
  rw [Preadditive.comp_sub, d_comp_homotopyZeroZeroToComplex_assoc ι φ comm,
    HomologicalComplex.Hom.comm, sub_self]

/-- Auxiliary construction for `Stacks.ResolutionDesc.homotopyZeroToComplex`. -/
def homotopyZeroOneToComplex (φ : K ⟶ T) (comm : ι.f 0 ≫ φ.f 0 = 0) : K.X 2 ⟶ T.X 1 :=
  (exact_succ ι 0).descToInjective (φ.f 1 - homotopyZeroZeroToComplex ι φ comm ≫ T.d 0 1)
    (d_comp_homotopyZeroOneToComplex_aux ι φ comm)

/-- The differential `K¹ ⟶ K²` followed by `homotopyZeroOneToComplex` is `φ¹ - h⁰ ≫ d`, where
`h⁰ = homotopyZeroZeroToComplex`. -/
@[reassoc (attr := simp)]
lemma d_comp_homotopyZeroOneToComplex (φ : K ⟶ T) (comm : ι.f 0 ≫ φ.f 0 = 0) :
    K.d 1 2 ≫ homotopyZeroOneToComplex ι φ comm =
      φ.f 1 - homotopyZeroZeroToComplex ι φ comm ≫ T.d 0 1 :=
  (exact_succ ι 0).comp_descToInjective _ _

omit [∀ n, Injective (T.X n)] in
/-- If `φⁿ⁺¹ = d ≫ g' + g ≫ d`, then the differential `Kⁿ⁺¹ ⟶ Kⁿ⁺²` kills `φⁿ⁺² - g' ≫ d`. -/
lemma d_comp_homotopyZeroSuccToComplex_aux (φ : K ⟶ T) (n : ℕ) (g : K.X (n + 1) ⟶ T.X n)
    (g' : K.X (n + 2) ⟶ T.X (n + 1))
    (w : φ.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ T.d n (n + 1)) :
    K.d (n + 1) (n + 2) ≫ (φ.f (n + 2) - g' ≫ T.d (n + 1) (n + 2)) = 0 := by
  rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, w, Preadditive.add_comp,
    assoc, assoc, HomologicalComplex.d_comp_d, comp_zero, add_zero, sub_self]

/-- Auxiliary construction for `Stacks.ResolutionDesc.homotopyZeroToComplex`. -/
def homotopyZeroSuccToComplex (φ : K ⟶ T) (n : ℕ) (g : K.X (n + 1) ⟶ T.X n)
    (g' : K.X (n + 2) ⟶ T.X (n + 1))
    (w : φ.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ T.d n (n + 1)) :
    K.X (n + 3) ⟶ T.X (n + 2) :=
  (exact_succ ι (n + 1)).descToInjective (φ.f (n + 2) - g' ≫ T.d (n + 1) (n + 2))
    (d_comp_homotopyZeroSuccToComplex_aux φ n g g' w)

/-- The differential `Kⁿ⁺² ⟶ Kⁿ⁺³` followed by `homotopyZeroSuccToComplex` is
`φⁿ⁺² - g' ≫ d`. -/
@[reassoc (attr := simp)]
lemma d_comp_homotopyZeroSuccToComplex (φ : K ⟶ T) (n : ℕ) (g : K.X (n + 1) ⟶ T.X n)
    (g' : K.X (n + 2) ⟶ T.X (n + 1))
    (w : φ.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ T.d n (n + 1)) :
    K.d (n + 2) (n + 3) ≫ homotopyZeroSuccToComplex ι φ n g g' w =
      φ.f (n + 2) - g' ≫ T.d (n + 1) (n + 2) :=
  (exact_succ ι (n + 1)).comp_descToInjective _ _

/-- A comparison from a resolution into a complex with injective terms killing the
augmentation is homotopic to zero. -/
def homotopyZeroToComplex (φ : K ⟶ T) (comm : ι.f 0 ≫ φ.f 0 = 0) : Homotopy φ 0 :=
  Homotopy.mkCoinductive _ (homotopyZeroZeroToComplex ι φ comm) (by simp)
    (homotopyZeroOneToComplex ι φ comm) (by simp) (fun n ⟨g, g', w⟩ ↦
      ⟨homotopyZeroSuccToComplex ι φ n g g' (by simp only [w, add_comm]), by simp⟩)

/-- Two comparisons from a resolution into a complex with injective terms which agree on the
augmentation are homotopic. -/
def homotopyToComplex (φ φ' : K ⟶ T) (h : ι.f 0 ≫ φ.f 0 = ι.f 0 ≫ φ'.f 0) :
    Homotopy φ φ' :=
  Homotopy.equivSubZero.invFun (homotopyZeroToComplex ι (φ - φ') (by
    rw [HomologicalComplex.sub_f_apply, Preadditive.comp_sub, h, sub_self]))

/-- Two comparisons from a resolution into a complex with injective terms which agree on the
augmentation induce the same map on the homology of any additive functor applied termwise. -/
lemma homologyMap_map_eq_of_injective {E : Type*} [Category* E] [Abelian E] (Q : C ⥤ E)
    [Q.Additive] (φ φ' : K ⟶ T) (h : ι.f 0 ≫ φ.f 0 = ι.f 0 ≫ φ'.f 0) (n : ℕ) :
    homologyMap ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) n =
      homologyMap ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map φ') n :=
  (Q.mapHomotopy (homotopyToComplex ι φ φ' h)).homologyMap_eq n

/-- The comparison of a resolution with an injective resolution of the same object is a
quasi-isomorphism. -/
lemma quasiIso_desc (J : InjectiveResolution B) : QuasiIso (desc ι J) := by
  have h : ι ≫ desc ι J = J.ι :=
    HomologicalComplex.from_single_hom_ext (by rw [comp_f, f_zero_comp_desc_f_zero])
  have : QuasiIso (ι ≫ desc ι J) := h ▸ inferInstance
  exact quasiIso_of_comp_left ι (desc ι J)

end Stacks.ResolutionDesc

namespace Stacks.Cohomology.RelativePullback

open RightDerivedCoEdge

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

/-- The comparison of a complex with the image of the identity functor is the identity. -/
lemma homologyToMapHomology_id {ℬ : Type*} [Category* ℬ] [Abelian ℬ] (C : CochainComplex ℬ ℕ)
    (i : ℕ) : homologyToMapHomology (𝟭 ℬ) C i = 𝟙 _ := by
  have hc : mapCycles (𝟭 ℬ) C i = 𝟙 _ := by
    rw [← cancel_mono ((((𝟭 ℬ).mapHomologicalComplex _).obj C).iCycles i)]
    exact (mapCycles_i (𝟭 ℬ) C i).trans (id_comp _).symm
  rw [← cancel_epi ((((𝟭 ℬ).mapHomologicalComplex _).obj C).homologyπ i),
    homologyπ_comp_homologyToMapHomology, mapCyclesIso, asIso_inv]
  simp only [hc, IsIso.inv_id, comp_id]
  exact (id_comp _).trans rfl

section Forget

variable {𝒳 : Type u₁} [Category.{v₁} 𝒳] [Abelian 𝒳] [HasInjectiveResolutions 𝒳]
  {𝒴 : Type u₂} [Category.{v₂} 𝒴] [Abelian 𝒴] [HasInjectiveResolutions 𝒴]
  {ℬ : Type u₃} [Category.{v₃} ℬ] [Abelian ℬ]
  (U : 𝒳 ⥤ 𝒴) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (Q : 𝒴 ⥤ ℬ) [Q.Additive]

/-- The augmentation `U X ⟶ U I` of the image under the exact functor `U` of the chosen
injective resolution `I` of `X`. -/
def forgetAug (X : 𝒳) :
    (CochainComplex.single₀ 𝒴).obj (U.obj X) ⟶
      (U.mapHomologicalComplex _).obj (injectiveResolution X).cocomplex :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨U.map (aug (injectiveResolution X)), by
      change U.map _ ≫ U.map _ = 0
      rw [← U.map_comp]
      exact (congrArg U.map (injectiveResolution X).ι_f_zero_comp_complex_d).trans (U.map_zero _ _)⟩

omit [HasInjectiveResolutions 𝒴] [PreservesFiniteLimits U] [PreservesFiniteColimits U] in
/-- The degree-zero component of `forgetAug U X` is `U` applied to the augmentation of the chosen
injective resolution of `X`. -/
@[simp]
lemma forgetAug_f_zero (X : 𝒳) : (forgetAug U X).f 0 = U.map (aug (injectiveResolution X)) :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- The augmentation `forgetAug U X` is a quasi-isomorphism. -/
instance quasiIso_forgetAug (X : 𝒳) : QuasiIso (forgetAug U X) := by
  have : U.PreservesHomology := Functor.preservesHomologyOfExact U
  have h : forgetAug U X = (HomologicalComplex.singleMapHomologicalComplex U
      (ComplexShape.up ℕ) 0).inv.app X ≫
        (U.mapHomologicalComplex _).map (injectiveResolution X).ι := by
    refine HomologicalComplex.from_single_hom_ext ?_
    rw [forgetAug_f_zero, comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
    simp [aug]
  rw [h]
  infer_instance

/-- The comparison of `U I` with the chosen injective resolution of `U X`. -/
def forgetComparison (X : 𝒳) :
    (U.mapHomologicalComplex _).obj (injectiveResolution X).cocomplex ⟶
      (injectiveResolution (U.obj X)).cocomplex :=
  Stacks.ResolutionDesc.desc (forgetAug U X) (injectiveResolution (U.obj X))

/-- In degree zero, `forgetComparison U X` carries the image under `U` of the augmentation of
the injective resolution of `X` to the augmentation of the injective resolution of `U X`. -/
@[reassoc]
lemma map_aug_comp_forgetComparison_f_zero (X : 𝒳) :
    U.map (aug (injectiveResolution X)) ≫ (forgetComparison U X).f 0 =
      aug (injectiveResolution (U.obj X)) := by
  rw [← forgetAug_f_zero]
  exact Stacks.ResolutionDesc.f_zero_comp_desc_f_zero _ _

/-- The map `Rⁿ(U ⋙ Q)(X) ⟶ Rⁿ Q (U X)` induced by the comparison of `U I` with an injective
resolution of `U X`. -/
def forgetMap (X : 𝒳) (n : ℕ) :
    ((U ⋙ Q).rightDerived n).obj X ⟶ (Q.rightDerived n).obj (U.obj X) :=
  (rdIso (injectiveResolution X) (U ⋙ Q) n).hom ≫
    homologyMap ((Q.mapHomologicalComplex _).map (forgetComparison U X)) n ≫
      (rdIso (injectiveResolution (U.obj X)) Q n).inv

attribute [local instance] HasDerivedCategory.standard in
attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso in
/-- `forgetMap U Q X n` is invertible when `U` carries injective objects to `Q`-acyclic objects. -/
theorem isIso_forgetMap [EnoughInjectives 𝒴] [PreservesFiniteLimits Q]
    (hU : ∀ I : 𝒳, Injective I → Q.rightAcyclic (U.obj I)) (X : 𝒳) (n : ℕ) :
    IsIso (forgetMap U Q X n) := by
  have : QuasiIso (forgetComparison U X) :=
    Stacks.ResolutionDesc.quasiIso_desc (forgetAug U X) (injectiveResolution (U.obj X))
  have := Stacks.AcyclicQuasiIso.isIso_homologyMap_map Q (forgetComparison U X)
    (fun k ↦ hU _ inferInstance)
    (fun k ↦ Stacks.Cohomology.Leray.rightAcyclic_of_injective Q _ inferInstance) n
  unfold forgetMap
  infer_instance

end Forget

section Compat

variable {𝒳₁ : Type u₁} [Category.{v₁} 𝒳₁] [Abelian 𝒳₁] [HasInjectiveResolutions 𝒳₁]
  {𝒳₂ : Type u₂} [Category.{v₂} 𝒳₂] [Abelian 𝒳₂] [HasInjectiveResolutions 𝒳₂]
  {𝒴₁ : Type u₃} [Category.{v₃} 𝒴₁] [Abelian 𝒴₁] [HasInjectiveResolutions 𝒴₁]
  {𝒴₂ : Type u₄} [Category.{v₄} 𝒴₂] [Abelian 𝒴₂] [HasInjectiveResolutions 𝒴₂]
  {ℬ : Type u₅} [Category.{v₅} ℬ] [Abelian ℬ]
  (U₁ : 𝒳₁ ⥤ 𝒴₁) [U₁.Additive] [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  (U₂ : 𝒳₂ ⥤ 𝒴₂) [U₂.Additive] [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  (H : 𝒳₁ ⥤ 𝒳₂) [H.Additive] [H.PreservesInjectiveObjects]
  (Ha : 𝒴₁ ⥤ 𝒴₂) [Ha.Additive] [Ha.PreservesInjectiveObjects]
  (ξ : H ⋙ U₂ ≅ U₁ ⋙ Ha) (Q : 𝒴₂ ⥤ ℬ) [Q.Additive]
  (e : H ⋙ U₂ ⋙ Q ≅ (U₁ ⋙ Ha ⋙ Q) ⋙ 𝟭 ℬ) (he : ∀ Z, e.hom.app Z = Q.map (ξ.hom.app Z))

include he in
/-- The map of `Stacks.Cohomology.RelativePullback.map` attached to `ψ : M ⟶ H N`, followed by the
comparison for `N`, is the comparison for `M` followed by `Rⁿ Q (U₂ ψ)` and the edge morphism of
`Ha ⋙ Q`. -/
theorem map_comp_forgetMap {M : 𝒳₂} {N : 𝒳₁} (ψ : M ⟶ H.obj N) (n : ℕ) :
    map (U₂ ⋙ Q) (U₁ ⋙ Ha ⋙ Q) H (𝟭 ℬ) e ψ n ≫ forgetMap U₁ (Ha ⋙ Q) N n =
      forgetMap U₂ Q M n ≫ (Q.rightDerived n).map (U₂.map ψ ≫ ξ.hom.app N) ≫
        (RightDerivedEdge.edge Ha Q n).app (U₁.obj N) := by
  let J₂ := injectiveResolution M
  let J₁ := injectiveResolution N
  let A₂ := injectiveResolution (U₂.obj M)
  let A₁ := injectiveResolution (U₁.obj N)
  let Bq := injectiveResolution (Ha.obj (U₁.obj N))
  let w := U₂.map ψ ≫ ξ.hom.app N
  let d : A₂.cocomplex ⟶ Bq.cocomplex := InjectiveResolution.desc w Bq A₂
  have hd : aug A₂ ≫ d.f 0 = w ≫ aug Bq := InjectiveResolution.desc_commutes_zero w Bq A₂
  let φ := RightDerivedEdge.resolutionComparison Ha (U₁.obj N)
  have h₂ : aug Bq ≫ φ.f 0 = Ha.map (aug A₁) :=
    RightDerivedEdge.ι_f_zero_comp_resolutionComparison Ha (U₁.obj N)
  rw [RightDerivedEdge.edge_app_eq Ha Q n A₁ Bq φ h₂]
  have hinj : ∀ k, Injective (((Ha.mapHomologicalComplex _).obj A₁.cocomplex).X k) := fun k ↦
    RightDerivedEdge.injective_mapHomologicalComplex_obj Ha _ A₁.injective k
  let γL : (U₂.mapHomologicalComplex _).obj J₂.cocomplex ⟶
      (Ha.mapHomologicalComplex _).obj A₁.cocomplex :=
    (U₂.mapHomologicalComplex _).map (comparison H ψ) ≫
      (NatTrans.mapHomologicalComplex ξ.hom _).app J₁.cocomplex ≫
        (Ha.mapHomologicalComplex _).map (forgetComparison U₁ N)
  let γR : (U₂.mapHomologicalComplex _).obj J₂.cocomplex ⟶
      (Ha.mapHomologicalComplex _).obj A₁.cocomplex :=
    forgetComparison U₂ M ≫ d ≫ φ
  have key : U₂.map (aug J₂) ≫ γL.f 0 = U₂.map (aug J₂) ≫ γR.f 0 := by
    change U₂.map (aug J₂) ≫ U₂.map ((comparison H ψ).f 0) ≫ ξ.hom.app (J₁.cocomplex.X 0) ≫
        Ha.map ((forgetComparison U₁ N).f 0) =
      U₂.map (aug J₂) ≫ (forgetComparison U₂ M).f 0 ≫ d.f 0 ≫ φ.f 0
    rw [← U₂.map_comp_assoc, aug_comp_comparison_f_zero, U₂.map_comp, assoc,
      ← Functor.comp_map, ξ.hom.naturality_assoc, Functor.comp_map, ← Ha.map_comp,
      map_aug_comp_forgetComparison_f_zero, map_aug_comp_forgetComparison_f_zero_assoc]
    rw [reassoc_of% hd, h₂]
    simp only [w, assoc]
    rfl
  have hγ : (forgetAug U₂ M).f 0 ≫ γL.f 0 = (forgetAug U₂ M).f 0 ≫ γR.f 0 := by
    rwa [forgetAug_f_zero]
  have hhom := Stacks.ResolutionDesc.homologyMap_map_eq_of_injective (forgetAug U₂ M) Q γL γR hγ n
  have hcx : complexMap (U₂ ⋙ Q) (U₁ ⋙ Ha ⋙ Q) H (𝟭 ℬ) e (comparison H ψ) ≫
      ((Ha ⋙ Q).mapHomologicalComplex _).map (forgetComparison U₁ N) =
      (Q.mapHomologicalComplex _).map γL := by
    ext k
    simp only [γL, comp_f, complexMap_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f, he, Functor.comp_map, Q.map_comp, assoc]
    rfl
  unfold map mapOf forgetMap
  simp only [assoc, homologyToMapHomology_id, Functor.id_map, id_comp]
  rw [Iso.inv_hom_id_assoc, rdIso_inv_naturality_assoc w A₂ Bq d hd Q n]
  simp only [rdIso]
  rw [← homologyMap_comp_assoc, hcx, hhom]
  simp only [γR, CategoryTheory.Functor.map_comp, homologyMap_comp, assoc]
  exact congrArg (fun t ↦ ((injectiveResolution M).isoRightDerivedObj (U₂ ⋙ Q) n).hom ≫
    homologyMap ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map (forgetComparison U₂ M)) n ≫
      homologyMap ((Q.mapHomologicalComplex (ComplexShape.up ℕ)).map d) n ≫ t)
    (Iso.inv_hom_id_assoc (Bq.isoRightDerivedObj Q n) _).symm

end Compat

end Stacks.Cohomology.RelativePullback

end
