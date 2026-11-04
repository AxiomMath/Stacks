module

public import StacksFrontier.AlgebraicGeometry.Descent.DescentLocusComparisonAffine
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.FibreTransport
public import StacksFrontier.Homology.ModuleCatHomologyMapElementwise

/-!
# The Čech models of Tag 0BF1 over an affine base

Let `f : X ⟶ Spec A` and `f' : X' ⟶ Spec A` be proper and of finite presentation, `a : X' ⟶ X`
a morphism over `Spec A`, and `L` an `𝒪_X`-module of finite presentation flat over `A`. This
file sets up the complexes that the argument of [Stacks, Tag 0BF1] runs on: the `ℤ`-indexed
`A`-linear Čech models of `RΓ(X, L)` and `RΓ(X', a^* L)`, the chain map between them induced by
pulling cochains back along `a`, and the identification of degree-zero cohomology with global
sections.

## Main definitions

* `AlgebraicGeometry.DescentLocusComparison.homologyZeroBaseEquivSections`: `H⁰` of the Čech
  model is `Γ(X, F)`.
* `AlgebraicGeometry.DescentLocusComparison.cechModelPullbackMap`: the chain map of Čech models
  induced by `a`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.DescentLocusComparison

open Stacks.AlgebraicGeometry.ProperFlatGlobalSections

attribute [local instance 10000] HasDerivedCategory.standard

section HomologyZero

/-- **Degree-zero cohomology of a complex with no term in degree `-1` is the kernel of the
differential.** -/
def homologyZeroEquivKer {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsZero (K.X (-1))) : K.homology 0 ≃ₗ[R] LinearMap.ker (K.d 0 1).hom :=
  ((K.isoHomologyπ (-1) 0 (by simp) (hK.eq_of_src _ _)).symm ≪≫
    (K.sc 0).moduleCatCyclesIso).toLinearEquiv.trans
    (LinearEquiv.ofEq _ _ (by
      change LinearMap.ker (K.d 0 ((ComplexShape.up ℤ).next 0)).hom = _
      rw [CochainComplex.next, zero_add]))

variable {B : Type u} [CommRing B] {X : Scheme.{u}} (f : X ⟶ Spec (.of B))
  {I : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i) (F : X.Modules)

/-- The degree-zero cocycles of the Čech model are those of the alternating Čech complex. -/
def kerBaseEquivKerAlternating :
    LinearMap.ker ((baseAlternatingCechComplex f U hU F).d 0 1).hom ≃ₗ[B]
      LinearMap.ker ((Stacks.Cech.alternatingCechModuleComplex f U F).d 0 1).hom where
  toFun x := ⟨(baseAlternatingCechComplexXIso f U hU F 0).hom x.1, by
    have hx : (baseAlternatingCechComplex f U hU F).d ((0 : ℕ) : ℤ) ((0 + 1 : ℕ) : ℤ) x.1 = 0 :=
      x.2
    have h := congr($(d_comp_baseAlternatingCechComplexXIso_hom f U hU F 0) x.1)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hx, map_zero] at h
    exact h.symm⟩
  invFun y := ⟨(baseAlternatingCechComplexXIso f U hU F 0).inv y.1, by
    have hy : (Stacks.Cech.alternatingCechModuleComplex f U F).d 0 (0 + 1) y.1 = 0 := y.2
    have h := congr($(baseAlternatingCechComplexXIso_inv_comp_d f U hU F 0) y.1)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hy, map_zero] at h
    exact h⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' b x := Subtype.ext (map_smul (baseAlternatingCechComplexXIso f U hU F 0).hom.hom b _)
  left_inv x := Subtype.ext (Iso.hom_inv_id_apply _ _)
  right_inv y := Subtype.ext (Iso.inv_hom_id_apply _ _)

/-- **Degree-zero cohomology of the Čech model is the module of global sections**, for a cover
of the whole scheme. -/
def homologyZeroBaseEquivSections :
    letI := Stacks.Cech.sectionsModule f F ⊤
    (baseAlternatingCechComplex f U hU F).homology 0 ≃ₗ[B] Γ(F, ⊤) :=
  letI := Stacks.Cech.sectionsModule f F ⊤
  letI := Stacks.Cech.cochainModule f U F 0
  letI := Stacks.Cech.cochainModule f U F 1
  (homologyZeroEquivKer _
      (isZero_baseAlternatingCechComplex_X_of_neg f U hU F (-1) (by norm_num))).trans
    ((kerBaseEquivKerAlternating f U hU F).trans
      ((LinearEquiv.ofEq _ _ (by
        rw [Stacks.Cech.alternatingCechModuleComplex_d]
        exact (Stacks.Cech.range_sectionsToAlternatingₗ f U F (fun _ => le_top) hU.le).symm)).trans
      (LinearEquiv.ofInjective _
        (Stacks.Cech.sectionsToAlternatingₗ_injective f U F (fun _ => le_top) hU.le)).symm))

/-- The Čech model has no cohomology in degree `-1`. -/
theorem isZero_homology_baseAlternatingCechComplex_neg_one :
    IsZero ((baseAlternatingCechComplex f U hU F).homology (-1)) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    (isZero_baseAlternatingCechComplex_X_of_neg f U hU F (-1) (by norm_num))

/-- **Global sections of a trivial module over a base with `Γ(X, 𝒪_X) = B` are `B`.** -/
def sectionsEquivOfIsoUnit {F : X.Modules} (e : F ≅ SheafOfModules.unit X.ringCatSheaf)
    (hΓ : Function.Bijective (Stacks.Cech.baseRingHom f ⊤).hom) :
    letI := Stacks.Cech.sectionsModule f F ⊤
    Γ(F, ⊤) ≃ₗ[B] B :=
  letI := Stacks.Cech.sectionsModule f F ⊤
  letI := Stacks.Cech.sectionsModule f (SheafOfModules.unit X.ringCatSheaf) ⊤
  let e₁ : Γ(F, ⊤) ≃ₗ[B] Γ(SheafOfModules.unit X.ringCatSheaf, ⊤) :=
    { toFun := e.hom.app ⊤
      invFun := e.inv.app ⊤
      map_add' := map_add _
      map_smul' := fun b x =>
        Scheme.Modules.Hom.app_smul e.hom ((Stacks.Cech.baseRingHom f ⊤).hom b) x
      left_inv := Stacks.Cech.iso_inv_app_hom_app e ⊤
      right_inv := Stacks.Cech.iso_inv_app_hom_app e.symm ⊤ }
  let m : B →ₗ[B] Γ(SheafOfModules.unit X.ringCatSheaf, ⊤) :=
    { toFun := fun b => (Stacks.Cech.baseRingHom f ⊤).hom b
      map_add' := map_add _
      map_smul' := fun b c => map_mul (Stacks.Cech.baseRingHom f ⊤).hom b c }
  e₁.trans (LinearEquiv.ofBijective m hΓ).symm

end HomologyZero

section PullbackMap

/-- **The degreewise component of a morphism transported to extensions by zero.** For
identifications `a` and `b` of two complexes with extensions by zero and a morphism `ψ` of the
unextended complexes, the component of `a ≫ ψ.extend ≫ b⁻¹` in a degree in the image of the
embedding is `ψ`'s, read through the components of `a` and `b`. -/
lemma extendMap_conj_f_comp {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] (e : c.Embedding c')
    {K L : HomologicalComplex C c} {B B' : HomologicalComplex C c'} (a : B ≅ K.extend e)
    (ψ : K ⟶ L) (b : B' ≅ L.extend e) {i : ι} {i' : ι'} (h : e.f i = i')
    (x : B.X i' ⟶ K.X i) (hx : a.hom.f i' ≫ (K.extendXIso e h).hom = x)
    (y : B'.X i' ⟶ L.X i) (hy : b.hom.f i' ≫ (L.extendXIso e h).hom = y) :
    (a.hom ≫ HomologicalComplex.extendMap ψ e ≫ b.inv).f i' ≫ y = x ≫ ψ.f i := by
  subst hx hy
  simp only [HomologicalComplex.comp_f, Category.assoc, HomologicalComplex.extendMap_f ψ e h]
  rw [← HomologicalComplex.comp_f_assoc, b.inv_hom_id, HomologicalComplex.id_f,
    Category.id_comp, Iso.inv_hom_id, Category.comp_id]

variable {A : Type u} [CommRing A] {X X' : Scheme.{u}} (a : X' ⟶ X)
  (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of A)) (ha : a ≫ f = f')
  {I I' : Type u} (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (W : I' → X'.Opens) (hW : (⊤ : X'.Opens) = ⨆ k, W k) (π : I' → I)
  (hWU : ∀ k, W k ≤ a ⁻¹ᵁ U (π k)) (F : X.Modules)

/-- **The chain map of Čech models induced by `a`**: pull cochains back along `a`, refining the
inverse-image cover by `W` through `π`. -/
def cechModelPullbackMap :
    baseAlternatingCechComplex f U hU F ⟶
      baseAlternatingCechComplex f' W hW ((Scheme.Modules.pullback a).obj F) :=
  (baseAlternatingCechComplexIsoExtend f U hU F).hom ≫
    HomologicalComplex.extendMap
      (Stacks.Cech.alternatingCechModuleRefinementPullbackMap a U W π hWU F f f' ha)
      ComplexShape.embeddingUpNat ≫
    (baseAlternatingCechComplexIsoExtend f' W hW ((Scheme.Modules.pullback a).obj F)).inv

/-- **In a nonnegative degree the chain map of Čech models is the pullback of alternating
cochains.** -/
theorem cechModelPullbackMap_f_comp (m : ℕ) :
    (cechModelPullbackMap a f f' ha U hU W hW π hWU F).f m ≫
        (baseAlternatingCechComplexXIso f' W hW ((Scheme.Modules.pullback a).obj F) m).hom =
      (baseAlternatingCechComplexXIso f U hU F m).hom ≫
        (Stacks.Cech.alternatingCechModuleRefinementPullbackMap a U W π hWU F f f' ha).f m :=
  extendMap_conj_f_comp ComplexShape.embeddingUpNat (baseAlternatingCechComplexIsoExtend f U hU F)
    (Stacks.Cech.alternatingCechModuleRefinementPullbackMap a U W π hWU F f f' ha)
    (baseAlternatingCechComplexIsoExtend f' W hW ((Scheme.Modules.pullback a).obj F))
    (ComplexShape.embeddingUpNat_f m) _
    (baseAlternatingCechComplexIsoExtend_hom_f_comp_extendXIso f U hU F m) _
    (baseAlternatingCechComplexIsoExtend_hom_f_comp_extendXIso f' W hW _ m)

/-- The elementwise form of `cechModelPullbackMap_f_comp`. -/
theorem cechModelPullbackMap_f_apply (m : ℕ) (x : (baseAlternatingCechComplex f U hU F).X m) :
    (baseAlternatingCechComplexXIso f' W hW ((Scheme.Modules.pullback a).obj F) m).hom
        ((cechModelPullbackMap a f f' ha U hU W hW π hWU F).f m x) =
      Stacks.Cech.alternatingCochainRefinementPullbackₗ a U W π hWU F f f' ha m
        ((baseAlternatingCechComplexXIso f U hU F m).hom x) :=
  congr($(cechModelPullbackMap_f_comp a f f' ha U hU W hW π hWU F m) x)

end PullbackMap

section Fibre

variable {A K : Type u} [CommRing A] [CommRing K] (χ : A →+* K)
  {X X' X₀ X'₀ : Scheme.{u}} (a : X' ⟶ X)
  {f : X ⟶ Spec (.of A)} {f' : X' ⟶ Spec (.of A)} (ha : a ≫ f = f')
  [IsSeparated f] [IsSeparated f']
  {f₀ : X₀ ⟶ Spec (.of K)} {f'₀ : X'₀ ⟶ Spec (.of K)} {q : X₀ ⟶ X} {q' : X'₀ ⟶ X'}
  (hsq : IsPullback q f₀ f (Spec.map (CommRingCat.ofHom χ)))
  (hsq' : IsPullback q' f'₀ f' (Spec.map (CommRingCat.ofHom χ)))
  (a₀ : X'₀ ⟶ X₀) (ha₀ : a₀ ≫ f₀ = f'₀) (hcomm : a₀ ≫ q = q' ≫ a)
  {I I' : Type u} [Finite I] [Finite I'] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i))
  (W : I' → X'.Opens) (hW : (⊤ : X'.Opens) = ⨆ k, W k) (hWaff : ∀ k, IsAffineOpen (W k))
  (π : I' → I) (hWU : ∀ k, W k ≤ a ⁻¹ᵁ U (π k)) (F : X.Modules)

omit [IsSeparated f] [IsSeparated f'] [Finite I] [Finite I'] in
include hcomm in
/-- **Pulling alternating cochains back along `a` and base changing them commute**, up to the
identification `a₀^* q^* F ≅ q'^* a^* F` of `Stacks.Cech.pullbackSquareIso`. -/
theorem alternatingCochainBaseChange_pullback (m : ℕ)
    (s : Stacks.Cech.alternatingCechModuleObj f U F m) :
    Stacks.Cech.alternatingCechModuleObjMap f'₀ (fun k => q' ⁻¹ᵁ W k)
        (Stacks.Cech.pullbackSquareIso a q q' a₀ hcomm F).hom m
        (Stacks.Cech.alternatingCochainRefinementPullbackₗ a₀ (fun i => q ⁻¹ᵁ U i)
          (fun k => q' ⁻¹ᵁ W k) π
          (Stacks.Cech.preimage_le_preimage_of_comm a q q' a₀ hcomm U W π hWU)
          ((Scheme.Modules.pullback q).obj F) f₀ f'₀ ha₀ m
          (Stacks.Cech.alternatingCochainBaseChangeₗ q U (fun i => q ⁻¹ᵁ U i) (Equiv.refl I) F
            (preimage_eq_preimage_equivRefl q U) χ f f₀
            (fun V => Stacks.Cech.baseRingHom_comp_app χ f f₀ q hsq V) m s)) =
      Stacks.Cech.alternatingCochainBaseChangeₗ q' W (fun k => q' ⁻¹ᵁ W k) (Equiv.refl I')
          ((Scheme.Modules.pullback a).obj F) (preimage_eq_preimage_equivRefl q' W) χ f' f'₀
          (fun V => Stacks.Cech.baseRingHom_comp_app χ f' f'₀ q' hsq' V) m
        (Stacks.Cech.alternatingCochainRefinementPullbackₗ a U W π hWU F f f' ha m s) := by
  refine Subtype.ext (funext fun k => ?_)
  exact Stacks.Cech.pullbackSquareIso_pullbackSections a q q' a₀ hcomm F
    (V := CechCochains.inter U (π ∘ k)) (V₀ := CechCochains.inter (fun i => q ⁻¹ᵁ U i) (π ∘ k))
    (V' := CechCochains.inter W k) (T := CechCochains.inter (fun k => q' ⁻¹ᵁ W k) k)
    _ _ _ _ (s.1 (π ∘ k))

variable [F.IsQuasicoherent] [((Scheme.Modules.pullback a).obj F).IsQuasicoherent]

include hcomm in
/-- **The chain map of Čech models, read on the fibre**: through the base-change identifications
of `fibreTransport`, its extension of scalars is the pullback of alternating cochains along the
fibre `a₀ : X'₀ ⟶ X₀`, followed by `a₀^* q^* F ≅ q'^* a^* F`. -/
theorem fibreTransport_cechModelPullbackMap (m : ℕ)
    (x : (StacksDraft.Perfect.extendScalarsCx χ (baseAlternatingCechComplex f U hU F)).X (m : ℤ)) :
    (fibreTransport χ hsq' ((Scheme.Modules.pullback a).obj F) W hW hWaff m).hom
        (((ModuleCat.extendScalars.{u, u, u} χ).map
          ((cechModelPullbackMap a f f' ha U hU W hW π hWU F).f (m : ℤ))) x) =
      Stacks.Cech.alternatingCechModuleObjMap f'₀ (fun k => q' ⁻¹ᵁ W k)
          (Stacks.Cech.pullbackSquareIso a q q' a₀ hcomm F).hom m
        (Stacks.Cech.alternatingCochainRefinementPullbackₗ a₀ (fun i => q ⁻¹ᵁ U i)
          (fun k => q' ⁻¹ᵁ W k) π
          (Stacks.Cech.preimage_le_preimage_of_comm a q q' a₀ hcomm U W π hWU)
          ((Scheme.Modules.pullback q).obj F) f₀ f'₀ ha₀ m
          ((fibreTransport χ hsq F U hU hUaff m).hom x)) := by
  have key : (ModuleCat.extendScalars.{u, u, u} χ).map
        ((cechModelPullbackMap a f f' ha U hU W hW π hWU F).f (m : ℤ)) ≫
        (fibreTransport χ hsq' ((Scheme.Modules.pullback a).obj F) W hW hWaff m).hom =
      (fibreTransport χ hsq F U hU hUaff m).hom ≫
        (Stacks.Cech.alternatingCechModuleRefinementPullbackMap a₀ (fun i => q ⁻¹ᵁ U i)
            (fun k => q' ⁻¹ᵁ W k) π
            (Stacks.Cech.preimage_le_preimage_of_comm a q q' a₀ hcomm U W π hWU)
            ((Scheme.Modules.pullback q).obj F) f₀ f'₀ ha₀).f m ≫
        Stacks.Cech.alternatingCechModuleObjMap f'₀ (fun k => q' ⁻¹ᵁ W k)
          (Stacks.Cech.pullbackSquareIso a q q' a₀ hcomm F).hom m := by
    apply ModuleCat.hom_ext
    apply StacksDraft.Perfect.extendScalars_ext χ
    intro c
    have h1 := fibreTransport_one_tmul χ hsq' ((Scheme.Modules.pullback a).obj F) W hW hWaff m
      ((cechModelPullbackMap a f f' ha U hU W hW π hWU F).f (m : ℤ) c)
    have h2 := fibreTransport_one_tmul χ hsq F U hU hUaff m c
    have h3 := cechModelPullbackMap_f_apply a f f' ha U hU W hW π hWU F m c
    have h4 := alternatingCochainBaseChange_pullback χ a ha hsq hsq' a₀ ha₀ hcomm U W π hWU F m
      ((baseAlternatingCechComplexXIso f U hU F m).hom c)
    simp only [ConcreteCategory.comp_apply]
    rw [StacksDraft.Perfect.map_etm, StacksDraft.Perfect.etm_eq_tmul,
      StacksDraft.Perfect.etm_eq_tmul]
    refine h1.trans ?_
    rw [h3, ← h4]
    exact congrArg _ (congrArg _ h2.symm)
  exact congr($key x)

/-- Every Čech `0`-cochain is alternating. -/
theorem isAlternating_zero {Y : TopCat.{u}} {J : Type u} (V : J → Opens Y)
    (G : TopCat.Presheaf AddCommGrpCat.{u} Y) (s : CechCochains.Cochain V G 0) :
    CechCochains.IsAlternating V G s :=
  ⟨fun i hi => absurd (fun a b _ => Fin.ext (by have := a.2; have := b.2; omega)) hi,
    fun _ a b hab => absurd (Fin.ext (by have := a.2; have := b.2; omega)) hab⟩

include hsq hsq' hUaff hWaff ha₀ hcomm in
/-- **Injectivity on `H¹` of the fibre of the chain map of Čech models.** If the map
`H¹(X₀, q^* F) → H¹(X₀, a₀_* a₀^* q^* F)` induced by the unit is injective (for instance if the
pullback map `H¹(X₀, q^* F) → H¹(X'₀, a₀^* q^* F)` of [Stacks, Tag 01FA] is), then the extension
of scalars of the chain map of Čech models to the fibre is injective on `H¹`. -/
theorem mono_homologyMap_one_cechModelPullbackMap
    (hinj : Function.Injective ((((sheafSections (Opens.grothendieckTopology X₀)
      AddCommGrpCat.{u}).obj (op ⊤)).rightDerived 1).map
        (Stacks.Cech.unitAb a₀ ((Scheme.Modules.pullback q).obj F)))) :
    Mono (HomologicalComplex.homologyMap
      (((ModuleCat.extendScalars.{u, u, u} χ).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (cechModelPullbackMap a f f' ha U hU W hW π hWU F)) 1) := by
  set F₀ := (Scheme.Modules.pullback q).obj F
  set e := Stacks.Cech.pullbackSquareIso a q q' a₀ hcomm F
  set U₀ : I → X₀.Opens := fun i => q ⁻¹ᵁ U i
  set W₀ : I' → X'₀.Opens := fun k => q' ⁻¹ᵁ W k
  have hW₀U₀ := Stacks.Cech.preimage_le_preimage_of_comm a q q' a₀ hcomm U W π hWU
  rw [HomologicalComplex.mono_homologyMap_iff_elementwise _ 0 1 2 (by simp) (by simp)]
  intro x hx y hy
  set T := fibreTransport χ hsq F U hU hUaff
  set T' := fibreTransport χ hsq' ((Scheme.Modules.pullback a).obj F) W hW hWaff
  -- the cocycle `Z` on the fibre
  set Z := (T 1).hom x
  have hZ : CechCochains.cechD U₀ F₀.presheaf 1 Z.1 = 0 := by
    have h := fibreTransport_d_apply χ hsq F U hU hUaff 1 x
    have hx' : (StacksDraft.Perfect.extendScalarsCx χ (baseAlternatingCechComplex f U hU F)).d
        ((1 : ℕ) : ℤ) ((1 + 1 : ℕ) : ℤ) x = 0 := hx
    rw [hx', map_zero] at h
    exact congrArg Subtype.val h.symm
  -- its pullback is the coboundary of `Y`, transported along `e`
  set Y := (T' 0).hom y
  have hY : Stacks.Cech.alternatingCechModuleObjMap f'₀ W₀ e.hom 1
      (Stacks.Cech.alternatingCochainRefinementPullbackₗ a₀ U₀ W₀ π hW₀U₀ F₀ f₀ f'₀ ha₀ 1 Z) =
      (Stacks.Cech.alternatingCechModuleComplex f'₀ W₀
        ((Scheme.Modules.pullback q').obj ((Scheme.Modules.pullback a).obj F))).d 0 (0 + 1) Y := by
    rw [← fibreTransport_cechModelPullbackMap χ a ha hsq hsq' a₀ ha₀ hcomm U hU hUaff W hW
      hWaff π hWU F 1 x]
    have h := fibreTransport_d_apply χ hsq' ((Scheme.Modules.pullback a).obj F) W hW hWaff 0 y
    refine Eq.trans ?_ h
    exact congrArg (T' 1).hom hy
  set t := (Stacks.Cech.alternatingCechModuleObjMap f'₀ W₀ e.inv 0 Y).1
  have ht : CechCochains.cechD W₀ ((Scheme.Modules.pullback a₀).obj F₀).presheaf 0 t =
      Stacks.Cech.cochainPullback a₀ U₀ W₀ π hW₀U₀ F₀ 1 Z.1 := by
    have hc := congr($((Stacks.Cech.alternatingCechModuleComplexMap f'₀ W₀ e.inv).comm 0 1) Y)
    simp only at hc
    have h1 : CechCochains.cechD W₀ ((Scheme.Modules.pullback a₀).obj F₀).presheaf 0 t =
        ((Stacks.Cech.alternatingCechModuleComplexMap f'₀ W₀ e.inv).f 1
          ((Stacks.Cech.alternatingCechModuleComplex f'₀ W₀
            ((Scheme.Modules.pullback q').obj
              ((Scheme.Modules.pullback a).obj F))).d 0 1 Y)).1 :=
      congrArg Subtype.val hc
    rw [h1, ← hY]
    funext k
    exact Stacks.Cech.iso_inv_app_hom_app e _ _
  obtain ⟨t', ht'⟩ := Stacks.Cech.exists_cechD_eq_of_cechD_eq_cochainPullback a₀ U₀ W₀ π hW₀U₀
    F₀ (top_eq_iSup_preimage q U hU) (top_eq_iSup_preimage q' W hW) hinj Z.1 hZ t ht
  refine ⟨(T 0).inv ⟨t', isAlternating_zero U₀ F₀.presheaf t'⟩, ?_⟩
  apply (ModuleCat.mono_iff_injective (T 1).hom).1 inferInstance
  refine (fibreTransport_d_apply χ hsq F U hU hUaff 0 _).trans ?_
  exact (congrArg _ (Iso.inv_hom_id_apply (T 0) _)).trans (Subtype.ext ht')

end Fibre

end AlgebraicGeometry.DescentLocusComparison

end
