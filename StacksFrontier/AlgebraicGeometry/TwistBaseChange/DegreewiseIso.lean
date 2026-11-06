module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ChartBaseChange
public import StacksFrontier.AlgebraicGeometry.ModuleChartLocality.BaseChange
public import StacksFrontier.AlgebraicGeometry.ModuleChartLocality.Chart
public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.RestrictIso

/-!
# The comparison maps on the twists of a degreewise base change are isomorphisms

Let `φ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings which is a base change
**degreewise** along `𝒜₀ ⟶ ℬ₀`: every homogeneous piece `ℬₙ` is `ℬ₀ ⊗_{𝒜₀} 𝒜ₙ` through `φ`. This
is the situation of the restriction of a quasi-coherent graded algebra along a morphism of affine
schemes, `ℬ = ℬ₀ ⊗_{𝒜₀} 𝒜`. This file proves that

* the irrelevant ideal of `ℬ` lies in the image of that of `𝒜`, so `AlgebraicGeometry.Proj.map φ`
  is defined;
* the domain of definition `U(φ)` of Tag 01MY is all of `Proj ℬ`;
* Tag 01MY's comparison map `θ n : mapHom* 𝒪_{Proj 𝒜}(n) ⟶ ι* 𝒪_{Proj ℬ}(n)` is an
  **isomorphism** for every `n : ℤ`.

## Main results

* `Stacks.AlgebraicGeometry.TwistBaseChange.irrelevant_le_map_of_isBaseChange`,
  `Stacks.AlgebraicGeometry.TwistBaseChange.mapDomain_eq_top_of_isBaseChange`.
* `Stacks.AlgebraicGeometry.TwistBaseChange.isIso_twistMap_of_isBaseChange`: **`θ n` is an
  isomorphism.**
* `Stacks.AlgebraicGeometry.TwistBaseChange.twistPushforwardMap_comp_eq`: for any graded map with
  `ℬ₊ ≤ 𝒜₊.map φ` and `U(φ) = Proj ℬ`, the adjoint `twistPushforwardMap` of Tag 01MY, carried to a
  morphism into `(Proj.map φ)_* (U(φ).ι)_* (U(φ).ι)⁻¹ 𝒪(n)`, is the module comparison
  `Stacks.ProjModuleComparison.pushforwardModuleMap` of the twist followed by the unit of the
  restriction to `U(φ)`.
* `Stacks.AlgebraicGeometry.TwistBaseChange.isIso_twistMap_of_isIso_moduleMap`: hence `θ n` is
  an isomorphism as soon as the module comparison `(Proj.map φ)^* 𝒪(n) ⟶ 𝒪(n)` is.
* `Stacks.AlgebraicGeometry.TwistBaseChange.isIso_homEquiv_symm_of_comp`: invertibility of an
  inverse adjoint transpose transfers across a factorization `R ≅ Ri ⋙ Rp` of the right adjoint.
* `Stacks.AlgebraicGeometry.TwistBaseChange.isBaseChange_of_ringEquiv` and
  `isBaseChange_pieceMap_comp_of_isIso`: a degreewise base change stays one after composing with
  graded ring isomorphisms on both sides.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization TensorProduct
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare Stacks.AlgebraicGeometry.ModuleChartLocality

namespace Stacks.AlgebraicGeometry.TwistBaseChange

universe u

/-! ### Abstract transfer -/

/-- **Invertibility of an inverse adjoint transpose, transferred across a factorization of the
right adjoint.** Let `F ⊣ R`, `P ⊣ Rp` and `I ⊣ Ri` be adjunctions with `R ≅ Ri ⋙ Rp`. If
`g : X ⟶ R (I Y)`, read through that isomorphism, is `gP` followed by `Rp` of the unit of `I ⊣ Ri`
at `Y`, and the transpose of `gP` along `P ⊣ Rp` is invertible, then so is the transpose of `g`
along `F ⊣ R`. -/
public theorem isIso_homEquiv_symm_of_comp {C D D' : Type*} [Category C] [Category D]
    [Category D'] {F : C ⥤ D} {R : D ⥤ C} (adjM : F ⊣ R)
    {P : C ⥤ D'} {Rp : D' ⥤ C} (adjP : P ⊣ Rp)
    {I : D' ⥤ D} {Ri : D ⥤ D'} (adjI : I ⊣ Ri)
    (α : R ≅ Ri ⋙ Rp) {X : C} {Y : D'} (g : X ⟶ R.obj (I.obj Y)) (gP : X ⟶ Rp.obj Y)
    (h : g ≫ α.hom.app _ = gP ≫ Rp.map (adjI.unit.app Y))
    (hP : IsIso ((adjP.homEquiv _ _).symm gP)) :
    IsIso ((adjM.homEquiv _ _).symm g) := by
  let adjM' := adjM.ofNatIsoRight α
  let adjC := adjP.comp adjI
  have e1 : (adjM'.homEquiv _ _).symm (g ≫ α.hom.app _) = (adjM.homEquiv _ _).symm g := by
    rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]
  have e2 := leftAdjointUniq_hom_app_homEquiv_symm adjM' adjC (g ≫ α.hom.app _)
  have e3 : (adjC.homEquiv _ _).symm (g ≫ α.hom.app _) =
      I.map ((adjP.homEquiv _ _).symm gP) := by
    rw [h, Adjunction.comp_homEquiv]
    show (adjI.homEquiv _ _).symm ((adjP.homEquiv _ _).symm (gP ≫ Rp.map (adjI.unit.app Y))) = _
    rw [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_left_symm]
    have hid : (adjI.homEquiv Y (I.obj Y)).symm (adjI.unit.app Y) = 𝟙 (I.obj Y) :=
      (Equiv.symm_apply_eq _).mpr (Adjunction.homEquiv_id _ _).symm
    rw [hid, Category.comp_id]
  rw [← e1, ← e2, e3]
  infer_instance

/-! ### Tag 01MY's comparison against the module comparison -/

section Bridge

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (ψ : 𝒜 →+*ᵍ ℬ) (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
  (hdom : mapDomain 𝒜 ℬ ψ = ⊤)

include hdom in
/-- On a domain of definition that is everything, Tag 01MY's base point is the image under
`AlgebraicGeometry.Proj.map`. -/
public theorem basePoint_eq_comapFun (y : (mapDomain 𝒜 ℬ ψ).toScheme) :
    basePoint 𝒜 ℬ ψ y = ProjectiveSpectrum.comapFun ψ hψ y.1 := by
  show (mapHom 𝒜 ℬ ψ).base y = _
  rw [mapHom_eq_ι_comp 𝒜 ℬ ψ hψ hdom, Scheme.Hom.comp_apply]
  rfl

/-- The fibre comparison of Tag 01MY at a point equal to `comapFun z` is the fibre comparison of
`Stacks.ProjModuleComparison` for the ring itself, evaluated on a family of fibres. -/
public theorem fibreMap_eq_moduleFibreMap {U : TopologicalSpace.Opens (ProjectiveSpectrum.top 𝒜)}
    (a : ∀ x : U, ModuleFiber (M := A) 𝒜 x.1)
    (x : ProjectiveSpectrum 𝒜) (z : ProjectiveSpectrum ℬ)
    (hx : x = ProjectiveSpectrum.comapFun ψ hψ z)
    (h : x.asHomogeneousIdeal = z.asHomogeneousIdeal.comap ψ) (h₁ : x ∈ U)
    (h₂ : ProjectiveSpectrum.comapFun ψ hψ z ∈ U) :
    fibreMap 𝒜 ℬ ψ x z h (a ⟨x, h₁⟩) =
      Stacks.ProjModuleComparison.fibreMap ψ hψ ψ.toRingHom.toSemilinearMap z (a ⟨_, h₂⟩) := by
  subst hx
  induction a ⟨_, h₁⟩ using LocalizedModule.induction_on with
  | h m s =>
    rw [Stacks.ProjModuleComparison.fibreMap_mk]
    exact fibreMap_mk 𝒜 ℬ ψ _ z h m s.1 s.2 _

/-- **Tag 01MY's adjoint comparison is the module comparison of the twist.** Carried along
`mapHom = U(φ).ι ≫ Proj.map φ` into the composite of direct images, `twistPushforwardMap` is
`Stacks.ProjModuleComparison.pushforwardModuleMap` for the twisted gradings, followed by the unit
of the restriction to `U(φ)`. -/
public theorem twistPushforwardMap_comp_eq (n : ℤ) :
    twistPushforwardMap 𝒜 ℬ ψ n ≫
      (Scheme.Modules.pushforwardCongr (mapHom_eq_ι_comp 𝒜 ℬ ψ hψ hdom)).hom.app _ ≫
      (Scheme.Modules.pushforwardComp (mapDomain 𝒜 ℬ ψ).ι
        (AlgebraicGeometry.Proj.map ψ hψ)).inv.app _ =
    Stacks.ProjModuleComparison.pushforwardModuleMap ψ hψ ψ.toRingHom.toSemilinearMap
        (fun i _ hm => map_mem_twistGrading 𝒜 ℬ ψ n i hm) ≫
      (Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map ψ hψ)).map
        ((Scheme.Modules.restrictAdjunction (mapDomain 𝒜 ℬ ψ).ι).unit.app
          (twistingSheaf ℬ n)) := by
  ext U x
  refine Subtype.ext (funext fun z => ?_)
  have hz : (z.1 : AlgebraicGeometry.Proj ℬ) ∈ mapDomain 𝒜 ℬ ψ := by
    have : ∀ w : AlgebraicGeometry.Proj ℬ, w ∈ mapDomain 𝒜 ℬ ψ := fun w => by
      rw [hdom]; trivial
    exact this _
  exact fibreMap_eq_moduleFibreMap 𝒜 ℬ ψ hψ x.1 (basePoint 𝒜 ℬ ψ ⟨z.1, hz⟩) z.1
    (basePoint_eq_comapFun 𝒜 ℬ ψ hψ hdom ⟨z.1, hz⟩) _ _ _

include hdom in
/-- **Tag 01MY's comparison map on the `n`-th twist is an isomorphism as soon as the module
comparison `(Proj.map φ)^* 𝒪(n) ⟶ 𝒪(n)` is**, for a graded map defined everywhere with
`ℬ₊ ≤ 𝒜₊.map φ`. -/
public theorem isIso_twistMap_of_isIso_moduleMap (n : ℤ)
    (hθ : IsIso (Stacks.ProjModuleComparison.moduleMap ψ hψ ψ.toRingHom.toSemilinearMap
        (fun i _ hm => map_mem_twistGrading 𝒜 ℬ ψ n i hm))) :
    IsIso (twistMap 𝒜 ℬ ψ n) := by
  have := isIso_mapDomain_ι 𝒜 ℬ ψ hdom
  have hT : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).homEquiv _ _
      |>.symm (twistPushforwardMap 𝒜 ℬ ψ n)) :=
    isIso_homEquiv_symm_of_comp
      (Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ))
      (Scheme.Modules.pullbackPushforwardAdjunction (AlgebraicGeometry.Proj.map ψ hψ))
      (Scheme.Modules.restrictAdjunction (mapDomain 𝒜 ℬ ψ).ι)
      (Scheme.Modules.pushforwardCongr (mapHom_eq_ι_comp 𝒜 ℬ ψ hψ hdom) ≪≫
        (Scheme.Modules.pushforwardComp _ _).symm)
      (twistPushforwardMap 𝒜 ℬ ψ n) _ (twistPushforwardMap_comp_eq 𝒜 ℬ ψ hψ hdom n) hθ
  have h3 : IsIso ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
      (twistingSheaf ℬ n)) :=
    inferInstanceAs (IsIso ((Scheme.Modules.restrictFunctorIsoPullback
      (mapDomain 𝒜 ℬ ψ).ι).app _).hom)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hT h3

end Bridge

/-! ### The twisted pieces of a degreewise base change -/

section Pieces

attribute [local instance] instVAddNatIntModuleChart

/-- In a nonnegative twisted degree, a twisted homogeneous piece is a homogeneous piece of the
ring. -/
public theorem mem_twistGrading_iff_of_nonneg {R : Type u} [CommRing R] (ℛ : ℕ → AddSubgroup R)
    [GradedRing ℛ] {n i : ℤ} (hk : 0 ≤ i + n) (x : R) :
    x ∈ twistGrading (S := R) ℛ n i ↔ x ∈ ℛ (i + n).toNat := by
  simp [integerGrading, hk, mem_homogeneousSubmodule]

/-- In a negative twisted degree, the twisted homogeneous piece is zero. -/
public theorem subsingleton_twistGrading_of_neg {R : Type u} [CommRing R]
    (ℛ : ℕ → AddSubgroup R) [GradedRing ℛ] {n i : ℤ} (hk : i + n < 0) :
    Subsingleton ↥(twistGrading (S := R) ℛ n i) := by
  refine ⟨fun x y => Subtype.ext ?_⟩
  have hx := x.2
  have hy := y.2
  simp only [twistGrading_apply, integerGrading_neg _ _ hk, Submodule.mem_bot] at hx hy
  rw [hx, hy]

variable {A B : Type u} [CommRing A] [CommRing B]
  {𝒜 : ℕ → AddSubgroup A} {ℬ : ℕ → AddSubgroup B} [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) [Algebra ↥(𝒜 0) ↥(ℬ 0)]
  (halg : ∀ r : ↥(𝒜 0), (algebraMap ↥(𝒜 0) ↥(ℬ 0) r : B) = φ (r : A))
  (hfA : ∀ n : ℕ, IsBaseChange ↥(ℬ 0) (Stacks.Proj.pieceMap φ halg n))

include hfA in
/-- **A degreewise base change of the ring is one of every twist**: the degree-`i` component of
`φ : A(n) → B(n)` is a base change along `𝒜₀ ⟶ ℬ₀`. -/
public theorem isBaseChange_modulePieceMap_twistGrading (n i : ℤ) :
    IsBaseChange ↥(ℬ 0) (modulePieceMap φ φ.toRingHom.toSemilinearMap
      (fun i _ hm => map_mem_twistGrading 𝒜 ℬ φ n i hm) halg i) := by
  by_cases hk : 0 ≤ i + n
  · have hA := mem_twistGrading_iff_of_nonneg 𝒜 hk
    have hB := mem_twistGrading_iff_of_nonneg ℬ hk
    let eM : ↥(gradePieceSubmodule 𝒜 (i + n).toNat) ≃ₗ[↥(𝒜 0)]
        ↥(twistGrading (S := A) 𝒜 n i) :=
      { toFun := fun x => ⟨x.1, (hA _).2 x.2⟩
        invFun := fun x => ⟨x.1, (hA _).1 x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun r x => Subtype.ext (Algebra.smul_def r (x : A))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let eN : ↥(gradePieceSubmodule ℬ (i + n).toNat) ≃ₗ[↥(ℬ 0)]
        TargetPiece ℬ (twistGrading (S := B) ℬ n) i :=
      { toFun := fun x => TargetPiece.ofPiece ⟨x.1, (hB _).2 x.2⟩
        invFun := fun x => ⟨(TargetPiece.toPiece x).1, (hB _).1 (TargetPiece.toPiece x).2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun r x => Subtype.ext (Algebra.smul_def r (x : B))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    refine (IsBaseChange.iff_of_equiv_comm eM eN ?_).mp (hfA (i + n).toNat)
    ext x
    rfl
  · have hk' : i + n < 0 := lt_of_not_ge hk
    have := subsingleton_twistGrading_of_neg 𝒜 hk'
    have : Subsingleton (TargetPiece ℬ (twistGrading (S := B) ℬ n) i) :=
      subsingleton_twistGrading_of_neg ℬ hk'
    exact IsBaseChange.of_equiv (LinearEquiv.ofSubsingleton _ _) fun _ => Subsingleton.elim _ _

include hfA in
/-- **The irrelevant ideal of `ℬ` lies in the image of that of `𝒜`** for a degreewise base change:
a homogeneous element of positive degree `d` of `ℬ` is a `ℬ₀`-combination of images of elements
of `𝒜 d`. -/
public theorem irrelevant_le_map_of_isBaseChange :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ := by
  refine irrelevant_le_map_of_mem_span 𝒜 ℬ φ fun d hd g hg => ?_
  refine (hfA d).inductionOn
    (motive := fun x => (x : B) ∈ Ideal.span (φ '' ⋃ n > 0, (𝒜 n : Set A)))
    (⟨g, hg⟩ : ↥(gradePieceSubmodule ℬ d)) ?_ ?_ ?_
  · intro m
    exact Ideal.subset_span ⟨m, Set.mem_iUnion₂.mpr ⟨d, hd, m.2⟩, rfl⟩
  · intro s x hx
    show (s : B) * (x : B) ∈ _
    exact Ideal.mul_mem_left _ _ hx
  · intro x y hx hy
    exact add_mem hx hy

include hfA in
/-- **The domain of definition of a degreewise base change is everything.** -/
public theorem mapDomain_eq_top_of_isBaseChange : mapDomain 𝒜 ℬ φ = ⊤ :=
  mapDomain_eq_top_of_irrelevant_le_map 𝒜 ℬ φ (irrelevant_le_map_of_isBaseChange φ halg hfA)

include hfA in
/-- **The module comparison `(Proj.map φ)^* 𝒪(n) ⟶ 𝒪(n)` of a degreewise base change is an
isomorphism.** -/
public theorem isIso_moduleMap_twistGrading_of_isBaseChange (n : ℤ) :
    IsIso (Stacks.ProjModuleComparison.moduleMap φ (irrelevant_le_map_of_isBaseChange φ halg hfA)
      φ.toRingHom.toSemilinearMap (fun i _ hm => map_mem_twistGrading 𝒜 ℬ φ n i hm)) :=
  isIso_moduleMap_of_isIso_extension φ _ _ _ fun _ _ _ hb =>
    isIso_moduleDegreeZeroExtension φ _ _ halg hb
      (isBaseChange_modulePieceMap_twistGrading φ halg hfA n) hfA

include hfA in
/-- **Tag 01MY's comparison map `θ n` on the `n`-th twist of a degreewise base change is an
isomorphism**, for every `n : ℤ`. -/
public theorem isIso_twistMap_of_isBaseChange (n : ℤ) :
    IsIso (Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap 𝒜 ℬ φ n) :=
  isIso_twistMap_of_isIso_moduleMap 𝒜 ℬ φ (irrelevant_le_map_of_isBaseChange φ halg hfA)
    (mapDomain_eq_top_of_isBaseChange φ halg hfA) n
    (isIso_moduleMap_twistGrading_of_isBaseChange φ halg hfA n)

end Pieces

/-! ### Transport along graded ring isomorphisms -/

/-- **A base change transports along ring isomorphisms of both coefficient rings.** If
`f : M → N` exhibits `N` as `S ⊗_R M`, and `f'` agrees with `f` under ring isomorphisms
`R ≃ R'`, `S ≃ S'` compatible with the algebra maps and additive isomorphisms `M ≃ M'`, `N ≃ N'`
semilinear over them, then `f'` exhibits `N'` as `S' ⊗_{R'} M'`. -/
public theorem isBaseChange_of_ringEquiv
    {R R' S S' M M' N N' : Type*} [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R' S']
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M']
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [AddCommGroup N'] [Module R' N'] [Module S' N'] [IsScalarTower R' S' N']
    (eR : R ≃+* R') (eS : S ≃+* S')
    (hRS : ∀ r : R, algebraMap R' S' (eR r) = eS (algebraMap R S r))
    (eM : M ≃+ M') (heM : ∀ (r : R) (m : M), eM (r • m) = eR r • eM m)
    (eN : N ≃+ N') (heN : ∀ (s : S) (n : N), eN (s • n) = eS s • eN n)
    {f : M →ₗ[R] N} {f' : M' →ₗ[R'] N'} (hff : ∀ m, f' (eM m) = eN (f m))
    (hf : IsBaseChange S f) : IsBaseChange S' f' := by
  have heN' : ∀ (s : S') (x : N'), eN.symm (s • x) = eS.symm s • eN.symm x := by
    intro s x
    apply eN.injective
    rw [AddEquiv.apply_symm_apply, heN, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  refine IsBaseChange.of_lift_unique _ fun Q _ _ _ _ g => ?_
  let : Module S Q := Module.compHom Q eS.toRingHom
  let : Module R Q := Module.compHom Q eR.toRingHom
  have : IsScalarTower R S Q := ⟨fun r s q => by
    show eS (r • s) • q = eR r • eS s • q
    rw [Algebra.smul_def, map_mul, ← hRS, mul_smul, algebraMap_smul]⟩
  let g₀ : M →ₗ[R] Q :=
    { toFun := fun m => g (eM m)
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun r m => by
        show g (eM (r • m)) = eR r • g (eM m)
        rw [heM, map_smul] }
  let G := hf.lift g₀
  let g' : N' →ₗ[S'] Q :=
    { toFun := fun x => G (eN.symm x)
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun s x => by
        show G (eN.symm (s • x)) = s • G (eN.symm x)
        rw [heN', G.map_smul]
        show eS (eS.symm s) • G (eN.symm x) = s • G (eN.symm x)
        rw [RingEquiv.apply_symm_apply] }
  refine ⟨g', LinearMap.ext fun m' => ?_, fun y hy => ?_⟩
  · obtain ⟨m, rfl⟩ := eM.surjective m'
    show G (eN.symm (f' (eM m))) = g (eM m)
    rw [hff, AddEquiv.symm_apply_apply]
    exact hf.lift_eq g₀ m
  · let Y : N →ₗ[S] Q :=
      { toFun := fun x => y (eN x)
        map_add' := fun a b => by rw [map_add, map_add]
        map_smul' := fun s x => by
          show y (eN (s • x)) = eS s • y (eN x)
          rw [heN, map_smul] }
    have hYG : Y = G := hf.algHom_ext Y G fun m => by
      show y (eN (f m)) = G (f m)
      rw [hf.lift_eq g₀ m, ← hff]
      exact LinearMap.congr_fun hy (eM m)
    refine LinearMap.ext fun x => ?_
    have := LinearMap.congr_fun hYG (eN.symm x)
    change y (eN (eN.symm x)) = G (eN.symm x) at this
    rwa [AddEquiv.apply_symm_apply] at this

section Transport

variable {A A' B B' : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
  {𝒜 : ℕ → AddSubgroup A} {𝒜' : ℕ → AddSubgroup A'} {ℬ : ℕ → AddSubgroup B}
  {ℬ' : ℕ → AddSubgroup B'} [GradedRing 𝒜] [GradedRing 𝒜'] [GradedRing ℬ] [GradedRing ℬ']

/-- The degree-zero part of a graded ring isomorphism, as a ring isomorphism. -/
public def gradeZeroRingEquivOfInverse (α : 𝒜 →+*ᵍ 𝒜') (α' : 𝒜' →+*ᵍ 𝒜)
    (h₁ : α'.comp α = GradedRingHom.id 𝒜) (h₂ : α.comp α' = GradedRingHom.id 𝒜') :
    ↥(𝒜 0) ≃+* ↥(𝒜' 0) :=
  RingEquiv.ofRingHom α.gradedZeroRingHom α'.gradedZeroRingHom
    (RingHom.ext fun x => Subtype.ext (congrArg (fun k : 𝒜' →+*ᵍ 𝒜' => k (x : A')) h₂))
    (RingHom.ext fun x => Subtype.ext (congrArg (fun k : 𝒜 →+*ᵍ 𝒜 => k (x : A)) h₁))

/-- A homogeneous piece of a graded ring isomorphism, as an additive isomorphism. -/
public def gradePieceAddEquivOfInverse (α : 𝒜 →+*ᵍ 𝒜') (α' : 𝒜' →+*ᵍ 𝒜)
    (h₁ : α'.comp α = GradedRingHom.id 𝒜) (h₂ : α.comp α' = GradedRingHom.id 𝒜') (n : ℕ) :
    ↥(gradePieceSubmodule 𝒜 n) ≃+ ↥(gradePieceSubmodule 𝒜' n) where
  toFun x := ⟨α x, α.map_mem x.2⟩
  invFun x := ⟨α' x, α'.map_mem x.2⟩
  left_inv x := Subtype.ext (congrArg (fun k : 𝒜 →+*ᵍ 𝒜 => k (x : A)) h₁)
  right_inv x := Subtype.ext (congrArg (fun k : 𝒜' →+*ᵍ 𝒜' => k (x : A')) h₂)
  map_add' x y := Subtype.ext (map_add α (x : A) y)

/-- **A degreewise base change stays one after composing with graded ring isomorphisms on both
sides.** -/
public theorem isBaseChange_pieceMap_comp_of_isIso
    (α : 𝒜 →+*ᵍ 𝒜') (α' : 𝒜' →+*ᵍ 𝒜) (hα₁ : α'.comp α = GradedRingHom.id 𝒜)
    (hα₂ : α.comp α' = GradedRingHom.id 𝒜')
    (γ : ℬ' →+*ᵍ ℬ) (γ' : ℬ →+*ᵍ ℬ') (hγ₁ : γ'.comp γ = GradedRingHom.id ℬ')
    (hγ₂ : γ.comp γ' = GradedRingHom.id ℬ)
    (β : 𝒜' →+*ᵍ ℬ') [Algebra ↥(𝒜' 0) ↥(ℬ' 0)]
    (halgβ : ∀ r : ↥(𝒜' 0), (algebraMap ↥(𝒜' 0) ↥(ℬ' 0) r : B') = β (r : A'))
    (hβ : ∀ n : ℕ, IsBaseChange ↥(ℬ' 0) (Stacks.Proj.pieceMap β halgβ n))
    [Algebra ↥(𝒜 0) ↥(ℬ 0)]
    (halg : ∀ r : ↥(𝒜 0), (algebraMap ↥(𝒜 0) ↥(ℬ 0) r : B) = (γ.comp (β.comp α)) (r : A))
    (n : ℕ) : IsBaseChange ↥(ℬ 0) (Stacks.Proj.pieceMap (γ.comp (β.comp α)) halg n) := by
  have hαα : ∀ x : A', α (α' x) = x := fun x =>
    congrArg (fun k : 𝒜' →+*ᵍ 𝒜' => k x) hα₂
  refine isBaseChange_of_ringEquiv (gradeZeroRingEquivOfInverse α' α hα₂ hα₁)
    (gradeZeroRingEquivOfInverse γ γ' hγ₁ hγ₂) (fun r => Subtype.ext ?_)
    (gradePieceAddEquivOfInverse α' α hα₂ hα₁ n) (fun r m => Subtype.ext ?_)
    (gradePieceAddEquivOfInverse γ γ' hγ₁ hγ₂ n) (fun s x => Subtype.ext ?_)
    (fun m => Subtype.ext ?_) (hβ n)
  · show (algebraMap ↥(𝒜 0) ↥(ℬ 0) (α'.gradedZeroRingHom r) : B) =
      γ (algebraMap ↥(𝒜' 0) ↥(ℬ' 0) r : B')
    rw [halg, halgβ]
    show γ (β (α (α' (r : A')))) = γ (β (r : A'))
    rw [hαα]
  · show α' ((r : A') * (m : A')) = (α' (r : A')) * α' (m : A')
    exact map_mul α' _ _
  · show γ ((s : B') * (x : B')) = γ (s : B') * γ (x : B')
    exact map_mul γ _ _
  · show γ (β (α (α' (m : A')))) = γ (β (m : A'))
    rw [hαα]

end Transport

end Stacks.AlgebraicGeometry.TwistBaseChange

end
