module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDenseAffineFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.SizeBoundFieldPoints
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackSizeBound

/-!
# Axiom [-1] for the Quot functor

Artin's criterion for algebraic spaces (Stacks 07Y1) asks a set-theoretic condition, axiom [-1]:
the values of the functor on the spectra of fields of finite type over `S` are bounded by the
size of one object of the site. For `Quot_{F/X/S}` in the situation of Remark 0CZW this holds
because a quotient of `F_k` is determined by its kernel, and the submodules of a module of finite
type on a quasi-compact algebraic space are boundedly many.

## Main results

* `AlgebraicGeometry.Space.eq_zero_of_app_eq_zero_of_isCoverDense`: a morphism of modules on the
  small étale site vanishing over a dense family of charts vanishes.
* `AlgebraicGeometry.Space.injective_subobject_range` and
  `AlgebraicGeometry.Space.mk_subobject_le`: a submodule is determined by its sections over a dense
  family of charts, so the submodules are boundedly many.
* `AlgebraicGeometry.Space.QuotSituation.mk_subobject_baseChangeModule_le`: the submodules of
  `F_T`, for an affine test scheme `T` and `F` of finite type, number at most `2 ^ 2 ^ size T`.
* `AlgebraicGeometry.Space.exists_sizeBound_quotOverBase`: axiom [-1] for `Quot_{F/X/S}`.

## References

* [Stacks Project, Tag 07Y1](https://stacks.math.columbia.edu/tag/07Y1)
* [Stacks Project, Tag 0CZW](https://stacks.math.columbia.edu/tag/0CZW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {Z : AlgebraicSpaces B S hS}

/-- A morphism of modules on the small étale site of an algebraic space vanishes as soon as it
vanishes on the sections over every member of a dense family of étale charts. -/
theorem eq_zero_of_app_eq_zero_of_isCoverDense {ι : Type u} (c : ι → SmallEtale B S hS Z.1)
    [(inducedFunctor c).IsCoverDense (SmallEtale.topology B S hS Z.1)]
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (φ : M ⟶ N)
    (h : ∀ (i : ι) (x : M.val.obj (op (c i))), φ.val.app (op (c i)) x = 0) : φ = 0 := by
  let P : (SmallEtale B S hS Z.1)ᵒᵖ ⥤ AddCommGrpCat.{u} := N.val.presheaf
  let Q : (SmallEtale B S hS Z.1)ᵒᵖ ⥤ AddCommGrpCat.{u} := M.val.presheaf
  let ψ : Q ⟶ P := (PresheafOfModules.toPresheaf _).map φ.val
  have hN : Presieve.IsSheaf (SmallEtale.topology B S hS Z.1) (P ⋙ forget AddCommGrpCat) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.HasSheafCompose.isSheaf _ N.isSheaf
  have main : ∀ (U : SmallEtale B S hS Z.1) (x : Q.obj (op U)), ψ.app (op U) x = 0 := by
    intro U x
    apply (hN _ ((inducedFunctor c).is_cover_of_isCoverDense _ U)).isSeparatedFor.ext
    rintro Y _ ⟨W, f₁, f₂, ⟨rfl⟩⟩
    have hnat : P.map f₂.op (ψ.app (op U) x) = ψ.app _ (Q.map f₂.op x) :=
      (ConcreteCategory.congr_hom (ψ.naturality f₂.op) x).symm
    have hcomp : P.map (f₂.op ≫ f₁.op) (ψ.app (op U) x) =
        P.map f₁.op (P.map f₂.op (ψ.app (op U) x)) :=
      ConcreteCategory.congr_hom (P.map_comp f₂.op f₁.op) _
    have hzero : ψ.app _ (Q.map f₂.op x) = 0 := h W _
    change P.map (f₂.op ≫ f₁.op) (ψ.app (op U) x) = P.map (f₂.op ≫ f₁.op) 0
    rw [map_zero, hcomp, hnat, hzero, map_zero]
  apply SheafOfModules.hom_ext
  ext U x
  exact main U.unop x

/-- A submodule of a module on the small étale site is contained in another as soon as, over every
member of a dense family of étale charts, the sections of the first lie among those of the
second. -/
theorem subobject_le_of_range_subset {ι : Type u} (c : ι → SmallEtale B S hS Z.1)
    [(inducedFunctor c).IsCoverDense (SmallEtale.topology B S hS Z.1)]
    {M : Modules.{u, u} B S hS Z.1 Z.2} (K K' : Subobject M)
    (h : ∀ i, Set.range (K.arrow.val.app (op (c i))) ⊆ Set.range (K'.arrow.val.app (op (c i)))) :
    K ≤ K' := by
  have hz : K.arrow ≫ cokernel.π K'.arrow = 0 := by
    refine eq_zero_of_app_eq_zero_of_isCoverDense c _ fun i x => ?_
    obtain ⟨y, hy⟩ := h i ⟨x, rfl⟩
    change (cokernel.π K'.arrow).val.app (op (c i)) (K.arrow.val.app (op (c i)) x) = 0
    rw [← hy]
    change (K'.arrow ≫ cokernel.π K'.arrow).val.app (op (c i)) y = 0
    rw [cokernel.condition]
    rfl
  apply Subobject.le_of_factors
  rw [← Abelian.monoLift_comp K'.arrow K.arrow hz]
  exact Subobject.factors_comp_arrow _

/-- **A submodule of a module on the small étale site is determined by its sections over a dense
family of étale charts.** -/
theorem injective_subobject_range {ι : Type u} (c : ι → SmallEtale B S hS Z.1)
    [(inducedFunctor c).IsCoverDense (SmallEtale.topology B S hS Z.1)]
    (M : Modules.{u, u} B S hS Z.1 Z.2) :
    Function.Injective fun (K : Subobject M) (i : ι) =>
      Set.range (K.arrow.val.app (op (c i))) := by
  intro K K' h
  exact le_antisymm (subobject_le_of_range_subset c K K' fun i => (congrFun h i).le)
    (subobject_le_of_range_subset c K' K fun i => (congrFun h i).ge)

/-- **The submodules of a module on the small étale site are boundedly many**: if the sections
over every member of a dense family of étale charts number at most `μ`, there are at most
`(2 ^ μ) ^ #ι` submodules. -/
theorem mk_subobject_le {ι : Type u} (c : ι → SmallEtale B S hS Z.1)
    [(inducedFunctor c).IsCoverDense (SmallEtale.topology B S hS Z.1)]
    (M : Modules.{u, u} B S hS Z.1 Z.2) {μ : Cardinal.{u}}
    (hμ : ∀ i, #(M.val.obj (op (c i))) ≤ μ) :
    Cardinal.lift.{u} #(Subobject M) ≤ Cardinal.lift.{u + 1} (((2 : Cardinal.{u}) ^ μ) ^ #ι) := by
  refine (Cardinal.lift_mk_le_lift_mk_of_injective (injective_subobject_range c M)).trans
    (Cardinal.lift_le.2 ?_)
  rw [Cardinal.mk_pi, ← Cardinal.prod_const']
  refine Cardinal.prod_le_prod _ _ fun i => ?_
  rw [Cardinal.mk_set]
  exact Cardinal.power_le_power_left two_ne_zero (hμ i)

/-- A finite module over a ring of cardinality at most an infinite cardinal `σ` has cardinality at
most `σ`. -/
theorem mk_le_of_moduleFinite {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] {σ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (hR : #R ≤ σ) : #M ≤ σ := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R M
  exact (Cardinal.mk_le_of_surjective hg).trans ((Cardinal.mk_le_of_injective
    (f := fun v : Fin n → R => List.ofFn v) List.ofFn_injective).trans
    ((Cardinal.mk_list_le_max R).trans (max_le hσ hR)))

/-- For an infinite cardinal `σ` and `κ ≤ 2 ^ σ`, `(2 ^ σ) ^ κ ≤ 2 ^ 2 ^ σ`. -/
private theorem two_power_power_le_two_power_two_power {σ κ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ)
    (hκ : κ ≤ 2 ^ σ) : ((2 : Cardinal.{u}) ^ σ) ^ κ ≤ 2 ^ (2 : Cardinal.{u}) ^ σ := by
  have hν : ℵ₀ ≤ (2 : Cardinal.{u}) ^ σ := hσ.trans (Cardinal.cantor σ).le
  calc ((2 : Cardinal.{u}) ^ σ) ^ κ ≤ ((2 : Cardinal.{u}) ^ σ) ^ ((2 : Cardinal.{u}) ^ σ) :=
        Cardinal.power_le_power_left (Cardinal.power_ne_zero _ two_ne_zero) hκ
    _ = (2 : Cardinal.{u}) ^ (σ * (2 : Cardinal.{u}) ^ σ) := by rw [← Cardinal.power_mul]
    _ = (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ σ := by
        rw [Cardinal.mul_eq_right hν (Cardinal.cantor σ).le
          (Cardinal.aleph0_pos.trans_le hσ).ne']

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- **The submodules of `F_T` are boundedly many**, for an affine test scheme `T` and `F` of
finite type: at most `2 ^ 2 ^ size T`. The base change `X_T` is quasi-compact, so it has an
affine chart covering its small étale site, no larger than `T`; above it the small étale site has
a dense family of affine charts bounded by `2 ^ size T`, over each of which the sections of `F_T`
form a finite module over a ring no larger than `T`, and
`AlgebraicGeometry.Space.mk_subobject_le` applies. -/
theorem mk_subobject_baseChangeModule_le (hFt : SheafOfModules.IsFiniteTypeOnSite D.F)
    (T : SchemesOver D.Y) [IsAffine ((BigFppfOver.toScheme B S hS).obj T.left)] :
    Cardinal.lift.{u} #(Subobject (D.baseChangeModule T)) ≤
      Cardinal.lift.{u + 1} ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
        ((BigFppfOver.toScheme B S hS).obj T.left).size) := by
  have hqc : IsQuasiCompactSpace B S hS (D.space T).1 :=
    isQuasiCompactSpace_pullback_of_isQuasiCompact_pullback_snd B S hS D.f.hom D.X.2 D.Y.2
      (fun Z g => isQuasiCompact_pullback_snd_of_isQuasiCompact B S hS D.finitePresentation.2.1
        Z g) T.left T.hom.hom inferInstance
  obtain ⟨U₀, hU₀, hcov⟩ := SmallEtale.exists_affineObject_coversTop B S hS _ (D.space T).2 hqc
  have : IsAffine (chartScheme U₀) := hU₀
  set σ := ((BigFppfOver.toScheme B S hS).obj T.left).size
  have hσ : ℵ₀ ≤ σ := Scheme.aleph0_le_size _
  have hν : ℵ₀ ≤ (2 : Cardinal.{u}) ^ σ := hσ.trans (Cardinal.cantor σ).le
  have hU₀size : (chartScheme U₀).size ≤ σ := by
    let h : U₀.obj.left ⟶ T.left :=
      Yoneda.fullyFaithful.preimage (U₀.obj.hom ≫ (D.projection T).hom)
    have hid : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (𝟙 T.left)) :=
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
        (@Etale.{u} : MorphismProperty Scheme.{u}) (𝟙 T.left)).2
        (by rw [CategoryTheory.Functor.map_id]; infer_instance)
    have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h) :=
      D.isLocallyOfFiniteType_projection T U₀.obj.left T.left U₀.obj.hom
        (yoneda.map (𝟙 T.left)) h U₀.property hid
        (by
          rw [CategoryTheory.Functor.map_id]
          exact (Category.comp_id (yoneda.map h)).trans (Yoneda.fullyFaithful.map_preimage _))
    exact Scheme.size_le_of_locallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h)
  obtain ⟨ι, c, _, hι, hc⟩ := SmallEtale.exists_denseAffineFamily U₀ hcov
  have hΓ : ∀ (V : Scheme.{u}) [IsAffine V], V.size ≤ σ → #Γ(V, ⊤) ≤ σ := fun V _ h =>
    (V.mk_sections_le_size ⟨⊤, isAffineOpen_top _⟩).trans h
  have hΓ₀ : #Γ(chartScheme U₀, ⊤) ≤ σ := hΓ _ hU₀size
  have hισ : #ι ≤ 2 ^ σ :=
    hι.trans ((mul_le_mul' hν (Cardinal.power_le_power_left two_ne_zero (max_le hσ hΓ₀))).trans
      (Cardinal.mul_eq_self hν).le)
  have hqcG : (D.baseChangeModule T).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ D.F D.quasicoherent
  have hftG : SheafOfModules.IsFiniteTypeOnSite (D.baseChangeModule T) :=
    isFiniteTypeOnSite_modulePullback B S hS _ D.F hFt
  have hsec : ∀ i, #((D.baseChangeModule T).val.obj (op (c i))) ≤ σ := fun i => by
    have := moduleFinite_sections_of_isFiniteType B S hS _ _
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS _ _ _ hqcG)
      (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite _ hftG) (hc i).1
    obtain ⟨haff, f, hf⟩ := hc i
    exact mk_le_of_moduleFinite (R := chartRing B S hS _ _ (c i)) hσ
      (hΓ (chartScheme (c i)) ((Scheme.size_le_of_locallyOfFiniteType f).trans hU₀size))
  exact (mk_subobject_le c (D.baseChangeModule T) hsec).trans
    (Cardinal.lift_le.2 (two_power_power_le_two_power_two_power hσ hισ))

end QuotSituation

section OverBase

variable (X : AlgebraicSpaces B S hS) (f : X ⟶ schemeSpace (BigFppfOver.terminalObj B S hS))
  (hf : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
  (hF : F.IsQuasicoherentOnSite)

/-- **Axiom [-1] for `Quot_{F/X/S}`**, the set-theoretic input of Stacks 07Y1 which Remark 0CZW
leaves implicit. In the situation of the remark (where `F` is of finite
presentation, in particular of finite type), the set-theoretic condition of Artin's axioms holds
for `Quot_{F/X/S}`: there is an object `T` of the site whose size bounds the number of quotients
over every field `k` of finite type over `S`. Indeed the quotients of `F_k` are determined by
their kernels, the submodules of `F_k`, of which there are at most `2 ^ 2 ^ size S`
(`AlgebraicGeometry.Space.QuotSituation.mk_subobject_baseChangeModule_le`), a cardinal below
the cutoff of the site because the cutoff is a strong limit. The remark leaves this condition
implicit, as the source does in the proof of Stacks 08WC. -/
theorem exists_sizeBound_quotOverBase (hFt : SheafOfModules.IsFiniteTypeOnSite F) :
    ∃ T : BigFppfOver B S hS,
      ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k],
        U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B S hS U →
          Cardinal.mk ((quotOverBasePresheaf X f hf F hF).obj (op U)) ≤ T.left.1.size := by
  let D := quotOverBase X f hf F hF
  let ι : ∀ T : BigFppfOver B S hS, (schemeSpaceFunctor B S hS).obj T ⟶ D.Y :=
    fun T => ObjectProperty.homMk (yoneda.map (Over.homMk T.hom (by simp)))
  set ν : Cardinal.{u} := (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ S.size
  have hSν : S.size ≤ ν := (Cardinal.cantor S.size).le.trans (Cardinal.cantor _).le
  have hν : ν < B.cutoff := B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit hS)
  obtain ⟨T₀, hT₀⟩ := exists_le_size_of_le_of_lt (hS := hS) ν hSν hν
  refine ⟨T₀, fun U k _ hU hft => ?_⟩
  have haffU : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := by
    change IsAffine U.left.1
    rw [hU]
    infer_instance
  have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj U) := by
    change Nonempty U.left.1
    rw [hU]
    infer_instance
  have : LocallyOfFiniteType (B.inclusion.map U.hom) := hft.1
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (D.testOver ι U).left) := haffU
  have hinj : Function.Injective fun x : D.properlySupportedQuotients (D.testOver ι U) =>
      (x : Subobject (D.baseChangeModule (D.testOver ι U))) := Subtype.val_injective
  have h₁ : Cardinal.lift.{u + 1} #((quotOverBasePresheaf X f hf F hF).obj (op U)) =
      Cardinal.lift.{u} #(D.properlySupportedQuotients (D.testOver ι U)) := by
    have : Small.{u} (D.quotSitePresheaf.obj (op U)) := D.small_quotFamilyOver U
    exact Cardinal.lift_mk_eq'.2 ⟨(equivShrink.{u} (D.quotSitePresheaf.obj (op U))).symm.trans
      (Equiv.ofBijective _ ⟨D.ofQuot_injective ι U, D.ofQuot_surjective ι U⟩).symm⟩
  have key : Cardinal.lift.{u + 1} #((quotOverBasePresheaf X f hf F hF).obj (op U)) ≤
      Cardinal.lift.{u + 1} ν := by
    rw [h₁]
    exact (Cardinal.lift_le.2 (Cardinal.mk_le_of_injective hinj)).trans
      ((D.mk_subobject_baseChangeModule_le hFt (D.testOver ι U)).trans
        (Cardinal.lift_le.2 (Cardinal.power_le_power_left two_ne_zero
          (Cardinal.power_le_power_left two_ne_zero
            (Scheme.size_le_of_locallyOfFiniteType (B.inclusion.map U.hom))))))
  exact (Cardinal.lift_le.1 key).trans (hT₀ U hne)

end OverBase

end AlgebraicGeometry.Space
