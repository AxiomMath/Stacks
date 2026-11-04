module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ProjectiveSpaceQuotSituation
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.Functor

/-!
# The Quot presheaf of `𝒪` on `ℙⁿ_U ⟶ U`, read on `ℙⁿ_T`

A section of the Quot presheaf of `𝒪_{ℙⁿ_U}/ℙⁿ_U/U` over a scheme `T` of the site is a morphism
`T ⟶ U` together with a quotient of `𝒪_{ℙⁿ_T}` of finite presentation and flat over `T`
(`AlgebraicGeometry.C1590Private.quotPairsIso`), naturally in `T`: the second component is the
quotient read on `ℙⁿ_T` (`AlgebraicGeometry.C1590Private.quotKernel`), which commutes with base
change by `AlgebraicGeometry.C1590Private.quotKernel_quotientPullback`. A section lies in `Quot^P`
exactly when the quotient has Hilbert polynomial `P` on every fibre
(`AlgebraicGeometry.C1590Private.mem_hilbertSubfunctor_iff_quotPairsIso`).

## Main definitions

* `AlgebraicGeometry.C1590Private.familiesFunctor`: `T ↦ Quot_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)` on schemes.
* `AlgebraicGeometry.C1590Private.quotPairs`: `T ↦ Hom(T, U) × Quot_{𝒪/ℙⁿ/ℤ}(T)` on the site.
* `AlgebraicGeometry.C1590Private.quotPairsIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.C1590Private

open ProjectiveQuot ProjectiveQuotOverSpace

universe u

variable (n r : ℕ)

/-- **The functor `T ↦ Quot_{𝒪^{⊕ r}/ℙⁿ/ℤ}(T)`** on schemes, read on kernels: its value at `T` is
`AlgebraicGeometry.ProjectiveQuot.families n r T`, and a morphism acts by
`AlgebraicGeometry.ProjectiveQuot.baseChange`. -/
def familiesFunctor : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj T := families n r T.unop
  map g := TypeCat.ofHom fun K => ⟨baseChange g.unop K.1, baseChange_mem_families g.unop K.2⟩
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro K
    exact Subtype.ext (baseChange_id T.unop K.1)
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro K
    exact Subtype.ext (baseChange_comp h.unop g.unop K.1)

variable {B : BigFppfSite.{u}} (U : BigFppfOver B integerBase B.contains_integerBase)

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- **`T ↦ Hom(T, U) × S(T)`** on the schemes of the site, for a presheaf `S` on schemes. -/
def pairsPresheaf (S : Scheme.{u}ᵒᵖ ⥤ Type (u + 1)) :
    (BigFppfOver B integerBase B.contains_integerBase)ᵒᵖ ⥤ Type (u + 1) where
  obj T := (T.unop ⟶ U) × S.obj (Opposite.op ((𝒯).obj T.unop))
  map g := TypeCat.ofHom fun p => (g.unop ≫ p.1, S.map ((𝒯).map g.unop).op p.2)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro p
    refine Prod.ext (Category.id_comp _) ?_
    change S.map ((𝒯).map (𝟙 T.unop)).op p.2 = p.2
    rw [CategoryTheory.Functor.map_id, op_id, Functor.map_id_apply]
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro p
    refine Prod.ext (Category.assoc _ _ _) ?_
    change S.map ((𝒯).map (h.unop ≫ g.unop)).op p.2 =
      S.map ((𝒯).map h.unop).op (S.map ((𝒯).map g.unop).op p.2)
    rw [CategoryTheory.Functor.map_comp, op_comp, Functor.map_comp_apply]

/-- The morphisms of the site into `U` are the morphisms of algebraic spaces into `h_U`. -/
def schemeSpaceHomEquiv (T : BigFppfOver B integerBase B.contains_integerBase) :
    (T ⟶ U) ≃ (schemeSpace T ⟶ schemeSpace U) where
  toFun a := schemeSpaceMap a
  invFun b := yoneda.preimage b.hom
  left_inv a := yoneda.preimage_map a
  right_inv b := ObjectProperty.hom_ext _ (yoneda.map_preimage b.hom)

variable {n U}

/-- A section of the Quot presheaf is a morphism to the base together with a member of
`Quot_{F/X/B}` of the resulting test scheme. -/
def quotFamilyOverEquivSigma (D : Space.QuotSituation B integerBase B.contains_integerBase)
    (T : BigFppfOver B integerBase B.contains_integerBase) :
    Space.QuotFamilyOver D T ≃
      Σ b : (schemeSpaceFunctor B integerBase B.contains_integerBase).obj T ⟶ D.Y,
        D.properlySupportedQuotients (CostructuredArrow.mk b) where
  toFun x := ⟨x.toBase, x.subobject, x.mem⟩
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The objectwise identification of the Quot presheaf with `quotPairs`. -/
def quotPairsEquiv (T : BigFppfOver B integerBase B.contains_integerBase) :
    Space.QuotFamilyOver (projectiveSpaceQuotSituation n U) T ≃
      (T ⟶ U) × families n 1 ((𝒯).obj T) :=
  (quotFamilyOverEquivSigma _ T).trans <|
    (Equiv.sigmaCongrRight fun b => properlySupportedQuotientsFamiliesEquiv
      (hasUnitReading_projectiveSpaceFrame n U) (CostructuredArrow.mk b)).trans <|
    (Equiv.sigmaEquivProd ((schemeSpaceFunctor B integerBase B.contains_integerBase).obj T ⟶
      (projectiveSpaceQuotSituation n U).Y) (families n 1 ((𝒯).obj T))).trans <|
    Equiv.prodCongr (schemeSpaceHomEquiv U T).symm (Equiv.refl _)

theorem quotPairsEquiv_fst (T : BigFppfOver B integerBase B.contains_integerBase)
    (x : Space.QuotFamilyOver (projectiveSpaceQuotSituation n U) T) :
    schemeSpaceMap (quotPairsEquiv T x).1 = x.toBase :=
  (schemeSpaceHomEquiv U T).apply_symm_apply x.toBase

theorem quotPairsEquiv_snd (T : BigFppfOver B integerBase B.contains_integerBase)
    (x : Space.QuotFamilyOver (projectiveSpaceQuotSituation n U) T) :
    (quotPairsEquiv T x).2.1 =
      quotKernel (hasUnitReading_projectiveSpaceFrame n U) (CostructuredArrow.mk x.toBase)
        x.subobject :=
  rfl

/-- **The Quot presheaf of `𝒪_{ℙⁿ_U}/ℙⁿ_U/U` is `T ↦ Hom(T, U) × Quot_{𝒪/ℙⁿ/ℤ}(T)`.** -/
def quotPairsIso :
    (projectiveSpaceQuotSituation n U).quotSitePresheaf ≅ pairsPresheaf U (familiesFunctor n 1) :=
  NatIso.ofComponents (fun T => (quotPairsEquiv T.unop).toIso) fun {T T'} g => by
    ext x
    refine Prod.ext ?_ (Subtype.ext ?_)
    · apply (schemeSpaceHomEquiv U T'.unop).injective
      change schemeSpaceMap (quotPairsEquiv T'.unop (x.baseChange g.unop)).1 =
        schemeSpaceMap (g.unop ≫ (quotPairsEquiv T.unop x).1)
      rw [quotPairsEquiv_fst, AlgebraicGeometry.schemeSpaceMap_comp, quotPairsEquiv_fst T.unop x]
      rfl
    · exact quotKernel_quotientPullback (hasUnitReading_projectiveSpaceFrame n U)
        (Space.QuotFamilyOver.restrict g.unop x.toBase) x.subobject x.mem.1.1.1

theorem quotPairsIso_hom_app_snd (T : (BigFppfOver B integerBase B.contains_integerBase)ᵒᵖ)
    (x : (projectiveSpaceQuotSituation n U).quotSitePresheaf.obj T) :
    ((quotPairsIso (n := n) (U := U)).hom.app T x).2.1 =
      quotKernel (hasUnitReading_projectiveSpaceFrame n U) (CostructuredArrow.mk x.toBase)
        x.subobject :=
  rfl

/-- **A section lies in `Quot^P` exactly when the quotient of `𝒪_{ℙⁿ_T}` it corresponds to has
Hilbert polynomial `P` on every fibre.** -/
theorem mem_hilbertSubfunctor_iff_quotPairsIso (P : Polynomial ℚ)
    (T : (BigFppfOver B integerBase B.contains_integerBase)ᵒᵖ)
    (x : (projectiveSpaceQuotSituation n U).quotSitePresheaf.obj T) :
    x ∈ (hilbertSubfunctor (projectiveSpaceFrame n U) P).obj T ↔
      ((quotPairsIso (n := n) (U := U)).hom.app T x).2.1 ∈
        hilbertFamilies n 1 P ((𝒯).obj T.unop) :=
  mem_hilbertQuotients_iff_quotKernel_mem _ P _ x.subobject x.mem.1.1.1

end AlgebraicGeometry.C1590Private

end
