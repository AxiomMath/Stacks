module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoheratorFlatPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOpensCoproductCutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChangeConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProj
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Contains

/-!
# The quotient of Situation 0849 by a quasi-coherent graded ideal

In Situation 0849 let `ℐ ⊆ 𝒜` be a graded ideal whose homogeneous pieces are quasi-coherent
`𝒪_X`-modules. The quotient `𝒜 ⧸ ℐ` is again a quasi-coherent graded `𝒪_X`-algebra, so it is a
Situation 0849 on the same algebraic space, and the quotient map `𝒜 ⟶ 𝒜 ⧸ ℐ` is a map of graded
algebras which is surjective in every degree. This is the algebra whose relative Proj
Stacks 085L and 085M identify with a closed subspace of `Proj_X(𝒜)`.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.GradedIdeal`: a graded ideal of the algebra of
  Situation 0849 with quasi-coherent pieces.
* `AlgebraicGeometry.Space.RelativeProjSituation.GradedIdeal.quotientSituation`: Situation 0849
  for `𝒜 ⧸ ℐ`.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.GradedIdeal.isQuasicoherent_quotientAlgebra_piece`:
  the pieces of `𝒜 ⧸ ℐ` are quasi-coherent, being cokernels of maps of quasi-coherent modules
  (Stacks 03M1).
* `AlgebraicGeometry.Space.hasCardinalLT_sections_of_epi`: the sections of a quotient of a
  quasi-coherent module whose sections are bounded by the cutoff of the site are bounded by it
  too, which is the size field of Situation 0849 for `𝒜 ⧸ ℐ`.

## Implementation notes

The size bound is read off the étale chart whose scheme is the coproduct `∐ V` of all the affine
opens `V` of the scheme of a given chart: it is an object of the site
(`AlgebraicGeometry.BigFppfSite.contains_sigma_affineOpens`), its sections bound the sections
over each affine open of the chart at once, and an epimorphism of quasi-coherent modules is
surjective over affine charts. The cutoff being a strong limit, the product over the affine opens
stays below it.

## References

* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

/-! ### Bounding the sections of a quotient of a quasi-coherent module -/

section Cutoff

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The coproduct of all the affine opens of the scheme of an object of the big fppf site, as an
object of the site over `S` through the canonical morphism to that scheme. -/
noncomputable def affineOpensCoverObj (A : BigFppfOver B S hS) : BigFppfOver B S hS :=
  Over.mk (B.inclusion.preimage
    (show B.inclusion.obj ⟨∐ fun V : ((BigFppfOver.toScheme B S hS).obj A).affineOpens =>
          (V.1 : Scheme.{u}), B.contains_sigma_affineOpens A.left.property⟩ ⟶
        B.inclusion.obj A.left from Sigma.desc fun V => V.1.ι) ≫ A.hom)

/-- The canonical morphism from the coproduct of the affine opens. -/
noncomputable def affineOpensCoverHom (A : BigFppfOver B S hS) : affineOpensCoverObj A ⟶ A :=
  Over.homMk (B.inclusion.preimage
    (show B.inclusion.obj ⟨∐ fun V : ((BigFppfOver.toScheme B S hS).obj A).affineOpens =>
          (V.1 : Scheme.{u}), B.contains_sigma_affineOpens A.left.property⟩ ⟶
        B.inclusion.obj A.left from Sigma.desc fun V => V.1.ι)) rfl

/-- The morphism of schemes underlying `affineOpensCoverHom A` is the morphism `∐ V ⟶ T`
induced by the inclusions of the affine opens `V` of the scheme `T` of `A`. -/
theorem toScheme_map_affineOpensCoverHom (A : BigFppfOver B S hS) :
    (BigFppfOver.toScheme B S hS).map (affineOpensCoverHom A) =
      Sigma.desc fun V : ((BigFppfOver.toScheme B S hS).obj A).affineOpens => V.1.ι :=
  B.inclusion.map_preimage _

/-- The morphism of schemes underlying `affineOpensCoverHom A` is étale. -/
theorem etale_toScheme_map_affineOpensCoverHom (A : BigFppfOver B S hS) :
    Etale ((BigFppfOver.toScheme B S hS).map (affineOpensCoverHom A)) := by
  rw [toScheme_map_affineOpensCoverHom]
  have : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  exact IsZariskiLocalAtSource.sigmaDesc fun V => inferInstanceAs (Etale V.1.ι)

/-- The morphism of schemes underlying `affineOpensCoverHom A` is surjective. -/
theorem surjective_toScheme_map_affineOpensCoverHom (A : BigFppfOver B S hS) :
    Surjective ((BigFppfOver.toScheme B S hS).map (affineOpensCoverHom A)) := by
  rw [toScheme_map_affineOpensCoverHom]
  refine Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_of_forall fun x => ?_)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj A).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, ⟨x, hxV⟩, rfl⟩

variable {X : AlgebraicSpaces B S hS}

/-- The étale chart of `X` whose scheme is the coproduct of all the affine opens of the scheme of
an étale chart `V`, mapping to `X` through `V`. -/
noncomputable def affineOpensCoverChart (V : SmallEtale B S hS X.1) : SmallEtale B S hS X.1 :=
  ⟨CostructuredArrow.mk
      (yoneda.map (affineOpensCoverHom ((SmallEtale.toOver B S hS X.1).obj V)) ≫ V.1.hom),
    etale_comp_of_scheme B S hS _ V.1.hom (etale_toScheme_map_affineOpensCoverHom _) V.property⟩

/-- The morphism of étale charts from `affineOpensCoverChart V` to `V`. -/
noncomputable def affineOpensCoverChartHom (V : SmallEtale B S hS X.1) :
    affineOpensCoverChart V ⟶ V :=
  ObjectProperty.homMk (CostructuredArrow.homMk (affineOpensCoverHom _) rfl)

/-- **The sections of a quotient of a quasi-coherent module are bounded by the cutoff** as soon
as those of the module are: an epimorphism of quasi-coherent modules is surjective on the affine
étale charts, the sections over any chart embed into the product of the sections over its affine
opens, and those are bounded all at once by the sections over the coproduct of the affine opens,
which is an object of the site. -/
theorem hasCardinalLT_sections_of_epi {M N : Modules.{u, u} B S hS X.1 X.2} (q : M ⟶ N)
    (hq : Epi q)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (hbound : ∀ U : (SmallEtale B S hS X.1)ᵒᵖ, HasCardinalLT (M.val.obj U) B.cutoff)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) : HasCardinalLT (N.val.obj U) B.cutoff := by
  let V := U.unop
  let A := (SmallEtale.toOver B S hS X.1).obj V
  let T := (BigFppfOver.toScheme B S hS).obj A
  let W := affineOpensCoverChart V
  let g := affineOpensCoverChartHom V
  have hinj : Function.Injective (N.val.map g.op) := by
    intro a b hab
    have hsep := Stacks.SheafOfModules.isSeparated_presheaf N _
      (sieve_generate_singleton_chart_mem_topology B S hS X.1 g
        (surjective_toScheme_map_affineOpensCoverHom A))
    exact (Presieve.isSeparatedFor_iff_generate.mpr hsep).ext fun _ _ hg => by
      cases hg
      exact hab
  let PN : (chartScheme W).Modules := restrictToChart B S hS X.2 N W
  let PM : (chartScheme W).Modules := restrictToChart B S hS X.2 M W
  have : PM.IsQuasicoherent := isQuasicoherent_restrictToChart_viaIdEtaleChart B S hS X M hM W
  let j : ∀ Z : T.affineOpens, (Z.1 : Scheme.{u}) ⟶ chartScheme W :=
    fun Z => Sigma.ι (fun V : T.affineOpens => (V.1 : Scheme.{u})) Z
  have hje : ∀ Z, Sigma.ι (fun V : T.affineOpens => (V.1 : Scheme.{u})) Z ≫
      (Iso.refl (chartScheme W)).hom = j Z := fun Z => Category.comp_id _
  have : ∀ Z, _root_.AlgebraicGeometry.IsOpenImmersion (j Z) := fun Z => inferInstanceAs
    (_root_.AlgebraicGeometry.IsOpenImmersion
      (Sigma.ι (fun V : T.affineOpens => (V.1 : Scheme.{u})) Z))
  let O : T.affineOpens → (chartScheme W).Opens := fun Z => (j Z).opensRange
  have hOaff : ∀ Z, IsAffineOpen (O Z) := fun Z => by
    have : IsAffine (Z.1 : Scheme.{u}) := Z.2
    exact isAffineOpen_opensRange _
  have hcov : ⨆ Z, O Z = ⊤ := iSup_opensRange_eq_top_of_sigma_iso j (Iso.refl _) hje
  set c := #Γ(PM, ⊤) with hc
  have hclt : c < B.cutoff := by
    rw [hc, mk_restrictToChart_sections]
    exact (hasCardinalLT_iff_cardinal_mk_lt _ _).1 (hbound _)
  have hcO : ∀ Z, #Γ(PM, O Z) ≤ c := by
    intro Z
    have hbot : O Z ⊓ (⨆ k : {k // k ≠ Z}, O k) = ⊥ := by
      rw [inf_iSup_eq]
      exact iSup_eq_bot.2 fun k => disjoint_iff.1
        (disjoint_opensRange_of_sigma_iso j (Iso.refl _) hje (Ne.symm k.2))
    have htop : O Z ⊔ (⨆ k : {k // k ≠ Z}, O k) = ⊤ := by
      rw [eq_top_iff, ← hcov]
      refine iSup_le fun k => ?_
      by_cases hk : k = Z
      · subst hk
        exact le_sup_left
      · exact le_sup_of_le_right (le_iSup (fun k : {k // k ≠ Z} => O k) ⟨k, hk⟩)
    have h := Scheme.Modules.mk_sections_le_of_inf_eq_bot PM hbot
    rwa [htop] at h
  have hNO : ∀ Z, #Γ(PN, O Z) ≤ c := by
    intro Z
    refine le_trans ?_ (hcO Z)
    rw [mk_restrictToChart_sections, mk_restrictToChart_sections]
    exact Cardinal.mk_le_of_surjective
      (surjective_val_app_of_epi_of_isQuasicoherentOnSite q hq hM hN _ (hOaff Z))
  let F : TopCat.Sheaf AddCommGrpCat.{u} (chartScheme W) := ⟨PN.presheaf, PN.isSheaf⟩
  have hinj' : Function.Injective
      (fun s : Γ(PN, ⊤) => fun Z : T.affineOpens =>
        PN.presheaf.map (homOfLE (le_top : O Z ≤ ⊤)).op s) := by
    intro a b hab
    exact TopCat.Sheaf.eq_of_locally_eq' F O ⊤ (fun Z => homOfLE le_top) hcov.ge a b
      (fun Z => congrFun hab Z)
  have hT : T.size < B.cutoff := A.left.property
  have hc0 : c ≠ 0 := Cardinal.mk_ne_zero _
  have hWtop : #(N.val.obj (op W)) = #Γ(PN, ⊤) := by
    rw [mk_restrictToChart_sections]
    exact Cardinal.mk_congr ((N.val.presheaf.mapIso
      (openChartTopIso B S hS X.1 W).op).addCommGroupIsoToAddEquiv.toEquiv)
  rw [hasCardinalLT_iff_cardinal_mk_lt]
  calc #(N.val.obj U) ≤ #(N.val.obj (op W)) := Cardinal.mk_le_of_injective hinj
    _ = #Γ(PN, ⊤) := hWtop
    _ ≤ #(∀ Z : T.affineOpens, Γ(PN, O Z)) := Cardinal.mk_le_of_injective hinj'
    _ = Cardinal.prod fun Z : T.affineOpens => #Γ(PN, O Z) := Cardinal.mk_pi _
    _ ≤ Cardinal.prod fun _ : T.affineOpens => c := Cardinal.prod_le_prod _ _ hNO
    _ = c ^ #T.affineOpens := by rw [Cardinal.prod_const, lift_id, lift_id]
    _ ≤ c ^ T.size := Cardinal.power_le_power_left hc0 T.mk_affineOpens_le_size
    _ < B.cutoff :=
        power_lt_of_isStrongPrelimit B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hclt hT

end Cutoff

end AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable (s : RelativeProjSituation.{u, u})

/-- A quasi-coherent graded ideal of the graded algebra of Situation 0849. -/
structure GradedIdeal extends SheafOfModules.GradedAlgebra.Ideal s.algebra where
  /-- Every homogeneous piece of the ideal is a quasi-coherent `𝒪_X`-module. -/
  isQuasicoherent (n : ℤ) : (piece n).toSheafOfModules.IsQuasicoherentOnSite

namespace GradedIdeal

variable {s} (I : s.GradedIdeal)

/-- The quotient `𝒜 ⧸ ℐ`, a sheaf of graded `𝒪_X`-algebras. -/
abbrev quotientAlgebra :
    SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf s.site s.base s.containsBase s.space) :=
  I.toIdeal.quotient

/-- The quotient map `𝒜 ⟶ 𝒜 ⧸ ℐ`. -/
abbrev quotientMap : SheafOfModules.GradedAlgebra.UnitalHom s.algebra I.quotientAlgebra :=
  I.toIdeal.quotientMap

/-- The quotient map is the cokernel of the inclusion of the ideal, in every degree. -/
def isColimitQuotientMap (n : ℤ) :
    IsColimit (CokernelCofork.ofπ (I.quotientMap.app n)
      (Stacks.SheafOfModules.kerSubmodule_ι_comp (I.toIdeal.quotientMapApp n))) :=
  Abelian.epiIsCokernelOfKernel _
    (Stacks.SheafOfModules.isLimitKernelForkKerSubmodule (I.toIdeal.quotientMapApp n))

/-- **The homogeneous pieces of `𝒜 ⧸ ℐ` are quasi-coherent**: each is the cokernel of a map of
quasi-coherent modules (Stacks 03M1). -/
theorem isQuasicoherent_quotientAlgebra_piece (n : ℤ) :
    (I.quotientAlgebra.piece n).IsQuasicoherentOnSite := by
  have hI : (Stacks.SheafOfModules.kerSubmodule
      (I.toIdeal.quotientMapApp n)).toSheafOfModules.IsQuasicoherentOnSite := by
    rw [I.toIdeal.kerSubmodule_quotientMapApp n]
    exact I.isQuasicoherent n
  let : ObjectProperty.IsClosedUnderCokernels
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureRingSheaf s.site s.base s.containsBase s.space)) :=
    isClosedUnderCokernels_quasicoherentSheaves_algebraicSpace s.site s.base s.containsBase s.space
  exact ObjectProperty.prop_of_isColimit_cokernelCofork
    (P := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf s.site s.base s.containsBase s.space))
    (I.isColimitQuotientMap n) hI (s.isQuasicoherent n)

/-- **Situation 0849 for the quotient `𝒜 ⧸ ℐ`**: the same site, base and algebraic space, with
the quotient of the graded algebra by a quasi-coherent graded ideal. -/
abbrev quotientSituation : RelativeProjSituation.{u, u} where
  site := s.site
  base := s.base
  containsBase := s.containsBase
  space := s.space
  algebra := I.quotientAlgebra
  mul_comm := I.toIdeal.quotient_mul_comm s.mul_comm
  negative_isZero n hn := I.toIdeal.isZero_quotient_piece (s.negative_isZero n hn)
  isQuasicoherent := I.isQuasicoherent_quotientAlgebra_piece
  sections_hasCardinalLT n :=
    hasCardinalLT_sections_of_epi (I.toIdeal.quotientMapApp n) (I.toIdeal.epi_quotientMapApp n)
      (s.isQuasicoherent n)
      (I.isQuasicoherent_quotientAlgebra_piece n) (s.sections_hasCardinalLT n)

/-- The site of `I.quotientSituation` is that of `s`. -/
@[simp] theorem quotientSituation_site : I.quotientSituation.site = s.site := rfl

/-- The base scheme of `I.quotientSituation` is that of `s`. -/
@[simp] theorem quotientSituation_base : I.quotientSituation.base = s.base := rfl

/-- The algebraic space of `I.quotientSituation` is that of `s`. -/
@[simp] theorem quotientSituation_space : I.quotientSituation.space = s.space := rfl

/-- The graded algebra of `I.quotientSituation` is the quotient `𝒜 ⧸ ℐ`. -/
theorem quotientSituation_algebra : I.quotientSituation.algebra = I.quotientAlgebra := rfl

end GradedIdeal

end AlgebraicGeometry.Space.RelativeProjSituation
