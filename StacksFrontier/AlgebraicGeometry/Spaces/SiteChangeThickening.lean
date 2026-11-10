module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalizeSiteChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatLocusAdicThickenings
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.BaseIdealSheaf

/-!
# Thickenings of a space over `Spec R`, read over `Spec R`

Let `h : Spec R ⟶ S` be a morphism of a big fppf site, `X` an algebraic space over `S` with a
morphism `π : X ⟶ Spec R`, `X'` the algebraic space over `Spec R` it is (Stacks 04SG,
`AlgebraicGeometry.Space.siteChangeSpace`), and `I ⊆ R` an ideal.  For a base change
`ι : Z ⟶ X` of a thickening `Spec(R/I^{n+1}) ⟶ Spec R` along `π`, and the adic fibre
`j : X'_n ⟶ X'` of `X'` (`AlgebraicGeometry.Space.adicFibreInclusion`), the equivalence
`Φ : Mod(𝒪_X) ⥤ Mod(𝒪_{X'})` of `AlgebraicGeometry.Space.siteChangeModules` carries
`ι_* ι^* N` to `j_* j^* (Φ N)` and to the term `Φ N / (I 𝒪_{X'})^{n+1} Φ N` of the completion
of Stacks 08B4, compatibly with the units and the projections.

## Main definitions

* `AlgebraicGeometry.Space.siteChangeThickeningIso`:
  `Φ(ι_* ι^* N) ≅ Φ N / (I 𝒪_{X'})^{n+1} Φ N`.

## Main results

* `AlgebraicGeometry.Space.map_unit_siteChangeThickeningIso_hom`: the isomorphism carries the
  image of the unit `N ⟶ ι_* ι^* N` to the projection of the completion.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 08B4](https://stacks.math.columbia.edu/tag/08B4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

section Thickening

variable (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ)

/-- The thickening `Spec(R/I^{n+1}) ⟶ Spec R` on global functions, read through `Γ(Spec R) ≅ R`. -/
theorem appTop_adicThickeningι :
    (adicThickeningι R I n).appTop = (Scheme.ΓSpecIso (.of R)).hom ≫
      CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))) ≫
        (Scheme.ΓSpecIso (.of (R ⧸ I ^ (n + 1)))).inv := by
  rw [Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
  rfl

/-- The thickening `Spec(R/I^{n+1}) ⟶ Spec R` on global functions is surjective. -/
theorem surjective_appTop_adicThickeningι :
    Function.Surjective (adicThickeningι R I n).appTop.hom := by
  intro y
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective ((Scheme.ΓSpecIso (.of (R ⧸ I ^ (n + 1)))).hom y)
  refine ⟨(Scheme.ΓSpecIso (.of R)).inv x, ?_⟩
  rw [appTop_adicThickeningι]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, hx,
    ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

/-- The kernel of the thickening on global functions is `I^{n+1}`, read through `Γ(Spec R) ≅ R`. -/
theorem ker_appTop_adicThickeningι :
    RingHom.ker (adicThickeningι R I n).appTop.hom =
      Ideal.map (Scheme.ΓSpecIso (.of R)).inv.hom (I ^ (n + 1)) := by
  have hmap : Ideal.map (Scheme.ΓSpecIso (.of R)).inv.hom (I ^ (n + 1)) =
      Ideal.comap (Scheme.ΓSpecIso (.of R)).hom.hom (I ^ (n + 1)) :=
    Ideal.map_comap_of_equiv (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm
  rw [hmap]
  ext x
  rw [RingHom.mem_ker, Ideal.mem_comap, appTop_adicThickeningι]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso _).1, Ideal.Quotient.eq_zero_iff_mem]

/-- Global functions of a morphism that is the thickening up to an isomorphism of its source. -/
private theorem appTop_hom_of_eq_comp_adicThickeningι {Z : Scheme.{u}} (τ : Z ⟶ Spec (.of R))
    (e : Z ≅ adicThickening R I n) (hτ : τ = e.hom ≫ adicThickeningι R I n) :
    τ.appTop.hom = e.hom.appTop.hom.comp (adicThickeningι R I n).appTop.hom ∧
      Function.Bijective e.hom.appTop.hom := by
  subst hτ
  have : IsIso e.hom.appTop := inferInstanceAs (IsIso (Scheme.Γ.map e.hom.op))
  exact ⟨by rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp],
    ConcreteCategory.bijective_of_isIso _⟩

/-- A morphism of schemes into `Spec R` which is the thickening up to an isomorphism of its
source is surjective on global functions. -/
theorem surjective_appTop_of_eq_comp_adicThickeningι {Z : Scheme.{u}} (τ : Z ⟶ Spec (.of R))
    (e : Z ≅ adicThickening R I n) (hτ : τ = e.hom ≫ adicThickeningι R I n) :
    Function.Surjective τ.appTop.hom := by
  obtain ⟨h₁, h₂⟩ := appTop_hom_of_eq_comp_adicThickeningι R I n τ e hτ
  rw [h₁]
  exact h₂.2.comp (surjective_appTop_adicThickeningι R I n)

/-- A morphism of schemes into `Spec R` which is the thickening up to an isomorphism of its
source has the kernel of the thickening on global functions. -/
theorem ker_appTop_of_eq_comp_adicThickeningι {Z : Scheme.{u}} (τ : Z ⟶ Spec (.of R))
    (e : Z ≅ adicThickening R I n) (hτ : τ = e.hom ≫ adicThickeningι R I n) :
    RingHom.ker τ.appTop.hom = RingHom.ker (adicThickeningι R I n).appTop.hom := by
  obtain ⟨h₁, h₂⟩ := appTop_hom_of_eq_comp_adicThickeningι R I n τ e hτ
  rw [h₁]
  exact RingHom.ker_comp_of_injective _ h₂.1

end Thickening

/-! ### The scalars of the base ring -/

section Scalars

variable {B : BigFppfSite.{u}} {R : Type u} [CommRing R] {hR : B.Contains (Spec (.of R))}

/-- On an algebraic space over `Spec R`, the scalars pulled back along any morphism to `Spec R`
are the scalars of the base ring. -/
theorem targetScalars_comp_ΓSpecIso_inv (Y : AlgebraicSpaces B (Spec (.of R)) hR)
    (f : Y ⟶ schemeSpace (baseObject R B hR)) :
    (targetScalars B (Spec (.of R)) hR f).comp (Scheme.ΓSpecIso (.of R)).inv.hom =
      baseRingHom R B hR Y.1 Y.2 := by
  ext a V
  change ((BigFppfOver.toScheme B (Spec (.of R)) hR).map (chartToTarget B (Spec (.of R)) hR f
      V.unop)).appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom a) =
    (((Scheme.ΓSpecIso (.of R)).inv ≫ Scheme.Γ.map ((B.inclusion.map
      ((SmallEtale.toOver B (Spec (.of R)) hR Y.1).obj V.unop).hom).op)).hom a)
  have h2 : (chartToTarget B (Spec (.of R)) hR f V.unop).left = V.unop.1.left.hom := by
    simpa using Over.w (chartToTarget B (Spec (.of R)) hR f V.unop)
  change (B.inclusion.map (chartToTarget B (Spec (.of R)) hR f V.unop).left).appTop.hom
    ((Scheme.ΓSpecIso (.of R)).inv.hom a) = _
  rw [h2]
  rfl

end Scalars

/-! ### The equivalence of module categories and the thickenings -/

section SiteChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {R : Type u} [CommRing R]
  {hR : B.Contains (Spec (.of R))} {h : B.obj hR ⟶ B.obj hS}
  (X : AlgebraicSpaces B S hS) (π : X ⟶ schemeSpace (Over.mk h))

/-- The scalars of the base ring `R` on `𝒪_X`-modules: pull back along `π` through
`Γ(Spec R) ≅ R`. -/
abbrev baseScalars : R →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) :=
  (targetScalars B S hS π).comp (Scheme.ΓSpecIso (.of R)).inv.hom

/-- The canonical morphism from the space over `Spec R` underlying `X` to `Spec R`. -/
abbrev siteChangeStructure : siteChangeSpace B X π ⟶ schemeSpace (baseObject R B hR) :=
  (terminalSpace_unique B (Spec (.of R)) hR (siteChangeSpace B X π)).default

/-- **The equivalence of module categories carries the scalars of `R` on `X` to the scalars of
the base ring on `X'`.** -/
theorem siteChangeModules_map_globalSmul_baseScalars (a : R) (N : Modules.{u, u} B S hS X.1 X.2) :
    (siteChangeModules B X π).map
        (Stacks.Cohomology.SiteModules.globalSmul _ (baseScalars X π a) N) =
      Stacks.Cohomology.SiteModules.globalSmul _
        (baseRingHom R B hR (siteChangeSpace B X π).1 (siteChangeSpace B X π).2 a)
        ((siteChangeModules B X π).obj N) := by
  refine (siteChangeModules_map_globalSmul B X π (siteChangeStructure X π)
    ((Scheme.ΓSpecIso (.of R)).inv.hom a) N).trans ?_
  rw [← targetScalars_comp_ΓSpecIso_inv (siteChangeSpace B X π) (siteChangeStructure X π)]
  rfl

/-- **The equivalence carries `N / J N` to `Φ N / J Φ N`** for an ideal `J` of `R`. -/
def siteChangeBaseQuotientIso (N : Modules.{u, u} B S hS X.1 X.2) (J : Ideal R) :
    (siteChangeModules B X π).obj (idealQuotient (baseScalars X π) N J) ≅
      idealQuotient (baseRingHom R B hR (siteChangeSpace B X π).1 (siteChangeSpace B X π).2)
        ((siteChangeModules B X π).obj N) J :=
  idealQuotientEquivalenceIso _ _ (siteChangeModules B X π)
    (fun a N => siteChangeModules_map_globalSmul_baseScalars X π a N) N J

/-- `siteChangeBaseQuotientIso` carries the image of the projection `N ⟶ N / J N` to the
projection `Φ N ⟶ Φ N / J Φ N`. -/
@[reassoc (attr := simp)]
theorem map_idealQuotientπ_siteChangeBaseQuotientIso_hom
    (N : Modules.{u, u} B S hS X.1 X.2) (J : Ideal R) :
    (siteChangeModules B X π).map (idealQuotientπ (baseScalars X π) N J) ≫
        (siteChangeBaseQuotientIso X π N J).hom =
      idealQuotientπ _ ((siteChangeModules B X π).obj N) J :=
  map_idealQuotientπ_idealQuotientEquivalenceIso_hom _ _ _ _ N J

end SiteChange

section Congr

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F} {A : Type u} [CommRing A]
  (φ : A →+* ↥(Stacks.Cohomology.SiteModules.GlobalSectionRing
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))))
  (N : Modules.{u, u} B S hS F hF)

/-- Equal ideals give the same quotient, compatibly with the projections. -/
theorem idealQuotientπ_eqToHom {J₁ J₂ : Ideal A} (hJ : J₁ = J₂) :
    idealQuotientπ φ N J₁ ≫ eqToHom (congrArg (idealQuotient φ N) hJ) = idealQuotientπ φ N J₂ := by
  subst hJ
  simp

end Congr

section Thickening

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {R : Type u} [CommRing R]
  {hR : B.Contains (Spec (.of R))} {h : B.obj hR ⟶ B.obj hS}
  (X : AlgebraicSpaces B S hS) (π : X ⟶ schemeSpace (Over.mk h)) (I : Ideal R) (n : ℕ)
  {Z : AlgebraicSpaces B S hS} {T' : BigFppfOver B S hS} (ι' : T' ⟶ Over.mk h)
  (i : Z ⟶ X) (p : Z ⟶ schemeSpace T') (hpb : IsPullback i p π (schemeSpaceMap ι'))
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  (hι : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι'))
  (hsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map ι').appTop.hom)
  (hJ : siteMapKer B S hS ι' = Ideal.map (Scheme.ΓSpecIso (.of R)).inv.hom (I ^ (n + 1)))

/-- The object `Spec R` of the site over `S`, given by `h`, is affine. -/
instance isAffine_toScheme_overMk_of_hom :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (Over.mk h)) :=
  inferInstanceAs (IsAffine (Spec (.of R)))

/-- **The equivalence of module categories carries the direct image of the restriction to a
thickening to the corresponding term of the completion**:
`Φ(ι_* ι^* N) ≅ Φ N / (I 𝒪_{X'})^{n+1} Φ N`. -/
def siteChangeThickeningIso (N : Modules.{u, u} B S hS X.1 X.2) :
    (siteChangeModules B X π).obj
        ((modulePushforward B S hS i).obj ((modulePullback B S hS i).obj N)) ≅
      smallEtaleAdicQuotient B (Spec (.of R)) hR (siteChangeSpace B X π).1
        (siteChangeSpace B X π).2 (C1573.baseIdealSubmodule (siteChangeSpace B X π).1
          (siteChangeSpace B X π).2 I) (n + 1) ((siteChangeModules B X π).obj N) :=
  (siteChangeModules B X π).mapIso
      ((baseChangeQuotientIso B S hS π ι' i p hpb hι hsurj N).symm ≪≫
        eqToIso (congrArg (idealQuotient (targetScalars B S hS π) N) hJ) ≪≫
        (idealQuotientCompIso (targetScalars B S hS π) (Scheme.ΓSpecIso (.of R)).inv.hom
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).2 N
            (I ^ (n + 1))).symm) ≪≫
    siteChangeBaseQuotientIso X π N (I ^ (n + 1)) ≪≫
    (C1573.baseIdealQuotientIso ((siteChangeModules B X π).obj N) I (n + 1)).symm

/-- The isomorphism `Φ(ι_* ι^* N) ≅ Φ N / (I 𝒪_{X'})^{n+1} Φ N` carries the image of the unit
`N ⟶ ι_* ι^* N` to the projection of the completion. -/
@[reassoc (attr := simp)]
theorem map_unit_siteChangeThickeningIso_hom (N : Modules.{u, u} B S hS X.1 X.2) :
    (siteChangeModules B X π).map ((modulePullbackAdjunction B S hS i).unit.app N) ≫
        (siteChangeThickeningIso X π I n ι' i p hpb hι hsurj hJ N).hom =
      smallEtaleAdicQuotientProjection B (Spec (.of R)) hR (siteChangeSpace B X π).1
        (siteChangeSpace B X π).2 (C1573.baseIdealSubmodule (siteChangeSpace B X π).1
          (siteChangeSpace B X π).2 I) (n + 1) ((siteChangeModules B X π).obj N) := by
  have e1 := idealQuotientπ_baseChangeQuotientIso_hom B S hS π ι' i p hpb hι hsurj N
  have e2 := idealQuotientπ_eqToHom (targetScalars B S hS π) N hJ
  have e3 := (Iso.comp_inv_eq _).mpr (idealQuotientπ_idealQuotientCompIso_hom
    (targetScalars B S hS π) (Scheme.ΓSpecIso (.of R)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).2 N
    (I ^ (n + 1))).symm
  have e4 := map_idealQuotientπ_siteChangeBaseQuotientIso_hom X π N (I ^ (n + 1))
  have e5 := C1573.smallEtaleAdicQuotientProjection_baseIdealQuotientIso_hom
    ((siteChangeModules B X π).obj N) I (n + 1)
  rw [← e1]
  simp only [siteChangeThickeningIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    eqToIso.hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc ((siteChangeModules B X π)) (baseChangeQuotientIso B S hS π ι' i p
    hpb hι hsurj N).hom, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    ← Functor.map_comp_assoc, e2, ← Functor.map_comp_assoc, e3,
    reassoc_of% e4, ← e5, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Thickening

end AlgebraicGeometry.Space

end
