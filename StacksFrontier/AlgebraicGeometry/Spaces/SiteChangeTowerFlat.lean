module

public import StacksFrontier.AlgebraicGeometry.Spaces.SiteChangeTower
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOverLocalBaseProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModulesFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFinitenessDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Extension
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubschemeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation

/-!
# Flatness on a tower of thickenings

Let `𝒯` be a tower of thickenings `i_n : Z_n ⟶ X` of a space `π : X ⟶ Spec R` over `S`
(`AlgebraicGeometry.Space.SiteChangeTower`), for a Noetherian local ring `R` and an ideal
`I ⊆ 𝔪`.  The base change `Λ(X'_n)` of the adic fibre of the space `X'` over `Spec R` is
identified with `Z_n` (`AlgebraicGeometry.Space.SiteChangeTower.adicFibreIso`), and through it
flatness of the restrictions `i_n^* N` over `T_n` gives flatness of the restrictions of `Ψ N` to
the adic fibres of `X'`.  With Stacks 08VP this makes a coherent `𝒪_X`-module with support proper
over `Spec R` whose restrictions to the `Z_n` are flat over the `T_n` flat over `Spec R`
(`AlgebraicGeometry.Space.SiteChangeTower.isFlatOver_of_isFlatOver_restrictions`).

## References

* [Stacks Project, Tag 08VP](https://stacks.math.columbia.edu/tag/08VP)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] CategoryTheory.catToReflQuiver

namespace SiteChangeTower

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {R : Type u} [CommRing R]
  {hR : B.Contains (Spec (.of R))} {h : B.obj hR ⟶ B.obj hS}
  {X : AlgebraicSpaces B S hS} {π : X ⟶ schemeSpace (Over.mk h)} {I : Ideal R}
  {Z : ℕ → AlgebraicSpaces B S hS} {i : ∀ n, Z n ⟶ X} {s : ∀ n, Z n ⟶ Z (n + 1)}
  {T : ℕ → BigFppfOver B S hS} {ι : ∀ n, T n ⟶ Over.mk h} {p : ∀ n, Z n ⟶ schemeSpace (T n)}
  (𝒯 : SiteChangeTower X π I Z i s T ι p) (n : ℕ)

include 𝒯

/-- The identification `Spec(R/I^{n+1}) ≅ T_n` followed by the scheme map of `ι_n` is the
structure morphism `Spec(R/I^{n+1}) ⟶ Spec R`. -/
theorem iso_inv_comp_toScheme_map :
    (𝒯.thickIso n).inv ≫ (BigFppfOver.toScheme B S hS).map (ι n) = adicThickeningι R I n := by
  rw [𝒯.thickIso_spec n, Iso.inv_hom_id_assoc]

/-- The identification of the thickening `T_n` with the image of `Spec(R/I^{n+1})`. -/
def thickeningIsoOver :
    (Over.map h).obj (adicThickeningObject R I B hR (contains_adicThickening R I B hR) n) ≅
      T n :=
  Over.isoMk (ObjectProperty.isoMk _ (𝒯.thickIso n).symm) (by
    apply ObjectProperty.hom_ext
    have hw : (ι n).left.hom ≫ h.hom = (T n).hom.hom :=
      congrArg (fun m => m.hom) (Over.w (ι n))
    have hi : (𝒯.thickIso n).inv ≫ (ι n).left.hom = adicThickeningι R I n :=
      𝒯.iso_inv_comp_toScheme_map n
    change (𝒯.thickIso n).inv ≫ (T n).hom.hom = adicThickeningι R I n ≫ h.hom
    rw [← hw, ← Category.assoc, hi])

/-- The identification `thickeningIsoOver` followed by `ι_n` is the structure morphism of
`Spec(R/I^{n+1})` over `Spec R`. -/
theorem thickeningIsoOver_hom_comp :
    (𝒯.thickeningIsoOver n).hom ≫ ι n =
      (Over.homMk (adicThickeningObject R I B hR (contains_adicThickening R I B hR) n).hom rfl :
        (Over.map h).obj (adicThickeningObject R I B hR (contains_adicThickening R I B hR) n) ⟶
          Over.mk h) := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  refine Eq.trans ?_ (𝒯.iso_inv_comp_toScheme_map n)
  rfl

/-- `Λ(Spec(R/I^{n+1})) ≅ T_n`, as presheaves. -/
def thickeningPresheafIso :
    (OverShriek.relocalizePresheafFunctor h).obj
        (yoneda.obj (adicThickeningObject R I B hR (contains_adicThickening R I B hR) n)) ≅
      yoneda.obj (T n) :=
  (OverShriek.relocalizeYonedaIso h).app _ ≪≫ yoneda.mapIso (𝒯.thickeningIsoOver n)

/-- The relocalized map `Λ(Spec(R/I^{n+1})) ⟶ Λ(Spec R) ⟶ Spec R` is `ι_n`, through
`thickeningPresheafIso`. -/
theorem relocalize_thickeningMap_comp :
    (OverShriek.relocalizePresheafFunctor h).map
        (yoneda.map (adicThickeningMap R I B hR (contains_adicThickening R I B hR) n)) ≫
        OverShriek.relocalizeToYoneda h (yoneda.obj (baseObject R B hR)) =
      (𝒯.thickeningPresheafIso n).hom ≫ yoneda.map (ι n) := by
  rw [relocalizeToYoneda_naturality B (Spec (.of R)) S hR hS h,
    ← AlgebraicGeometry.Stack.relocalizeToYoneda_yoneda h, thickeningPresheafIso, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc, ← Functor.map_comp, thickeningIsoOver_hom_comp]

/-- The square `Λ(X'_n) ⟶ X`, `Λ(X'_n) ⟶ T_n` over `π` and `ι_n` is cartesian. -/
theorem isPullback_relocalize_adicFibre :
    IsPullback
      ((OverShriek.relocalizePresheafFunctor h).map
          (adicFibreInclusion R I B hR (siteChangeSpace B X π) (siteChangeStructure X π) n).hom ≫
        (siteChangeIso B X π).hom.hom)
      ((OverShriek.relocalizePresheafFunctor h).map
          (adicFibreProjection R I B hR (siteChangeSpace B X π) (siteChangeStructure X π) n).hom ≫
        (𝒯.thickeningPresheafIso n).hom)
      π.hom (yoneda.map (ι n)) := by
  have : PreservesLimitsOfShape WalkingCospan (OverShriek.relocalizePresheafFunctor h) :=
    relocalizePresheaf_preservesConnectedLimits h
  have h0 := (AlgebraicSpaces.isPullback_hom B (Spec (.of R)) hR
    (isPullback_adicFibre R I B hR (siteChangeSpace B X π) (siteChangeStructure X π) n)).map
      (OverShriek.relocalizePresheafFunctor h)
  refine h0.of_iso (Iso.refl _) ((ObjectProperty.ι _).mapIso (siteChangeIso B X π))
    (𝒯.thickeningPresheafIso n)
    (@asIso _ _ _ _ (OverShriek.relocalizeToYoneda h (yoneda.obj (baseObject R B hR)))
      (isIso_relocalizeToYoneda_yonedaId B (Spec (.of R)) S hR hS h)) ?_ ?_ ?_ ?_
  · simp
  · simp
  · exact relocalize_siteChangeStructure_comp X π
  · exact 𝒯.relocalize_thickeningMap_comp n

/-- **`Λ(X'_n) ≅ Z_n`**, over `X` and over `T_n`. -/
def adicFibreIso :
    relocalizeSpace B hR hS h
        (adicFibreSpaceOf R I B hR (siteChangeSpace B X π) (siteChangeStructure X π) n) ≅ Z n :=
  ObjectProperty.isoMk _
    ((𝒯.isPullback_relocalize_adicFibre n).isoIsPullback _ _
      (AlgebraicSpaces.isPullback_hom B S hS (𝒯.isPullback n)))

/-- The identification `Λ(X'_n) ≅ Z_n` lies over `X`: composed with `i_n` it is the
relocalized adic fibre inclusion followed by `siteChangeIso`. -/
theorem adicFibreIso_hom_i :
    (𝒯.adicFibreIso n).hom ≫ i n =
      relocalizeHom B hR hS h
          (adicFibreInclusion R I B hR (siteChangeSpace B X π) (siteChangeStructure X π) n) ≫
        (siteChangeIso B X π).hom :=
  ObjectProperty.hom_ext _ (IsPullback.isoIsPullback_hom_fst _ _
    (𝒯.isPullback_relocalize_adicFibre n) (AlgebraicSpaces.isPullback_hom B S hS (𝒯.isPullback n)))

/-- The identification `Λ(X'_n) ≅ Z_n` lies over `T_n`: composed with `p_n` it is the
relocalized adic fibre projection followed by `thickeningPresheafIso`. -/
theorem adicFibreIso_hom_p :
    (𝒯.adicFibreIso n).hom.hom ≫ (p n).hom =
      (OverShriek.relocalizePresheafFunctor h).map
          (adicFibreProjection R I B hR (siteChangeSpace B X π) (siteChangeStructure X π) n).hom ≫
        (𝒯.thickeningPresheafIso n).hom :=
  IsPullback.isoIsPullback_hom_snd _ _
    (𝒯.isPullback_relocalize_adicFibre n) (AlgebraicSpaces.isPullback_hom B S hS (𝒯.isPullback n))

omit 𝒯 in
/-- The inclusion of an adic fibre is representable. -/
theorem relativelyRepresentable_adicFibreInclusion :
    yoneda.relativelyRepresentable
      (adicFibreInclusion R I B hR (siteChangeSpace B X π) (siteChangeStructure X π) n).hom :=
  relativelyRepresentable_hom_of_isFinite B (Spec (.of R)) hR _
    (isFinite_of_isClosedImmersion B (Spec (.of R)) hR _
      (isClosedImmersion_of_isPullback_schemeSpaceMap B (Spec (.of R)) hR
        (siteChangeStructure X π) _ _ _
        (isPullback_adicFibre R I B hR (siteChangeSpace B X π) (siteChangeStructure X π) n)
        (IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective)))

/-- **Flatness on the tower gives flatness on the adic fibres of `X'`.** -/
theorem isFlatOver_adicFibre (N : Modules.{u, u} B S hS X.1 X.2) (hN : N.IsQuasicoherentOnSite)
    (hflat : IsFlatOver B S hS (Z n).2 (p n).hom
      ((modulePullback B S hS (i n)).obj N)) :
    IsFlatOver B (Spec (.of R)) hR
      (adicFibreSpaceOf R I B hR (siteChangeSpace B X π) (siteChangeStructure X π) n).2
      (adicFibreProjection R I B hR (siteChangeSpace B X π) (siteChangeStructure X π) n).hom
      ((modulePullback B (Spec (.of R)) hR
        (adicFibreInclusion R I B hR (siteChangeSpace B X π) (siteChangeStructure X π) n)).obj
          ((siteChangeModules B X π).obj N)) := by
  let ι' := adicFibreInclusion R I B hR (siteChangeSpace B X π) (siteChangeStructure X π) n
  let e := siteChangeIso B X π
  let j := 𝒯.adicFibreIso n
  let M := (modulePullback B S hS (i n)).obj N
  have hMq : M.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ N hN
  have : ((modulePullback B S hS j.hom).obj M).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ M hMq
  refine (isFlatOver_relocalizeModulesEquivalence_functor_iff B hR hS h
    (adicFibreSpaceOf R I B hR (siteChangeSpace B X π) (siteChangeStructure X π) n).2
    (schemeSpace (adicThickeningObject R I B hR (contains_adicThickening R I B hR) n)).2
    (adicFibreProjection R I B hR (siteChangeSpace B X π) (siteChangeStructure X π) n).hom
    _).1 ?_
  -- the module, read on `Z_n`
  let c : relocalizeSpace B hR hS h
      (schemeSpace (adicThickeningObject R I B hR (contains_adicThickening R I B hR) n)) ≅
        schemeSpace (T n) := ObjectProperty.isoMk _ (𝒯.thickeningPresheafIso n)
  let q : relocalizeSpace B hR hS h
      (adicFibreSpaceOf R I B hR (siteChangeSpace B X π) (siteChangeStructure X π) n) ⟶
      relocalizeSpace B hR hS h
        (schemeSpace (adicThickeningObject R I B hR (contains_adicThickening R I B hR) n)) :=
    relocalizeHom B hR hS h
      (adicFibreProjection R I B hR (siteChangeSpace B X π) (siteChangeStructure X π) n)
  have hjq : j.hom ≫ (p n ≫ c.inv) = q ≫ 𝟙 _ := by
    rw [Category.comp_id, ← Category.assoc, Iso.comp_inv_eq]
    exact ObjectProperty.hom_ext _ (𝒯.adicFibreIso_hom_p n)
  have hpb : IsPullback j.hom q (p n ≫ c.inv) (𝟙 _) := IsPullback.of_horiz_isIso ⟨hjq⟩
  have h1 : IsFlatOver B S hS (Z n).2 (p n ≫ c.inv).hom M :=
    isFlatOver_comp_of_isFlat B S hS (p n) c.inv M hflat
      (isFlat_of_isIso _ (relocalizeSpace B hR hS h
        (schemeSpace (adicThickeningObject R I B hR (contains_adicThickening R I B hR) n))).2)
  have h2 := isFlatOver_modulePullback B S hS hpb M h1
  -- identify the module
  refine IsFlatOver.of_iso B S hS _ ?_ h2
  refine ((modulePullbackCompIso B S hS j.hom (i n)).app N).trans ?_
  refine (eqToIso (congrArg (fun k => (modulePullback B S hS k).obj N)
    (𝒯.adicFibreIso_hom_i n))).trans ?_
  refine ((modulePullbackCompIso B S hS (relocalizeHom B hR hS h ι') e.hom).app
    N).symm.trans ?_
  refine ((modulePullback B S hS (relocalizeHom B hR hS h ι')).mapIso
    (((modulePushforwardInvIsoModulePullback B S hS e).app N).symm.trans
      ((relocalizeModulesEquivalence B hR hS h (siteChangeSpace B X π).1
        (siteChangeSpace B X π).2).counitIso.app
          _).symm)).trans ?_
  exact ((relocalizeModulePullbackIso B hR hS h ι'
    (relativelyRepresentable_adicFibreInclusion n)).app _).symm

/-- **Flatness over `Spec R` from flatness on a tower of thickenings** (Stacks 08VP, 0CZG): a
coherent `𝒪_X`-module with support proper over `Spec R`, for `R` Noetherian local and `I ⊆ 𝔪`,
is flat over `Spec R` as soon as its restrictions to the `Z_n` are flat over the `T_n`. -/
theorem isFlatOver_of_isFlatOver_restrictions [IsNoetherianRing R] [IsLocalRing R]
    (hI : I ≤ IsLocalRing.maximalIdeal R)
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hπ : IsLocallyOfFiniteType B S hS π.hom) (N : Modules.{u, u} B S hS X.1 X.2)
    (hN : IsCoherent B S hS X.1 X.2 N)
    (hNp : HasProperSupport B S hS X.2 (schemeSpace (Over.mk h)).2 π.hom hπ
      ((SheafOfModules.toSheaf _).obj N))
    (hflat : ∀ n, IsFlatOver B S hS (Z n).2 (p n).hom
      ((modulePullback B S hS (i n)).obj N)) :
    IsFlatOver B S hS X.2 π.hom N := by
  have hft : SheafOfModules.IsFiniteTypeOnSite N :=
    let := hN.toIsCoherentOnSite
    isFiniteTypeOnSite_of_isCoherentOnSite B S hS X N
  have hf' := (isLocallyOfFiniteType_siteChangeStructure_iff X π).2 hπ
  have hfp : IsLocallyOfFinitePresentation B (Spec (.of R)) hR (siteChangeStructure X π).hom :=
    isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B (Spec (.of R)) hR
      (siteChangeSpace B X π).2 (schemeSpace (baseObject R B hR)).2 _
      (hasEtaleLocalProperty_isLocallyNoetherian_baseObject R B hR) hf'
  have : IsCoherent B (Spec (.of R)) hR (siteChangeSpace B X π).1 (siteChangeSpace B X π).2
      ((siteChangeModules B X π).obj N) := (isCoherent_siteChangeModules_iff X π N).2 hN
  refine isFlatOver_of_isFlatOver_siteChangeModules X π N hN.toIsQuasicoherentOnSite ?_
  exact isFlatOver_of_isFlatOver_adicFibres I hI (siteChangeSpace B X π) (siteChangeStructure X π)
    hfp _ (fun n => 𝒯.isFlatOver_adicFibre n N hN.toIsQuasicoherentOnSite (hflat n))
    ((hasProperSupport_siteChangeModules_iff X π hπ N hN.toIsQuasicoherentOnSite hft).2 hNp)

end SiteChangeTower

end AlgebraicGeometry.Space

end
