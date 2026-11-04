module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingNoetherianAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction

/-!
# Affineness from the vanishing of twisted first cohomology

Let `X` be a Noetherian algebraic space over a scheme `S` and let `T_a` (`a ∈ ℕ`) be
autoequivalences of the category of `𝒪_X`-modules, with natural transformations
`μ_a : 𝟭 ⟶ T_a`.  The model is `T_a = - ⊗ 𝓛^{⊗ ad}` and `μ_a` multiplication by `s^a` for a
global section `s` of an invertible module `𝓛^{⊗ d}`, as in the proof of Stacks 0D2W.

If every coherent `𝓚` has some `a` with `H¹(X, T_a 𝓚) = 0`, then global sections are right exact
on quasi-coherent modules *up to twisting*: for an epimorphism `g : 𝓟 → 𝓠` of quasi-coherent
modules and a global section `t` of `𝓠`, some `μ_a(t)` lifts to a global section of `T_a 𝓟`
(`AlgebraicGeometry.Space.exists_comp_map_eq_comp_app_of_epi`).  The argument is that of
Stacks 0D2V: the section `t` lifts over an affine surjective chart, the lift lies in a coherent
submodule `𝓖 ⊆ 𝓟` (Stacks 07UV), and the corestriction `q : 𝓖 → 𝓙` of `g` to the image has a
coherent kernel `𝓚`; twisting the short exact sequence `0 → 𝓚 → 𝓖 → 𝓙 → 0` by `T_a` keeps it
exact, and `H¹(T_a 𝓚) = 0` lifts `μ_a(t)`.

If moreover `j : U ⟶ X` is an affine étale morphism along which every `μ_a` becomes invertible,
then `U` is affine (`AlgebraicGeometry.Space.isAffineSpace_of_isAffineHom_of_twist`): this is
the claim in the proof of Stacks 0D2W.  Given an epimorphism `g : 𝓐 → 𝓝` of quasi-coherent
`𝒪_U`-modules and a section `t` of `𝓝`, apply the above to `j_* g`, which is an epimorphism of
quasi-coherent modules because `j` is affine (Stacks 07U8, 073H), and to the adjoint of `t`; pull
the lift back to `U`, divide by the invertible `j^* μ_a` and apply the counit.  Serre's criterion
(Stacks 07V6) concludes.

## Main results

* `AlgebraicGeometry.Space.exists_comp_map_eq_comp_app_of_epi`: twisted right exactness of
  global sections on quasi-coherent modules.
* `AlgebraicGeometry.Space.isAffineSpace_of_isAffineHom_of_twist`: an affine étale `U ⟶ X` over
  which the twists become trivial is affine.

## Implementation notes

The source writes `H¹(U, 𝓕) = H¹(X, j_* 𝓕)` and commutes cohomology with the filtered colimit
`j_* 𝓕 = colim 𝓕_i` of coherent modules (Stacks 069U, 073E) to show that `H¹(U, 𝓕) = 0`.  Here
the colimit is replaced by the direct argument on sections above, which is all that Serre's
criterion consumes.

## References

* [Stacks Project, Tag 0D2W](https://stacks.math.columbia.edu/tag/0D2W)
* [Stacks Project, Tag 0D2V](https://stacks.math.columbia.edu/tag/0D2V)
* [Stacks Project, Tag 07V6](https://stacks.math.columbia.edu/tag/07V6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] HasDerivedCategory.standard

/-- **An exact twist with vanishing first cohomology of the kernel is surjective on sections**:
for an autoequivalence `T` of the `𝒪_X`-modules and a short exact sequence
`0 ⟶ 𝓚 ⟶ 𝓟 ⟶ 𝓠 ⟶ 0` with `H¹(X, T 𝓚) = 0`, the map `Γ(T 𝓟) ⟶ Γ(T 𝓠)` is surjective. -/
theorem surjective_sectionsMap_map_of_isZero_rightDerived_one {X : AlgebraicSpaces B S hS}
    (T : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS X.1 X.2) [T.IsEquivalence]
    {E : ShortComplex (Modules.{u, u} B S hS X.1 X.2)} (hE : E.ShortExact)
    (h : have := enoughInjectives_modules B S hS X.1 X.2
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj (T.obj E.X₁))) :
    Function.Surjective (SheafOfModules.sectionsMap (T.map E.g)) := by
  have := enoughInjectives_modules B S hS X.1 X.2
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS X.1 X.2
  exact (ModuleCat.epi_iff_surjective _).1
    (Stacks.Cohomology.SectionsEpi.epi_map_g_of_isZero_rightDerived_one _ (hE.map_of_exact T) h)

/-- **Global sections are right exact on quasi-coherent modules up to twisting.**  Let `X` be a
Noetherian algebraic space, `T_a` autoequivalences of its modules and `μ_a : 𝟭 ⟶ T_a`.  If every
coherent `𝓚` has some `a` with `H¹(X, T_a 𝓚) = 0`, then for every epimorphism `g : 𝓟 ⟶ 𝓠` of
quasi-coherent modules and every `t : 𝒪_X ⟶ 𝓠` there are `a` and `σ : 𝒪_X ⟶ T_a 𝓟` with
`σ ≫ T_a g = t ≫ μ_a`. -/
theorem exists_comp_map_eq_comp_app_of_epi {X : AlgebraicSpaces B S hS}
    (hN : IsNoetherian B S hS hZ X.1)
    (T : ℕ → Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS X.1 X.2)
    [∀ a, (T a).IsEquivalence] (μ : ∀ a, 𝟭 _ ⟶ T a)
    (h : have := enoughInjectives_modules B S hS X.1 X.2
      ∀ K : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 K →
        ∃ a, IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj ((T a).obj K)))
    {P Q : Modules.{u, u} B S hS X.1 X.2} (g : P ⟶ Q) (hg : Epi g)
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite)
    (t : SheafOfModules.unit _ ⟶ Q) :
    ∃ (a : ℕ) (σ : SheafOfModules.unit _ ⟶ (T a).obj P), σ ≫ (T a).map g = t ≫ (μ a).app Q := by
  classical
  have := enoughInjectives_modules B S hS X.1 X.2
  have := preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS X.1 X.2
  have := isClosedUnderKernels_quasicoherentSheaves_smallEtale B S hS X.1 X.2
  have := isClosedUnderCokernels_quasicoherentSheaves B S hS X.1 X.2
  have hXN : Fact (HasEtaleLocalProperty B S hS X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hN.2.2⟩
  -- a surjective affine chart, and a lift over it
  obtain ⟨U, hU, hUsurj, -⟩ := exists_surjective_isNoetherianAffineChart B S hS hZ X hN
  have hsurj : IsSurjective B S hS U.1.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 U.1.left U.1.hom).1 hUsurj
  have hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj U)) := hU.1
  set ts := Q.unitHomEquiv t with hts
  obtain ⟨m, hm⟩ := surjective_val_app_of_epi_of_isQuasicoherentOnSite g hg hP hQ U hUaff
    (ts.val (op U))
  -- a coherent submodule of `P` through the lift
  obtain ⟨G, hG, hmG⟩ := exists_isCoherent_mem_submodule_of_chart B S hS hZ X hN U hUaff hsurj
    P hP U (have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj U)) := hUaff
     inferInstance) m
  set ψ := G.ι ≫ g with hψ
  set J := SheafOfModules.Submodule.ker (cokernel.π ψ) with hJ
  -- `t` is a section of the image of `ψ`
  have ht0 : SheafOfModules.sectionsMap (cokernel.π ψ) ts = 0 := by
    refine sections_eq_zero_of_val_eq_zero B S hS U hsurj _ ?_
    show (cokernel.π ψ).val.app (op U) (ts.val (op U)) = 0
    rw [← hm]
    show ((G.ι ≫ g) ≫ cokernel.π ψ).val.app (op U) ⟨m, hmG⟩ = 0
    rw [cokernel.condition]
    rfl
  have ht0' : ∀ W, (cokernel.π ψ).val.app W (ts.val W) = 0 := fun W =>
    congrArg (fun s => s.val W) ht0
  let t' : J.toSheafOfModules.sections :=
    PresheafOfModules.sectionsMk (fun W => ⟨ts.val W, ht0' W⟩)
      (fun _ _ f => Subtype.ext (ts.property f))
  have ht' : J.toSheafOfModules.unitHomEquiv.symm t' ≫ J.ι = t := by
    apply Q.unitHomEquiv.injective
    rw [SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply]
    rfl
  -- the corestriction of `ψ` to its image is an epimorphism with coherent kernel
  have hψJ : ∀ (W : (smallEtaleRingedSite B S hS X.1 X.2).Cᵒᵖ) (x : G.toSheafOfModules.val.obj W),
      ψ.val.app W x ∈ J.obj W := fun W x => by
    show (ψ ≫ cokernel.π ψ).val.app W x = 0
    rw [cokernel.condition]
    rfl
  let q : G.toSheafOfModules ⟶ J.toSheafOfModules := J.factorThru ψ hψJ
  have hq : q = Abelian.factorThruImage (C := Modules.{u, u} B S hS X.1 X.2) ψ ≫
      (SheafOfModules.Submodule.kerIsoKernel _).inv := by
    rw [← cancel_mono J.ι]
    simp only [q, SheafOfModules.Submodule.factorThru_ι, Category.assoc]
    rw [← SheafOfModules.Submodule.kerIsoKernel_hom_comp_ι, Iso.inv_hom_id_assoc]
    exact (Abelian.image.fac (C := Modules.{u, u} B S hS X.1 X.2) ψ).symm
  have hqepi : Epi q := by
    have h1 : Epi (Abelian.factorThruImage (C := Modules.{u, u} B S hS X.1 X.2) ψ) :=
      Abelian.instEpiFactorThruImage (C := Modules.{u, u} B S hS X.1 X.2) ψ
    have h2 : Epi (SheafOfModules.Submodule.kerIsoKernel (cokernel.π ψ)).inv :=
      @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)
    rw [hq]
    exact @epi_comp _ _ _ _ _ _ h1 _ h2
  have hGq : G.toSheafOfModules.IsQuasicoherentOnSite := hG.toIsQuasicoherentOnSite
  have hJq : J.toSheafOfModules.IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso (SheafOfModules.Submodule.kerIsoKernel _).symm
      ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_kernel _ hQ
        ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_cokernel ψ hGq hQ))
  have hJc : IsCoherent B S hS X.1 X.2 J.toSheafOfModules :=
    isCoherent_of_epi_of_isQuasicoherentOnSite B S hS X.1 X.2 q hJq hG
  have hK : IsCoherent B S hS X.1 X.2 (kernel q) := isCoherent_kernel B S hS X.1 X.2 hG hJc q
  have hSE := have := hqepi; ShortComplex.shortExact_mk_kernel_ι q
  -- the twist that kills the first cohomology of the kernel
  obtain ⟨a, ha⟩ := h _ hK
  have hqsurj := surjective_sectionsMap_map_of_isZero_rightDerived_one B S hS (T a) hSE ha
  obtain ⟨σG, hσG⟩ := hqsurj (((T a).obj J.toSheafOfModules).unitHomEquiv
    (J.toSheafOfModules.unitHomEquiv.symm t' ≫ (μ a).app J.toSheafOfModules))
  refine ⟨a, ((T a).obj G.toSheafOfModules).unitHomEquiv.symm σG ≫ (T a).map G.ι, ?_⟩
  have hfac : G.ι ≫ g = q ≫ J.ι := (SheafOfModules.Submodule.factorThru_ι J ψ hψJ).symm
  have hσ : ((T a).obj G.toSheafOfModules).unitHomEquiv.symm σG ≫ (T a).map q =
      J.toSheafOfModules.unitHomEquiv.symm t' ≫ (μ a).app J.toSheafOfModules := by
    apply ((T a).obj J.toSheafOfModules).unitHomEquiv.injective
    rw [SheafOfModules.unitHomEquiv_comp_apply, Equiv.apply_symm_apply, hσG]
  calc (((T a).obj G.toSheafOfModules).unitHomEquiv.symm σG ≫ (T a).map G.ι) ≫ (T a).map g
      = (((T a).obj G.toSheafOfModules).unitHomEquiv.symm σG ≫ (T a).map q) ≫
          (T a).map J.ι := by
        rw [Category.assoc, Category.assoc, ← (T a).map_comp, ← (T a).map_comp, hfac]
    _ = J.toSheafOfModules.unitHomEquiv.symm t' ≫ ((μ a).app J.toSheafOfModules ≫
          (T a).map J.ι) := by rw [hσ, Category.assoc]
    _ = t ≫ (μ a).app Q := by
        rw [← (μ a).naturality J.ι, ← Category.assoc, Functor.id_map, ht']

/-- **An affine morphism over which the twists become trivial has affine source.**  Let `X` be a
Noetherian algebraic space, `T_a` autoequivalences of its modules and `μ_a : 𝟭 ⟶ T_a` such that
every coherent `𝓚` has some `a` with `H¹(X, T_a 𝓚) = 0`.  If `j : U ⟶ X` is affine, `U` is
quasi-compact and quasi-separated, and every `j^* μ_a` is an isomorphism, then `U` is an affine
scheme.

This is Serre's criterion (`AlgebraicGeometry.Space.isAffineSpace_of_surjective_sectionsMap`)
on `U`, from `AlgebraicGeometry.Space.exists_comp_map_eq_comp_app_of_epi` applied to `j_* g`;
see the module docstring. -/
theorem isAffineSpace_of_isAffineHom_of_twist {X U : AlgebraicSpaces B S hS}
    (hN : IsNoetherian B S hS hZ X.1) (j : U ⟶ X) (hj : IsAffineHom B S hS j.hom)
    (hqc : IsQuasiCompactSpace B S hS U.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ U.1)
    (T : ℕ → Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS X.1 X.2)
    [∀ a, (T a).IsEquivalence] (μ : ∀ a, 𝟭 _ ⟶ T a)
    (h : have := enoughInjectives_modules B S hS X.1 X.2
      ∀ K : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 K →
        ∃ a, IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj ((T a).obj K)))
    (hμ : ∀ a (F : Modules.{u, u} B S hS X.1 X.2),
      IsIso ((modulePullback B S hS j).map ((μ a).app F))) :
    IsAffineSpace B S hS U.1 := by
  refine isAffineSpace_of_surjective_sectionsMap B S hS hZ (fun A N g hg hA hN' => ?_) hqc hqs
  intro t
  have := enoughInjectives_modules B S hS U.1 U.2
  have := isClosedUnderKernels_quasicoherentSheaves_smallEtale B S hS U.1 U.2
  let adj := modulePullbackAdjunction B S hS j
  let F := modulePullback B S hS j
  let G := modulePushforward B S hS j
  have : F.Additive := adj.left_adjoint_additive
  have : G.Additive := adj.right_adjoint_additive
  have : PreservesLimits G := adj.rightAdjoint_preservesLimits
  let e : (SheafOfModules.unit _ : Modules.{u, u} B S hS U.1 U.2) ≅
      F.obj (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2) :=
    Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
      (smallEtaleRingedToposModulesHom B S hS j)
  set tb := N.unitHomEquiv.symm t with htb
  let t' : (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2) ⟶ G.obj N :=
    adj.homEquiv _ _ (e.inv ≫ tb)
  -- the direct image of `g` is an epimorphism
  have hker : (kernel g).IsQuasicoherentOnSite :=
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_kernel g hA hN'
  have hSE := ShortComplex.shortExact_mk_kernel_ι g
  have hz := isZero_rightDerived_modulePushforward_isAffineHom B S hS j hj _
    hker 1 one_pos
  have h2 := Stacks.Cohomology.SectionsEpi.epi_map_g_of_isZero_rightDerived_one G hSE
  have hGg : Epi (G.map g) := by
    exact h2 hz
  obtain ⟨a, σ, hσ⟩ := exists_comp_map_eq_comp_app_of_epi B S hS hZ hN T μ h (G.map g) hGg
    (isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional _ _ _ j hj _ hA)
    (isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional _ _ _ j hj _ hN') t'
  have hP := hμ a (G.obj A)
  have hQ := hμ a (G.obj N)
  let lift : SheafOfModules.unit _ ⟶ A :=
    e.hom ≫ F.map σ ≫ inv (F.map ((μ a).app (G.obj A))) ≫ adj.counit.app A
  have n1 : adj.counit.app A ≫ g = F.map (G.map g) ≫ adj.counit.app N :=
    (adj.counit.naturality g).symm
  have n2 : inv (F.map ((μ a).app (G.obj A))) ≫ F.map (G.map g) =
      F.map ((T a).map (G.map g)) ≫ inv (F.map ((μ a).app (G.obj N))) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← F.map_comp, ← (μ a).naturality, Functor.id_map,
      F.map_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have n3 : F.map σ ≫ F.map ((T a).map (G.map g)) = F.map t' ≫ F.map ((μ a).app (G.obj N)) := by
    rw [← F.map_comp, hσ, F.map_comp]
  have n4 : F.map t' ≫ adj.counit.app N = e.inv ≫ tb := by
    exact (adj.homEquiv_counit (g := t')).symm.trans ((adj.homEquiv _ _).symm_apply_apply _)
  have key : lift ≫ g = tb := by
    calc lift ≫ g = e.hom ≫ F.map σ ≫ inv (F.map ((μ a).app (G.obj A))) ≫
          (adj.counit.app A ≫ g) := by simp only [lift, Category.assoc]
      _ = e.hom ≫ ((F.map σ ≫ F.map ((T a).map (G.map g))) ≫
          inv (F.map ((μ a).app (G.obj N)))) ≫ adj.counit.app N := by
          rw [n1, ← Category.assoc (inv _), n2]; simp only [Category.assoc]
      _ = e.hom ≫ (F.map t' ≫ adj.counit.app N) := by
          rw [n3]; simp only [Category.assoc, IsIso.hom_inv_id_assoc]
      _ = tb := by rw [n4, Iso.hom_inv_id_assoc]
  refine ⟨A.unitHomEquiv lift, ?_⟩
  rw [← SheafOfModules.unitHomEquiv_comp_apply, key, htb, Equiv.apply_symm_apply]

end AlgebraicGeometry.Space

end
