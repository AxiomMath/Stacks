module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.PairBaseChange07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.WholeSpaceSectionsLevelQuotient
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AdicLevelCone07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechPullbackOpen07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleUnitMono07QA
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenSectionsMoore07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.PerOpenData07Q9

/-!
# The Čech sections over `f⁻¹(W)` as the Moore complex of the base change of `M(•)`

Fix a global crystalline situation `(p, (S, I, γ), X)`, affine opens `V ⊆ S` and `W ⊆ X` with `W`
mapping into `V`, a morphism `f : X' ⟶ X` with `f⁻¹(W)` affine, a surjective presentation `g₂` of
`Γ(f⁻¹(W))` over `Γ(V)` with a morphism `r` from the tautological presentation of `Γ(W)`, and a
crystal in quasi-coherent `𝒪_{X/S}`-modules `ℱ`.  Let `T'` and `T` be the Čech systems of `W` and
of `f⁻¹(W)` (`openSystem07Q9`), `τ n e : f(T(n)_e) ⟶ T'(n)_{e + N'}` the morphism of systems over
`f` (`openCechSystemHom07Q9`), `M(•)` the cosimplicial module of the restriction of `ℱ` to
`Cris(W/S|_V)` (`openCosimplicialModule07Q9`) and `G : D(•) ⟶ D'(•)` a morphism of cosimplicial
divided power algebras whose completion is the map of envelopes of `r`.

The local step of [Stacks, Tag 07Q9] identifies `ℱ' = f_cris^*ℱ` on the levels of `T` with the
completed base change `M'(n) = (D'(n) ⊗_{D(n)} M(n))^∧` of `M(n)`.  On a single level this is the
identification `ℱ'_{T(n)_e} = τ^* ℱ_{T'(n)_{e + N'}}` of `bijective_crisInverseImageBaseChange`,
read through the identifications of the section rings of the levels with the finite levels
`D(n)/(p)^{N + e + N'}` and `D'(n)/(p)^{N' + e}` and of the sections of `ℱ` over `T'(n)_{e + N'}`
with `M(n)/(p)^{N + e + N'}`: the map

`D'(n) ⊗_{D(n)} M(n) → ℱ'(T(n)_e)`,  `d ⊗ m ↦ d · τ^* m_{e + N'}`

induces a bijection `(D'(n) ⊗_{D(n)} M(n))/(p)^{N' + e} ≅ ℱ'(T(n)_e)`.  Passing to the limit over
`e` (`AdicLevelCone07Q9`) identifies the complex of Čech sections of `ℱ'` over `T` with the Moore
complex of `M'(•)`, and under these identifications the Čech pullback of the module unit
`ℱ ⟶ f_{cris, *}f_cris^*ℱ` is the Moore map of `m ↦ 1 ⊗ m`.

## Main definitions

* `CosimplicialCompletedModule.pullbackCarrierMapSmall07Q9` — the morphism of cosimplicial abelian
  groups `M(•) ⟶ M'(•)`, `m ↦ 1 ⊗ m`.
* `openLevelScalars07Q9` — the scalars `D(n) → Γ(T(n)_e)` of the levels of a Čech system of an
  affine open.
* `sourceLevelMap07Q9` — the map `D'(n) ⊗_{D(n)} M(n) → ℱ'(T(n)_e)`.
* `sourceSectionsMooreIso07Q9` — **the Čech sections of `ℱ'` over `T` are the Moore complex of
  `M'(•)`**.

## Main results

* `crisDirectImageEval_crisModuleUnit07Q9` — the module unit followed by the evaluation of
  `f_{cris, *}` at `τ` is `crisInverseImageRestrict`.
* `tauRing_openLevelScalars07Q9` — the ring map of `τ n e` on the scalars of the levels is the map
  of completed envelopes.
* `bijective_sourceLevelMap07Q9` — the level maps are bijective.
* `sectionsMap_sourceSectionsMooreIso07Q9` — **the square**: the Čech pullback of the module unit
  is, through the two Moore identifications, the Moore map of `m ↦ 1 ⊗ m`.

## Implementation notes

The morphism `G` enters only through `hG`: any morphism of cosimplicial divided power algebras
whose completion is `completedEnvelopeMap07Q9` will do, for instance the morphism of envelopes of
the renaming of variables of a chain normal form, for which `hG` holds by definition.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial
open scoped TensorProduct

noncomputable section

namespace Crystalline.CosimplicialCompletedModule

variable {A : Type u} [CommRing A] {E E' : CosimplicialDPAlgebra.{u, u} A} {p : ℕ}
  (V : CosimplicialCompletedModule.{u, u, u} E p) (g : E.Hom E')

/-- **The morphism of cosimplicial abelian groups `M(•) ⟶ M'(•)`, `m ↦ 1 ⊗ m`**, into the base
change of a cosimplicial module along a morphism of cosimplicial divided power algebras, in the
universe of the modules. -/
def pullbackCarrierMapSmall07Q9 :
    V.carrierCosimplicialSmall ⟶ (V.pullback07Q9 g).carrierCosimplicialSmall where
  app n := AddCommGrpCat.ofHom (V.pullbackApp07Q9 g n.len).toAddMonoidHom
  naturality _ _ φ := AddCommGrpCat.ext fun x ↦ V.pullbackApp07Q9_naturality g φ x

/-- The morphism `M(•) ⟶ M'(•)` on elements. -/
theorem pullbackCarrierMapSmall07Q9_app_apply (n : SimplexCategory)
    (x : V.carrierCosimplicialSmall.obj n) :
    ConcreteCategory.hom ((V.pullbackCarrierMapSmall07Q9 g).app n) x =
      V.pullbackApp07Q9 g n.len x :=
  rfl

end Crystalline.CosimplicialCompletedModule

namespace Crystalline.GlobalCrystallineSituation.SmallSite

section UnitSections

variable {S S' : GlobalCrystallineSituation.{u}} (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)
  (F : SheafOfModules.{u} (structureSheaf S'))

/-- **The module unit `ℱ ⟶ f_{cris, *}f_cris^*ℱ` read on sections**: at an object `A` of
`Cris(X'/S')` followed by the evaluation of `f_{cris, *}` at `τ : f(A') ⟶ A`, it sends (the
universe lift of) a section `s` of `ℱ` over `A` to the restriction `τ^* s` of
`crisInverseImageRestrict`. -/
theorem crisDirectImageEval_crisModuleUnit07Q9 {A : CrystallineThickening S'}
    {A' : CrystallineThickening S}
    (τ : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A') ⟶
      (CrystallineThickening.ι S').obj A) (s : F.val.obj (op A)) :
    ConcreteCategory.hom ((crisModuleUnit S S' fS fX hf ((moduleULift S').obj F)).hom.app (op A) ≫
        crisDirectImageEval S S' fS fX hf τ ((toAbelianSheaf S).obj
          ((crisModuleInverseImage fS fX hf).obj ((moduleULift S').obj F))))
      (show ((toAbelianSheaf S').obj ((moduleULift S').obj F)).obj.obj (op A) from ULift.up s) =
      crisInverseImageRestrict fS fX hf F τ s := by
  rw [crisModuleUnit_app_comp_crisDirectImageEval]
  rfl

end UnitSections


/-! ### The scalars of the levels of the Čech system of an affine open -/

section Levels

variable (S : GlobalCrystallineSituation.{u}) {V : S.S.scheme.Opens} {W : S.X.Opens}
  (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hVW : W ≤ sourceToBase S ⁻¹ᵁ V) {ι : Type u}
  (g : MvPolynomial ι (openAffineSituation07Q9 S hW hVW).A
    →ₐ[(openAffineSituation07Q9 S hW hVW).A] (openAffineSituation07Q9 S hW hVW).C)
  (hg : Function.Surjective g)

/-- **The section ring of the level `(n, e)` of the Čech system of `W` is `D(n)/(p)^{N + e}`**,
`D(n)` the `p`-adically completed divided power envelope of the `(n + 1)`-fold tensor power of
the presentation `g`. -/
def openLevelRingEquiv07Q9 (n e : ℕ) :
    (pAdicCompletedTensorPowerEnvelope (openAffineSituation07Q9 S hW hVW) g hg n ⧸
        DividedPowers.pAdicIdeal
            (A := pAdicCompletedTensorPowerEnvelope (openAffineSituation07Q9 S hW hVW) g hg n)
            (openAffineSituation07Q9 S hW hVW).p ^
          (uniformLevel (openAffineSituation07Q9 S hW hVW) + e)) ≃+*
      ((structureSheaf (restrict S V W hVW)).obj.obj
        (op (((openLocalSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).obj e)) : Type u) :=
  haveI := isAffine_restrictX07Q9 S hW hVW
  haveI := isAffine_restrictS07Q9 S hV hVW
  (Ideal.quotientEquiv _ (DividedPowers.pAdicIdeal
      (A := (tensorPowerEnvelopeThickening _ g hg n).thickening.ring)
      (openAffineSituation07Q9 S hW hVW).p ^
        (uniformLevel (openAffineSituation07Q9 S hW hVW) + e))
      (tensorPowerEnvelopeThickeningRingEquiv _ g hg n).symm
      (by rw [Ideal.map_pow, pAdicIdeal_map_ringHom])).trans
    (wholeSiteInverseSectionsRingEquiv (isNilpotent_prime_openSituation07Q9 S hW hVW)
      (((affineLevelSystem _ g hg).obj ⦋n⦌).obj (op e))).symm

/-- **The scalars of the level `(n, e)`**: the reduction `D(n) → D(n)/(p)^{N + e}` followed by
`openLevelRingEquiv07Q9`. -/
def openLevelScalars07Q9 (n e : ℕ) :
    pAdicCompletedTensorPowerEnvelope (openAffineSituation07Q9 S hW hVW) g hg n →+*
      ((structureSheaf (restrict S V W hVW)).obj.obj
        (op (((openLocalSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).obj e)) : Type u) :=
  (openLevelRingEquiv07Q9 S hV hW hVW g hg n e).toRingHom.comp (Ideal.Quotient.mk _)

/-- The scalars of a level are surjective. -/
theorem openLevelScalars07Q9_surjective (n e : ℕ) :
    Function.Surjective (openLevelScalars07Q9 S hV hW hVW g hg n e) :=
  (openLevelRingEquiv07Q9 S hV hW hVW g hg n e).surjective.comp Ideal.Quotient.mk_surjective

/-- `openLevelRingEquiv07Q9` read through the identification of the section ring with the finite
level. -/
theorem wholeSiteInverseSectionsRingEquiv_openLevelScalars07Q9 (n e : ℕ)
    (a : pAdicCompletedTensorPowerEnvelope (openAffineSituation07Q9 S hW hVW) g hg n) :
    haveI := isAffine_restrictX07Q9 S hW hVW
    haveI := isAffine_restrictS07Q9 S hV hVW
    wholeSiteInverseSectionsRingEquiv (isNilpotent_prime_openSituation07Q9 S hW hVW)
        (((affineLevelSystem _ g hg).obj ⦋n⦌).obj (op e))
        (openLevelScalars07Q9 S hV hW hVW g hg n e a) =
      Ideal.Quotient.mk (DividedPowers.pAdicIdeal
          (A := (tensorPowerEnvelopeThickening _ g hg n).thickening.ring)
          (openAffineSituation07Q9 S hW hVW).p ^
            (uniformLevel (openAffineSituation07Q9 S hW hVW) + e))
        ((tensorPowerEnvelopeThickeningRingEquiv _ g hg n).symm a) :=
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  RingEquiv.apply_symm_apply _ _

/-- **The scalars of the levels are compatible with the tower maps.** -/
theorem openLevelScalars07Q9_tower (n : ℕ) {e e' : ℕ} (h : e ≤ e')
    (a : pAdicCompletedTensorPowerEnvelope (openAffineSituation07Q9 S hW hVW) g hg n) :
    ((structureSheaf (restrict S V W hVW)).obj.map
        (((openLocalSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).map (homOfLE h)).op).hom
        (openLevelScalars07Q9 S hV hW hVW g hg n e' a) =
      openLevelScalars07Q9 S hV hW hVW g hg n e a := by
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  apply (wholeSiteInverseSectionsRingEquiv (isNilpotent_prime_openSituation07Q9 S hW hVW)
    (((affineLevelSystem _ g hg).obj ⦋n⦌).obj (op e))).injective
  refine (wholeSiteInverseSectionsRingEquiv_naturality _
    (((affineLevelSystem _ g hg).obj ⦋n⦌).map ((homOfLE h).op : (op e' : ℕᵒᵖ) ⟶ op e)) _).trans
      ?_
  rw [wholeSiteInverseSectionsRingEquiv_openLevelScalars07Q9,
    wholeSiteInverseSectionsRingEquiv_openLevelScalars07Q9]
  rfl

/-- **The scalars of the levels are compatible with the cosimplicial structure maps.** -/
theorem openLevelScalars07Q9_simplicial {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) (e : ℕ)
    (a : pAdicCompletedTensorPowerEnvelope (openAffineSituation07Q9 S hW hVW) g hg n) :
    ((structureSheaf (restrict S V W hVW)).obj.map
        (((openLocalSystem07Q9 S hV hW hVW g hg).map φ.op).app e).op).hom
        (openLevelScalars07Q9 S hV hW hVW g hg n e a) =
      openLevelScalars07Q9 S hV hW hVW g hg m e
        ((cosimplicialEnvelopeRing _ g hg).map φ a) := by
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  apply (wholeSiteInverseSectionsRingEquiv (isNilpotent_prime_openSituation07Q9 S hW hVW)
    (((affineLevelSystem _ g hg).obj ⦋m⦌).obj (op e))).injective
  refine (wholeSiteInverseSectionsRingEquiv_naturality _
    (((affineLevelSystem _ g hg).map φ).app (op e)) _).trans ?_
  refine (congrArg (fun y ↦ (((affineLevelSystem _ g hg).map φ).app (op e)).hom.hom.toRingHom y)
    (wholeSiteInverseSectionsRingEquiv_openLevelScalars07Q9 S hV hW hVW g hg n e a)).trans
    (Eq.trans ?_ (wholeSiteInverseSectionsRingEquiv_openLevelScalars07Q9 S hV hW hVW g hg m e
      _).symm)
  change Ideal.Quotient.mk _ (((envelopeCosimplicial _ g hg).map φ).hom.toRingHom
    ((tensorPowerEnvelopeThickeningRingEquiv _ g hg n).symm a)) = _
  refine congrArg (Ideal.Quotient.mk _)
    ((tensorPowerEnvelopeThickeningRingEquiv _ g hg m).injective ?_)
  rw [tensorPowerEnvelopeThickeningRingEquiv_envelopeCosimplicial_map _ g hg φ,
    RingEquiv.apply_symm_apply]
  exact (RingEquiv.apply_symm_apply _ _).symm

/-- **At the tautological presentation the scalars of the levels are those of
`levelSectionsScalars`.** -/
theorem levelSectionsScalars_eq_openLevelScalars07Q9 (n e : ℕ)
    (a : pAdicCompletedTensorPowerEnvelope (openAffineSituation07Q9 S hW hVW)
      (canonicalPresentation _) (canonicalPresentation_surjective _) n) :
    haveI := isAffine_restrictX07Q9 S hW hVW
    haveI := isAffine_restrictS07Q9 S hV hVW
    levelSectionsScalars (isNilpotent_prime_openSituation07Q9 S hW hVW) ⦋n⦌ e a =
      openLevelScalars07Q9 S hV hW hVW (canonicalPresentation _)
        (canonicalPresentation_surjective _) n e a := by
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  apply (wholeSiteInverseSectionsRingEquiv (isNilpotent_prime_openSituation07Q9 S hW hVW)
    (((affineLevelSystem _ (canonicalPresentation _) (canonicalPresentation_surjective _)).obj
      ⦋n⦌).obj (op e))).injective
  refine Eq.trans ?_ (wholeSiteInverseSectionsRingEquiv_openLevelScalars07Q9 S hV hW hVW _ _ n e
    a).symm
  apply (Ideal.quotientEquiv _ _ (wholeSpaceSystemEnvelopeRingEquiv
    (isNilpotent_prime_openSituation07Q9 S hW hVW) n)
    (wholeSpaceSystemEnvelope_pAdicIdeal_pow_map _ n _)).injective
  refine ((wholeSpaceEnvelopeRingLevelEquiv _ n e).apply_symm_apply _).trans ?_
  exact (congrArg _ (RingEquiv.apply_symm_apply _ _).symm).trans
    (Ideal.quotientEquiv_mk _ _ _ _ _).symm

end Levels

/-! ### The ring map of the morphism of Čech systems on the levels -/

section Ring

variable (S : GlobalCrystallineSituation.{u}) {V : S.S.scheme.Opens} {W : S.X.Opens}
  (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hVW : W ≤ sourceToBase S ⁻¹ᵁ V)
  {X' : Scheme.{u}} (f : X' ⟶ S.X) (hW₂ : IsAffineOpen (f ⁻¹ᵁ W)) {ι κ : Type u}
  (g : MvPolynomial ι (openAffineSituation07Q9 S hW hVW).A
    →ₐ[(openAffineSituation07Q9 S hW hVW).A] (openAffineSituation07Q9 S hW hVW).C)
  (hg : Function.Surjective g)
  (g₂ : MvPolynomial κ (openAffineSituation₂07Q9 S hVW f hW₂).A
    →ₐ[(openAffineSituation₂07Q9 S hVW f hW₂).A] (openAffineSituation₂07Q9 S hVW f hW₂).C)
  (hg₂ : Function.Surjective g₂)
  (r : MvPolynomial ι (openAffineSituation07Q9 S hW hVW).A →+*
    MvPolynomial κ (openAffineSituation₂07Q9 S hVW f hW₂).A)
  (hr : g₂.toRingHom.comp r = (restrictMap07Q9 S hVW f).appTop.hom.comp g.toRingHom)

/-- **The ring map of the morphism of Čech systems `τ n e` is the map of finite levels**
`D(n)/(p)^{N + e + N'} ⟶ D'(n)/(p)^{N' + e}`, through the identifications of the section rings
of the two levels with the finite levels. -/
theorem wholeSiteInverseSectionsRingEquiv_tauRing07Q9 (n e : ℕ)
    (x : (structureSheaf (restrict S V W hVW)).obj.obj
      (op (((openLocalSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).obj
        (e + openSystemShift07Q9 S hVW f hW₂)))) :
    haveI := isAffine_restrictX07Q9 (overSituation S f) hW₂ (preimage_le_overSituation07Q9 S hVW f)
    haveI := isAffine_restrictS07Q9 (overSituation S f) hV (preimage_le_overSituation07Q9 S hVW f)
    wholeSiteInverseSectionsRingEquiv (isNilpotent_prime_openSituation07Q9 (overSituation S f) hW₂
        (preimage_le_overSituation07Q9 S hVW f)) (levelObj₂07Q9 S hVW f hW₂ g₂ hg₂ n e)
        ((tauRing (openSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e)).hom x) =
      levelRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr n e
        (haveI := isAffine_restrictX07Q9 S hW hVW
        haveI := isAffine_restrictS07Q9 S hV hVW
        wholeSiteInverseSectionsRingEquiv (isNilpotent_prime_openSituation07Q9 S hW hVW)
          (levelObj07Q9 S hW hVW g hg n (e + openSystemShift07Q9 S hVW f hW₂)) x) := by
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  have := isAffine_restrictX07Q9 (overSituation S f) hW₂ (preimage_le_overSituation07Q9 S hVW f)
  have := isAffine_restrictS07Q9 (overSituation S f) hV (preimage_le_overSituation07Q9 S hVW f)
  set hp := isNilpotent_prime_openSituation07Q9 S hW hVW
  set hp₂ := isNilpotent_prime_openSituation07Q9 (overSituation S f) hW₂
    (preimage_le_overSituation07Q9 S hVW f)
  set c₁ := wholeSiteInverseSectionsRingEquiv hp
    (levelObj07Q9 S hW hVW g hg n (e + openSystemShift07Q9 S hVW f hW₂))
  set c₂ := wholeSiteInverseSectionsRingEquiv hp₂ (levelObj₂07Q9 S hVW f hW₂ g₂ hg₂ n e)
  have := isAffine_sourceObj07Q9 S hV hVW f hW₂ g₂ hg₂ n e
  have : IsAffine ((CrystallineThickening.ι (restrict S V W hVW)).obj
      (((openLocalSystem07Q9 S hV hW hVW g hg).obj (op ⦋n⦌)).obj
        (e + openSystemShift07Q9 S hVW f hW₂))).thickening.source :=
    @IsAffine.of_isIso _ _ _ (isIso_toX_openLocalSystem07Q9 S hV hW hVW g hg n _)
      (isAffine_restrictX07Q9 S hW hVW)
  have hb := congrArg (fun φ ↦ c₂ (φ.hom.toRingHom (c₁ x)))
    (levelBridge_localSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e)
  have h2 : c₂ ((levelAffineHom07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e).hom.toRingHom
      (c₁ x)) = levelRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr n e (c₁ x) :=
    congrArg (fun φ ↦ φ.hom.hom.toRingHom
        (levelRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr n e (c₁ x)))
      ((wholeSiteEquivLittleAffine hp₂).counitIso.inv_hom_id_app
        (levelObj₂07Q9 S hVW f hW₂ g₂ hg₂ n e))
  have h3 : (levelBridge hp _ _ (localSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n
      e)).hom.toRingHom (c₁ x) =
      (tauRing (openSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e)).hom x :=
    congrArg (fun y ↦ (wholeHomToAffine hp (localSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r
        hr n e)).hom.toRingHom y)
      (congrArg (fun φ ↦ φ.hom.hom.toRingHom x)
        ((wholeSiteEquivLittleAffine hp).counitIso.hom_inv_id_app
          (levelObj07Q9 S hW hVW g hg n (e + openSystemShift07Q9 S hVW f hW₂))))
  exact (congrArg c₂ h3).symm.trans (hb.trans h2)

/-- **The ring map of the morphism of Čech systems on the scalars of the levels**: `τ n e` carries
the scalar `a ∈ D(n)` of the level `e + N'` of the system of `W` to the scalar `g_n(a) ∈ D'(n)` of
the level `e` of the system of `f⁻¹(W)`, `g_n` the map of completed envelopes. -/
theorem tauRing_openLevelScalars07Q9 (n e : ℕ)
    (a : pAdicCompletedTensorPowerEnvelope (openAffineSituation07Q9 S hW hVW) g hg n) :
    (tauRing (openSystemMap07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e)).hom
        (openLevelScalars07Q9 S hV hW hVW g hg n (e + openSystemShift07Q9 S hVW f hW₂) a) =
      openLevelScalars07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f)
        g₂ hg₂ n e
        ((completedEnvelopeMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr n).toRingHom a) := by
  have := isAffine_restrictX07Q9 (overSituation S f) hW₂ (preimage_le_overSituation07Q9 S hVW f)
  have := isAffine_restrictS07Q9 (overSituation S f) hV (preimage_le_overSituation07Q9 S hVW f)
  apply (wholeSiteInverseSectionsRingEquiv (isNilpotent_prime_openSituation07Q9 (overSituation S f)
    hW₂ (preimage_le_overSituation07Q9 S hVW f)) (levelObj₂07Q9 S hVW f hW₂ g₂ hg₂ n e)).injective
  refine (wholeSiteInverseSectionsRingEquiv_tauRing07Q9 S hV hW hVW f hW₂ g hg g₂ hg₂ r hr n e
    _).trans ?_
  refine (congrArg (levelRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr n e)
    (wholeSiteInverseSectionsRingEquiv_openLevelScalars07Q9 S hV hW hVW g hg n _ a)).trans
    (Eq.trans ?_ (wholeSiteInverseSectionsRingEquiv_openLevelScalars07Q9 (overSituation S f) hV hW₂
      (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂ n e _).symm)
  refine congrArg (Ideal.Quotient.mk _)
    ((tensorPowerEnvelopeThickeningRingEquiv _ g₂ hg₂ n).injective ?_)
  refine (ringEquiv_envelopeRingMap07Q9 S hW hVW f hW₂ g hg g₂ hg₂ r hr n _).trans ?_
  rw [RingEquiv.apply_symm_apply]
  exact (RingEquiv.apply_symm_apply _ _).symm

end Ring

/-! ### Additive maps out of an extension of scalars -/

section ExtendScalarsLift

variable {R B : Type u} [CommRing R] [CommRing B] (φ : R →+* B) {M : ModuleCat.{u} R}
  {P : Type*} [AddCommGroup P]

/-- **An additive map out of `B ⊗_R M`** from a biadditive map balanced over `φ : R → B`. -/
def extendScalarsLift07Q9 (f : B →+ M →+ P)
    (hf : ∀ (c : R) (t : B) (s : M), f (φ c * t) s = f t (c • s)) :
    (ModuleCat.extendScalars φ).obj M →+ P :=
  TensorProduct.liftAddHom f (fun c t s ↦ hf c t s)

/-- `extendScalarsLift07Q9` on a pure tensor. -/
@[simp] theorem extendScalarsLift07Q9_tmul (f : B →+ M →+ P)
    (hf : ∀ (c : R) (t : B) (s : M), f (φ c * t) s = f t (c • s)) (t : B) (s : M) :
    extendScalarsLift07Q9 φ f hf (Stacks.PullbackModel.tmul φ t s) = f t s :=
  rfl

/-- Two additive maps out of `B ⊗_R M` agreeing on pure tensors agree. -/
theorem extendScalars_addHom_ext07Q9 {g g' : (ModuleCat.extendScalars φ).obj M →+ P}
    (h : ∀ (t : B) (s : M), g (Stacks.PullbackModel.tmul φ t s) =
      g' (Stacks.PullbackModel.tmul φ t s)) : g = g' :=
  AddMonoidHom.ext fun x ↦ TensorProduct.inductionOn x
    (fun t s ↦ h t s)
    (fun x y hx hy ↦ (map_add g x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add g' x y).symm))

end ExtendScalarsLift

/-! ### The sections of `f_cris^*ℱ` over the levels of the Čech system of `f⁻¹(W)` -/

section Source

variable (S : GlobalCrystallineSituation.{u}) {V : S.S.scheme.Opens} {W : S.X.Opens}
  (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hVW : W ≤ sourceToBase S ⁻¹ᵁ V)
  {X' : Scheme.{u}} (f : X' ⟶ S.X) (hW₂ : IsAffineOpen (f ⁻¹ᵁ W)) {κ : Type u}
  (g₂ : MvPolynomial κ (openAffineSituation₂07Q9 S hVW f hW₂).A
    →ₐ[(openAffineSituation₂07Q9 S hVW f hW₂).A] (openAffineSituation₂07Q9 S hVW f hW₂).C)
  (hg₂ : Function.Surjective g₂)
  (r : MvPolynomial (openAffineSituation07Q9 S hW hVW).C (openAffineSituation07Q9 S hW hVW).A →+*
    MvPolynomial κ (openAffineSituation₂07Q9 S hVW f hW₂).A)
  (hr : g₂.toRingHom.comp r = (restrictMap07Q9 S hVW f).appTop.hom.comp
    (canonicalPresentation (openAffineSituation07Q9 S hW hVW)).toRingHom)
  (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsQuasiCoherentCrystal S F)
  (G : (envelopeDPAlgebra (openAffineSituation07Q9 S hW hVW) (canonicalPresentation _)).Hom
    (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂))
  (hG : ∀ (n : ℕ) (x : (envelopeDPAlgebra (openAffineSituation07Q9 S hW hVW)
      (canonicalPresentation _)).completedRing (restrict S V W hVW).p n),
    G.completedRingMap (restrict S V W hVW).p n x =
      (completedEnvelopeMap07Q9 S hW hVW f hW₂ (canonicalPresentation _)
        (canonicalPresentation_surjective _) g₂ hg₂ r hr n).toRingHom x)

/-- **The pulled back crystal `ℱ' = f_cris^*ℱ`** on `Cris(X'/S)`. -/
abbrev sourceSheaf07Q9 : ModuleSheaf (overSituation S f) :=
  (crisModuleInverseImage (S := overSituation S f) (S' := S) (𝟙 S.S) f
    (overSituation_compat S f)).obj ((moduleULift S).obj F)

/-- The level `e` in degree `n` of the Čech system of `f⁻¹(W)`. -/
abbrev sourceLevel07Q9 (n e : ℕ) : CrystallineThickening (overSituation S f) :=
  ((openSystem07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f) g₂
    hg₂).obj (op ⦋n⦌)).obj e

/-- **The restriction `M(n) → ℱ'(T(n)_e)`**: the component of `m ∈ M(n)` at the level `e + N'` of
the system of `W`, restricted along `τ n e` to the level `e` of the system of `f⁻¹(W)`. -/
def sourceRestrict07Q9 (n e : ℕ) (m : (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n) :
    (sourceSheaf07Q9 S f F).val.obj (op (sourceLevel07Q9 S hV hVW f hW₂ g₂ hg₂ n e)) :=
  haveI := isAffine_restrictX07Q9 S hW hVW
  haveI := isAffine_restrictS07Q9 S hV hVW
  crisInverseImageRestrict (S := overSituation S f) (S' := S) (𝟙 S.S) f (overSituation_compat S f) F
    (openSystemMap07Q9 S hV hW hVW f hW₂ (canonicalPresentation _)
      (canonicalPresentation_surjective _) g₂ hg₂ r hr n e)
    (wholeSpaceSectionsVal (isNilpotent_prime_openSituation07Q9 S hW hVW)
      (restrictCrystal07Q9 S V W hVW F hF) m (e + openSystemShift07Q9 S hVW f hW₂))

/-- The restriction `M(n) → ℱ'(T(n)_e)` is additive. -/
theorem sourceRestrict07Q9_add (n e : ℕ)
    (m m' : (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n) :
    sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n e (m + m') =
      sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n e m +
        sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n e m' :=
  lowerShriekRestrict_add _ _ _ _

/-- The scalars of the level `e` in degree `n` of the system of `f⁻¹(W)`, in the ring the sections
of `ℱ'` there are a module over. -/
abbrev sourceScalars07Q9 (n e : ℕ) :
    pAdicCompletedTensorPowerEnvelope (openAffineSituation₂07Q9 S hVW f hW₂) g₂ hg₂ n →+*
      ((structureSheaf (overSituation S f)).obj.obj
        (op (sourceLevel07Q9 S hV hVW f hW₂ g₂ hg₂ n e)) : Type u) :=
  openLevelScalars07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂
    n e

/-- **The restriction `M(n) → ℱ'(T(n)_e)` is semilinear** over the map `D(n) → D'(n)` of completed
envelopes followed by the scalars of the level. -/
theorem sourceRestrict07Q9_smul (n e : ℕ)
    (a : (envelopeDPAlgebra (openAffineSituation07Q9 S hW hVW)
      (canonicalPresentation _)).completedRing (restrict S V W hVW).p n)
    (m : (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n) :
    sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n e (a • m) =
      sourceScalars07Q9 S hV hVW f hW₂ g₂ hg₂ n e
          ((completedEnvelopeMap07Q9 S hW hVW f hW₂ (canonicalPresentation _)
            (canonicalPresentation_surjective _) g₂ hg₂ r hr n).toRingHom a) •
        sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n e m := by
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  have h1 := wholeSpaceSectionsVal_smul (isNilpotent_prime_openSituation07Q9 S hW hVW)
    (restrictCrystal07Q9 S V W hVW F hF) (n := ⦋n⦌) a m (e + openSystemShift07Q9 S hVW f hW₂)
  have h2 := tauRing_openLevelScalars07Q9 S hV hW hVW f hW₂ (canonicalPresentation _)
    (canonicalPresentation_surjective _) g₂ hg₂ r hr n e a
  have h3 := (congrArg (tauRing (openSystemMap07Q9 S hV hW hVW f hW₂ (canonicalPresentation _)
      (canonicalPresentation_surjective _) g₂ hg₂ r hr n e)).hom
    (levelSectionsScalars_eq_openLevelScalars07Q9 S hV hW hVW n
      (e + openSystemShift07Q9 S hVW f hW₂) a)).trans h2
  refine (congrArg (crisInverseImageRestrict (S := overSituation S f) (S' := S) (𝟙 S.S) f
    (overSituation_compat S f) F (openSystemMap07Q9 S hV hW hVW f hW₂ (canonicalPresentation _)
      (canonicalPresentation_surjective _) g₂ hg₂ r hr n e)) h1).trans ?_
  refine (crisInverseImageRestrict_smul (S := overSituation S f) (S' := S) (𝟙 S.S) f
    (overSituation_compat S f) F _ _ _).trans ?_
  exact congrArg (fun t ↦ (show ((structureSheaf (overSituation S f)).obj.obj
    (op (sourceLevel07Q9 S hV hVW f hW₂ g₂ hg₂ n e)) : Type u) from t) • _) h3

/-- The bilinear map `D'(n) × M(n) → ℱ'(T(n)_e)`, `(d, m) ↦ d · τ^* m`. -/
def sourceLevelBil07Q9 (n e : ℕ) :
    (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
        (restrict S V W hVW).p n →+
      ((openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n →+
        (sourceSheaf07Q9 S f F).val.obj (op (sourceLevel07Q9 S hV hVW f hW₂ g₂ hg₂ n e))) :=
  AddMonoidHom.mk'
    (fun d ↦ AddMonoidHom.mk'
      (fun m : (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n ↦
        (sourceScalars07Q9 S hV hVW f hW₂ g₂ hg₂ n e d •
          sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n e m :
            (sourceSheaf07Q9 S f F).val.obj (op (sourceLevel07Q9 S hV hVW f hW₂ g₂ hg₂ n e))))
      (fun m m' ↦ by rw [sourceRestrict07Q9_add, smul_add]))
    (fun d d' ↦ AddMonoidHom.ext fun m ↦
      (congrArg (fun t ↦ (t • sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n e m :
          (sourceSheaf07Q9 S f F).val.obj (op (sourceLevel07Q9 S hV hVW f hW₂ g₂ hg₂ n e))))
        (map_add (sourceScalars07Q9 S hV hVW f hW₂ g₂ hg₂ n e) d d')).trans (add_smul _ _ _))

/-- `V'(n)` before completion: `D'(n) ⊗_{D(n)} M(n)`, along the component of `G`. -/
abbrev sourceTensor07Q9 (n : ℕ) : Type u :=
  letI := G.completedAlgebra07Q9 (restrict S V W hVW).p n
  (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
      (restrict S V W hVW).p n ⊗[(envelopeDPAlgebra (openAffineSituation07Q9 S hW hVW)
        (canonicalPresentation _)).completedRing (restrict S V W hVW).p n]
    (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n

include hG in
/-- **The map `D'(n) ⊗_{D(n)} M(n) → ℱ'(T(n)_e)`**, `d ⊗ m ↦ d · τ^* m`. -/
def sourceLevelMap07Q9 (n e : ℕ) :
    sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n →+
      (sourceSheaf07Q9 S f F).val.obj (op (sourceLevel07Q9 S hV hVW f hW₂ g₂ hg₂ n e)) :=
  letI := G.completedAlgebra07Q9 (restrict S V W hVW).p n
  TensorProduct.liftAddHom (sourceLevelBil07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n e)
    (fun a d m ↦ by
      change sourceScalars07Q9 S hV hVW f hW₂ g₂ hg₂ n e
          (G.completedRingMap (restrict S V W hVW).p n a * d) • _ =
        sourceScalars07Q9 S hV hVW f hW₂ g₂ hg₂ n e d •
          sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n e (a • m)
      rw [sourceRestrict07Q9_smul, ← hG]
      refine (congrArg (fun t ↦ (sourceScalars07Q9 S hV hVW f hW₂ g₂ hg₂ n e t •
          sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n e m :
            (sourceSheaf07Q9 S f F).val.obj (op (sourceLevel07Q9 S hV hVW f hW₂ g₂ hg₂ n e))))
        (mul_comm (G.completedRingMap (restrict S V W hVW).p n a) d)).trans ?_
      refine (congrArg (fun t ↦ (t • sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n
          e m : (sourceSheaf07Q9 S f F).val.obj (op (sourceLevel07Q9 S hV hVW f hW₂ g₂ hg₂ n e))))
        (map_mul (sourceScalars07Q9 S hV hVW f hW₂ g₂ hg₂ n e) d
          (G.completedRingMap (restrict S V W hVW).p n a))).trans (mul_smul _ _ _))

/-- The level map on a pure tensor. -/
theorem sourceLevelMap07Q9_tmul (n e : ℕ)
    (d : (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
      (restrict S V W hVW).p n)
    (m : (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n) :
    letI := G.completedAlgebra07Q9 (restrict S V W hVW).p n
    sourceLevelMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e (d ⊗ₜ m) =
      sourceScalars07Q9 S hV hVW f hW₂ g₂ hg₂ n e d •
        sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n e m :=
  rfl

/-- **The map `D'(n) ⊗_{D(n)} M(n) → ℱ'(T(n)_e)` is semilinear** over the scalars of the level. -/
theorem sourceLevelMap07Q9_smul (n e : ℕ)
    (a : (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
      (restrict S V W hVW).p n)
    (x : sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n) :
    sourceLevelMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e (a • x) =
      sourceScalars07Q9 S hV hVW f hW₂ g₂ hg₂ n e a •
        sourceLevelMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e x := by
  let := G.completedAlgebra07Q9 (restrict S V W hVW).p n
  induction x using TensorProduct.inductionOn with
  | tmul d m =>
    rw [TensorProduct.smul_tmul', sourceLevelMap07Q9_tmul, sourceLevelMap07Q9_tmul,
      smul_eq_mul]
    erw [map_mul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The level map on `1 ⊗ m` is the restriction of `m`. -/
theorem sourceLevelMap07Q9_one_tmul (n e : ℕ)
    (m : (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n) :
    letI := G.completedAlgebra07Q9 (restrict S V W hVW).p n
    sourceLevelMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e (1 ⊗ₜ m) =
      sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n e m := by
  refine (sourceLevelMap07Q9_tmul S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e 1 m).trans ?_
  erw [map_one, one_smul]

/-- The scalars of the level `e` kill `(p)^{N' + e}`. -/
theorem sourceScalars07Q9_eq_zero (n e : ℕ)
    (a : (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
      (restrict S V W hVW).p n)
    (ha : a ∈ DividedPowers.pAdicIdeal (A := (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f
      hW₂) g₂).completedRing (restrict S V W hVW).p n) (restrict S V W hVW).p ^
        (openSystemShift07Q9 S hVW f hW₂ + e)) :
    sourceScalars07Q9 S hV hVW f hW₂ g₂ hg₂ n e a = 0 :=
  (congrArg (openLevelRingEquiv07Q9 (overSituation S f) hV hW₂
      (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂ n e)
    (Ideal.Quotient.eq_zero_iff_mem.2 ha)).trans (map_zero _)

include hG in
/-- **`D'(n) ⊗_{D(n)} M(n) → ℱ'(T(n)_e)` kills `(p)^{N' + e}`.** -/
theorem sourceLevelMap07Q9_eq_zero (n e : ℕ) (x : sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n)
    (hx : x ∈ (DividedPowers.pAdicIdeal (A := (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f
      hW₂) g₂).completedRing (restrict S V W hVW).p n) (restrict S V W hVW).p ^
        (openSystemShift07Q9 S hVW f hW₂ + e) • ⊤ :
          Submodule ((envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
            (restrict S V W hVW).p n) (sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n))) :
    sourceLevelMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e x = 0 := by
  refine Submodule.smul_induction_on hx (fun a ha y _ ↦ ?_) (fun y z hy hz ↦ ?_)
  · rw [sourceLevelMap07Q9_smul, sourceScalars07Q9_eq_zero S hV hVW f hW₂ g₂ hg₂ n e a ha,
      zero_smul]
  · rw [map_add, hy, hz, add_zero]

/-- **The restrictions `M(n) → ℱ'(T(n)_e)` are compatible with the tower maps.** -/
theorem sourceRestrict07Q9_tower (n : ℕ) {e e' : ℕ} (h : e ≤ e')
    (m : (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n) :
    (sourceSheaf07Q9 S f F).val.map (((openSystem07Q9 (overSituation S f) hV hW₂
        (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂).obj (op ⦋n⦌)).map (homOfLE h)).op
        (sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n e' m) =
      sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n e m := by
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  refine (crisInverseImageRestrict_naturality (S := overSituation S f) (S' := S) (𝟙 S.S) f
    (overSituation_compat S f) F _ _ _ _ (openSystemMap07Q9_naturality_tower S hV hW hVW f hW₂
      (canonicalPresentation _) (canonicalPresentation_surjective _) g₂ hg₂ r hr n h) _).trans
    ?_
  exact congrArg (crisInverseImageRestrict (S := overSituation S f) (S' := S) (𝟙 S.S) f
    (overSituation_compat S f) F (openSystemMap07Q9 S hV hW hVW f hW₂ (canonicalPresentation _)
      (canonicalPresentation_surjective _) g₂ hg₂ r hr n e))
    (wholeSpaceSectionsVal_restrict (isNilpotent_prime_openSituation07Q9 S hW hVW)
      (restrictCrystal07Q9 S V W hVW F hF) (n := ⦋n⦌) m
      (homOfLE (Nat.add_le_add_right h (openSystemShift07Q9 S hVW f hW₂))))

/-- The scalars of the levels of the system of `f⁻¹(W)` are compatible with the tower maps. -/
theorem sourceScalars07Q9_tower (n : ℕ) {e e' : ℕ} (h : e ≤ e')
    (a : (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
      (restrict S V W hVW).p n) :
    ((structureSheaf (overSituation S f)).obj.map (((openSystem07Q9 (overSituation S f) hV hW₂
        (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂).obj (op ⦋n⦌)).map (homOfLE h)).op).hom
        (sourceScalars07Q9 S hV hVW f hW₂ g₂ hg₂ n e' a) =
      sourceScalars07Q9 S hV hVW f hW₂ g₂ hg₂ n e a :=
  openLevelScalars07Q9_tower (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f)
    g₂ hg₂ n h a

/-- **The maps `D'(n) ⊗_{D(n)} M(n) → ℱ'(T(n)_e)` are compatible with the tower maps.** -/
theorem sourceLevelMap07Q9_tower (n : ℕ) {e e' : ℕ} (h : e ≤ e')
    (x : sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n) :
    (sourceSheaf07Q9 S f F).val.map (((openSystem07Q9 (overSituation S f) hV hW₂
        (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂).obj (op ⦋n⦌)).map (homOfLE h)).op
        (sourceLevelMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e' x) =
      sourceLevelMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e x := by
  let := G.completedAlgebra07Q9 (restrict S V W hVW).p n
  induction x using TensorProduct.inductionOn with
  | tmul d m =>
    rw [sourceLevelMap07Q9_tmul, sourceLevelMap07Q9_tmul, PresheafOfModules.map_smul,
      sourceRestrict07Q9_tower]
    exact congrArg (fun t ↦ (show ((structureSheaf (overSituation S f)).obj.obj
      (op (sourceLevel07Q9 S hV hVW f hW₂ g₂ hg₂ n e)) : Type u) from t) • _)
      (sourceScalars07Q9_tower S hV hVW f hW₂ g₂ hg₂ n h d)
  | add x y hx hy => simp only [map_add, hx, hy]; rfl

/-! #### The level maps through the base change of sections -/

/-- The level `e + N'` in degree `n` of the system of `W`. -/
abbrev targetLevel07Q9 (n e : ℕ) : CrystallineThickening S :=
  ((openSystem07Q9 S hV hW hVW (canonicalPresentation _) (canonicalPresentation_surjective _)).obj
    (op ⦋n⦌)).obj (e + openSystemShift07Q9 S hVW f hW₂)

/-- The morphism `τ n e` of the Čech systems. -/
abbrev sourceTau07Q9 (n e : ℕ) :=
  openSystemMap07Q9 S hV hW hVW f hW₂ (canonicalPresentation _)
    (canonicalPresentation_surjective _) g₂ hg₂ r hr n e

/-- The scalars of the level `e` in degree `n` of the system of `f⁻¹(W)`, in the commutative ring
of global sections of its ambient scheme. -/
abbrev sourceScalarsTop07Q9 (n e : ℕ) :
    (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
        (restrict S V W hVW).p n →+*
      Γ(((changeBase (overSituation S f) S (𝟙 S.S) f (overSituation_compat S f)).obj
        ((CrystallineThickening.ι (overSituation S f)).obj
          (sourceLevel07Q9 S hV hVW f hW₂ g₂ hg₂ n e))).thickening.target.scheme, ⊤) :=
  sourceScalars07Q9 S hV hVW f hW₂ g₂ hg₂ n e

/-- The component `m_{e + N'}` of `m ∈ M(n)`, a section of `ℱ` over the level `e + N'` of the
system of `W`. -/
def targetVal07Q9 (n e : ℕ) :
    (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n →+
      sectionsOver F (targetLevel07Q9 S hV hW hVW f hW₂ n e) where
  toFun m :=
    haveI := isAffine_restrictX07Q9 S hW hVW
    haveI := isAffine_restrictS07Q9 S hV hVW
    wholeSpaceSectionsVal (isNilpotent_prime_openSituation07Q9 S hW hVW)
      (restrictCrystal07Q9 S V W hVW F hF) m (e + openSystemShift07Q9 S hVW f hW₂)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The reduction `m ↦ m_{e + N'}` is additive. -/
theorem targetVal07Q9_add (n e : ℕ)
    (m m' : (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n) :
    targetVal07Q9 S hV hW hVW f hW₂ F hF n e (m + m') =
      targetVal07Q9 S hV hW hVW f hW₂ F hF n e m + targetVal07Q9 S hV hW hVW f hW₂ F hF n e m' :=
  map_add _ _ _

/-- The bilinear map `D'(n) × M(n) → Γ(T(n)_e) ⊗_{Γ(T'(n)_{e + N'})} ℱ(T'(n)_{e + N'})`,
`(d, m) ↦ d ⊗ m_{e + N'}`. -/
def sourceToBaseChangeBil07Q9 (n e : ℕ) :
    (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
        (restrict S V W hVW).p n →+
      ((openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n →+
        (ModuleCat.extendScalars (tauRing (sourceTau07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr n
          e)).hom).obj (sectionsOver F (targetLevel07Q9 S hV hW hVW f hW₂ n e))) :=
  AddMonoidHom.mk'
    (fun d ↦ AddMonoidHom.mk'
      (fun m ↦ Stacks.PullbackModel.tmul (tauRing (sourceTau07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr
          n e)).hom (sourceScalarsTop07Q9 S hV hVW f hW₂ g₂ hg₂ n e d)
          (targetVal07Q9 S hV hW hVW f hW₂ F hF n e m))
      (fun m m' ↦ by
        rw [targetVal07Q9_add]
        exact Stacks.PullbackColimit.tmul_add _ _ _ _))
    (fun d d' ↦ AddMonoidHom.ext fun m ↦ by
      change Stacks.PullbackModel.tmul _ (sourceScalarsTop07Q9 S hV hVW f hW₂ g₂ hg₂ n e (d + d'))
          (targetVal07Q9 S hV hW hVW f hW₂ F hF n e m) =
        Stacks.PullbackModel.tmul _ (sourceScalarsTop07Q9 S hV hVW f hW₂ g₂ hg₂ n e d)
            (targetVal07Q9 S hV hW hVW f hW₂ F hF n e m) +
          Stacks.PullbackModel.tmul _ (sourceScalarsTop07Q9 S hV hVW f hW₂ g₂ hg₂ n e d')
            (targetVal07Q9 S hV hW hVW f hW₂ F hF n e m)
      rw [Stacks.PullbackColimit.tmul_eq_smul _ (sourceScalarsTop07Q9 S hV hVW f hW₂ g₂ hg₂ n e _),
        map_add, add_smul, ← Stacks.PullbackColimit.tmul_eq_smul,
        ← Stacks.PullbackColimit.tmul_eq_smul])

/-- The ring map of `τ n e` on the scalars of the level `e + N'` of the system of `W`, in the form
of `levelSectionsScalars`. -/
theorem tauRing_levelSectionsScalars07Q9 (n e : ℕ)
    (a : (envelopeDPAlgebra (openAffineSituation07Q9 S hW hVW)
      (canonicalPresentation _)).completedRing (restrict S V W hVW).p n) :
    haveI := isAffine_restrictX07Q9 S hW hVW
    haveI := isAffine_restrictS07Q9 S hV hVW
    (tauRing (sourceTau07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr n e)).hom
        (levelSectionsScalars (isNilpotent_prime_openSituation07Q9 S hW hVW) ⦋n⦌
          (e + openSystemShift07Q9 S hVW f hW₂) a) =
      sourceScalarsTop07Q9 S hV hVW f hW₂ g₂ hg₂ n e
        ((completedEnvelopeMap07Q9 S hW hVW f hW₂ (canonicalPresentation _)
          (canonicalPresentation_surjective _) g₂ hg₂ r hr n).toRingHom a) :=
  (congrArg (tauRing (sourceTau07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr n e)).hom
    (levelSectionsScalars_eq_openLevelScalars07Q9 S hV hW hVW n
      (e + openSystemShift07Q9 S hVW f hW₂) a)).trans
    (tauRing_openLevelScalars07Q9 S hV hW hVW f hW₂ (canonicalPresentation _)
      (canonicalPresentation_surjective _) g₂ hg₂ r hr n e a)

/-- A scalar of `D(n)` acts on the reduction `m ↦ m_{e + N'}` through the scalars of the
level. -/
theorem targetVal07Q9_smul (n e : ℕ)
    (a : (envelopeDPAlgebra (openAffineSituation07Q9 S hW hVW)
      (canonicalPresentation _)).completedRing (restrict S V W hVW).p n)
    (m : (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n) :
    haveI := isAffine_restrictX07Q9 S hW hVW
    haveI := isAffine_restrictS07Q9 S hV hVW
    targetVal07Q9 S hV hW hVW f hW₂ F hF n e (a • m) =
      (show (crisCommRing S).obj (op ((CrystallineThickening.ι S).obj
          (targetLevel07Q9 S hV hW hVW f hW₂ n e))) from
        levelSectionsScalars (isNilpotent_prime_openSituation07Q9 S hW hVW) ⦋n⦌
          (e + openSystemShift07Q9 S hVW f hW₂) a) •
        targetVal07Q9 S hV hW hVW f hW₂ F hF n e m :=
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  wholeSpaceSectionsVal_smul (isNilpotent_prime_openSituation07Q9 S hW hVW)
    (restrictCrystal07Q9 S V W hVW F hF) (n := ⦋n⦌) a m (e + openSystemShift07Q9 S hVW f hW₂)

include hG in
/-- **The map `D'(n) ⊗_{D(n)} M(n) → Γ(T(n)_e) ⊗_{Γ(T'(n)_{e + N'})} ℱ(T'(n)_{e + N'})`**,
`d ⊗ m ↦ d ⊗ m_{e + N'}`. -/
def sourceToBaseChange07Q9 (n e : ℕ) :
    sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n →+
      (ModuleCat.extendScalars (tauRing (sourceTau07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr n
        e)).hom).obj (sectionsOver F (targetLevel07Q9 S hV hW hVW f hW₂ n e)) :=
  letI := G.completedAlgebra07Q9 (restrict S V W hVW).p n
  TensorProduct.liftAddHom (sourceToBaseChangeBil07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n e)
    (fun a d m ↦ by
      change Stacks.PullbackModel.tmul _ (sourceScalarsTop07Q9 S hV hVW f hW₂ g₂ hg₂ n e
          (G.completedRingMap (restrict S V W hVW).p n a * d))
          (targetVal07Q9 S hV hW hVW f hW₂ F hF n e m) =
        Stacks.PullbackModel.tmul _ (sourceScalarsTop07Q9 S hV hVW f hW₂ g₂ hg₂ n e d)
          (targetVal07Q9 S hV hW hVW f hW₂ F hF n e (a • m))
      rw [targetVal07Q9_smul, Stacks.PullbackColimit.tmul_smul_right,
        tauRing_levelSectionsScalars07Q9, ← hG, map_mul, mul_comm])

/-- `sourceToBaseChange07Q9` on a pure tensor. -/
theorem sourceToBaseChange07Q9_tmul (n e : ℕ)
    (d : (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
      (restrict S V W hVW).p n)
    (m : (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n) :
    letI := G.completedAlgebra07Q9 (restrict S V W hVW).p n
    sourceToBaseChange07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e (d ⊗ₜ m) =
      Stacks.PullbackModel.tmul (tauRing (sourceTau07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr
          n e)).hom (sourceScalarsTop07Q9 S hV hVW f hW₂ g₂ hg₂ n e d)
          (targetVal07Q9 S hV hW hVW f hW₂ F hF n e m) :=
  rfl

/-- **The level map factors through the base change of the sections of `ℱ`**: it is
`sourceToBaseChange07Q9` followed by `crisInverseImageBaseChange`. -/
theorem crisInverseImageBaseChange_sourceToBaseChange07Q9 (n e : ℕ)
    (x : sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n) :
    crisInverseImageBaseChange (S := overSituation S f) (S' := S) (𝟙 S.S) f
        (overSituation_compat S f) F (sourceTau07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr n e)
        (sourceToBaseChange07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e x) =
      sourceLevelMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e x := by
  let := G.completedAlgebra07Q9 (restrict S V W hVW).p n
  induction x using TensorProduct.inductionOn with
  | tmul d m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-! #### The inverse on the levels -/

/-- The level `(p)^{N' + e}` of the `p`-adic filtration of `D'(n) ⊗_{D(n)} M(n)`. -/
abbrev sourceTensorLevel07Q9 (n e : ℕ) :
    Submodule ((envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
      (restrict S V W hVW).p n) (sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n) :=
  DividedPowers.pAdicIdeal (A := (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f
    hW₂) g₂).completedRing (restrict S V W hVW).p n) (restrict S V W hVW).p ^
      (openSystemShift07Q9 S hVW f hW₂ + e) • ⊤

/-- `M(n)/(p)^{N + e + N'}`. -/
abbrev targetQuot07Q9 (n e : ℕ) : Type u :=
  (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n ⧸
    (DividedPowers.pAdicIdeal (A := (envelopeDPAlgebra (openAffineSituation07Q9 S hW hVW)
        (canonicalPresentation _)).completedRing (restrict S V W hVW).p n)
        (restrict S V W hVW).p ^
      (uniformLevel (openAffineSituation07Q9 S hW hVW) + (e + openSystemShift07Q9 S hVW f hW₂))
      • (⊤ : Submodule ((envelopeDPAlgebra (openAffineSituation07Q9 S hW hVW)
        (canonicalPresentation _)).completedRing (restrict S V W hVW).p n)
        ((openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n)))

/-- **The kernel of `m ↦ m_{e + N'}` is `(p)^{N + e + N'} M(n)`**, the level quotient property of
the cosimplicial module of a quasi-coherent crystal. -/
theorem targetVal07Q9_eq_zero_iff (n e : ℕ)
    (m : (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n) :
    targetVal07Q9 S hV hW hVW f hW₂ F hF n e m = 0 ↔
      m ∈ (DividedPowers.pAdicIdeal (A := (envelopeDPAlgebra (openAffineSituation07Q9 S hW hVW)
        (canonicalPresentation _)).completedRing (restrict S V W hVW).p n)
        (restrict S V W hVW).p ^
      (uniformLevel (openAffineSituation07Q9 S hW hVW) + (e + openSystemShift07Q9 S hVW f hW₂))
      • (⊤ : Submodule ((envelopeDPAlgebra (openAffineSituation07Q9 S hW hVW)
        (canonicalPresentation _)).completedRing (restrict S V W hVW).p n)
        ((openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n))) :=
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  (mem_pow_smul_top_iff_wholeSpaceSectionsVal_eq_zero (isNilpotent_prime_openSituation07Q9 S hW hVW)
    (restrictCrystal07Q9 S V W hVW F hF)
    (isSurjectiveComparison_of_isSheafCrystal (restrictCrystal07Q9 S V W hVW F hF).property.2) n
    (e + openSystemShift07Q9 S hVW f hW₂) m).symm

/-- The pairing `D'(n) × M(n) → (D'(n) ⊗_{D(n)} M(n)) / (p)^{N' + e}` on a fixed first factor,
which kills `(p)^{N + e + N'} M(n)`. -/
def sourcePairingRight07Q9 (n e : ℕ)
    (d : (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
      (restrict S V W hVW).p n) :
    targetQuot07Q9 S hV hW hVW f hW₂ F hF n e →+
      sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n ⧸
        sourceTensorLevel07Q9 S hV hW hVW f hW₂ g₂ F hF G n e :=
  letI := G.completedAlgebra07Q9 (restrict S V W hVW).p n
  QuotientAddGroup.lift _
    ((Submodule.mkQ (sourceTensorLevel07Q9 S hV hW hVW f hW₂ g₂ F hF G n e)).toAddMonoidHom.comp
      ((TensorProduct.mk _ _ _ d).toAddMonoidHom))
    (fun m hm ↦ by
      change Submodule.Quotient.mk (d ⊗ₜ[(envelopeDPAlgebra (openAffineSituation07Q9 S hW hVW)
            (canonicalPresentation _)).completedRing (restrict S V W hVW).p n] m) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      refine Submodule.smul_induction_on hm (fun a ha m' _ ↦ ?_) (fun x y hx hy ↦ ?_)
      · have hGa : G.completedRingMap (restrict S V W hVW).p n a ∈
            DividedPowers.pAdicIdeal (A := (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f
              hW₂) g₂).completedRing (restrict S V W hVW).p n) (restrict S V W hVW).p ^
                (openSystemShift07Q9 S hVW f hW₂ + e) := by
          refine Ideal.pow_le_pow_right (show openSystemShift07Q9 S hVW f hW₂ + e ≤
            uniformLevel (openAffineSituation07Q9 S hW hVW) +
              (e + openSystemShift07Q9 S hVW f hW₂) by omega) ?_
          rw [← pAdicIdeal_map_ringHom (restrict S V W hVW).p
            (G.completedRingMap (restrict S V W hVW).p n), ← Ideal.map_pow]
          exact Ideal.mem_map_of_mem _ ha
        change d ⊗ₜ[(envelopeDPAlgebra (openAffineSituation07Q9 S hW hVW)
            (canonicalPresentation _)).completedRing (restrict S V W hVW).p n]
          (a • (m' : (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n)) ∈ _
        rw [← TensorProduct.smul_tmul, Algebra.smul_def, ← smul_eq_mul, ← TensorProduct.smul_tmul']
        exact Submodule.smul_mem_smul hGa Submodule.mem_top
      · rw [TensorProduct.tmul_add]
        exact add_mem hx hy)

/-- `sourcePairingRight07Q9` on a class. -/
theorem sourcePairingRight07Q9_mk (n e : ℕ)
    (d : (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
      (restrict S V W hVW).p n)
    (m : (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n) :
    letI := G.completedAlgebra07Q9 (restrict S V W hVW).p n
    sourcePairingRight07Q9 S hV hW hVW f hW₂ g₂ F hF G n e d (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (d ⊗ₜ m) :=
  rfl

/-- **The pairing
`D'(n)/(p)^{N' + e} × M(n)/(p)^{N + e + N'} → (D'(n) ⊗_{D(n)} M(n))/(p)^{N' + e}`** induced by
`(d, m) ↦ d ⊗ m`. -/
def sourcePairing07Q9 (n e : ℕ) :
    (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
        (restrict S V W hVW).p n ⧸ DividedPowers.pAdicIdeal (A := (envelopeDPAlgebra
          (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing (restrict S V W hVW).p n)
          (restrict S V W hVW).p ^ (openSystemShift07Q9 S hVW f hW₂ + e) →+
      (targetQuot07Q9 S hV hW hVW f hW₂ F hF n e →+
      sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n ⧸
        sourceTensorLevel07Q9 S hV hW hVW f hW₂ g₂ F hF G n e) :=
  letI := G.completedAlgebra07Q9 (restrict S V W hVW).p n
  QuotientAddGroup.lift _
    (AddMonoidHom.mk' (sourcePairingRight07Q9 S hV hW hVW f hW₂ g₂ F hF G n e)
      (fun d d' ↦ AddMonoidHom.ext fun z ↦ by
        obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        change sourcePairingRight07Q9 S hV hW hVW f hW₂ g₂ F hF G n e (d + d')
            (Submodule.Quotient.mk m) =
          sourcePairingRight07Q9 S hV hW hVW f hW₂ g₂ F hF G n e d (Submodule.Quotient.mk m) +
            sourcePairingRight07Q9 S hV hW hVW f hW₂ g₂ F hF G n e d' (Submodule.Quotient.mk m)
        rw [sourcePairingRight07Q9_mk, sourcePairingRight07Q9_mk, sourcePairingRight07Q9_mk,
          TensorProduct.add_tmul]
        rfl))
    (fun d hd ↦ AddMonoidHom.ext fun z ↦ by
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      change sourcePairingRight07Q9 S hV hW hVW f hW₂ g₂ F hF G n e d
          (Submodule.Quotient.mk m) = 0
      rw [sourcePairingRight07Q9_mk, Submodule.Quotient.mk_eq_zero, ← mul_one d, ← smul_eq_mul,
        ← TensorProduct.smul_tmul']
      exact Submodule.smul_mem_smul hd Submodule.mem_top)

/-- `sourcePairing07Q9` on classes. -/
theorem sourcePairing07Q9_mk (n e : ℕ)
    (d : (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
      (restrict S V W hVW).p n)
    (m : (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n) :
    letI := G.completedAlgebra07Q9 (restrict S V W hVW).p n
    sourcePairing07Q9 S hV hW hVW f hW₂ g₂ F hF G n e (Ideal.Quotient.mk _ d)
        (Submodule.Quotient.mk m) = Submodule.Quotient.mk (d ⊗ₜ m) :=
  rfl

/-- The sections of `ℱ` over the extension of an object of `Cris(W/S|_V)` are the sections of its
restriction over the object, as abelian groups. -/
def restrictSectionsAddEquiv07Q9 (A : CrystallineThickening (restrict S V W hVW)) :
    (smallExtendSheafRestriction S V W hVW F).val.obj (op A) ≃+
      F.val.obj (op ((smallExtend S V W hVW).obj A)) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The reduction `m ↦ m_{e + N'}` is surjective. -/
theorem targetVal07Q9_surjective (n e : ℕ) :
    Function.Surjective (targetVal07Q9 S hV hW hVW f hW₂ F hF n e) :=
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  surjective_wholeSpaceSectionsVal (isNilpotent_prime_openSituation07Q9 S hW hVW)
    (restrictCrystal07Q9 S V W hVW F hF)
    (isSurjectiveComparison_of_isSheafCrystal (restrictCrystal07Q9 S V W hVW F hF).property.2) n
    (e + openSystemShift07Q9 S hVW f hW₂)

/-- **The inverse `ℱ(T'(n)_{e + N'}) → M(n)/(p)^{N + e + N'}` of the reduction to the level**,
through a choice of lifts. -/
def targetLevelInv07Q9 (n e : ℕ) :
    sectionsOver F (targetLevel07Q9 S hV hW hVW f hW₂ n e) →+
      targetQuot07Q9 S hV hW hVW f hW₂ F hF n e where
  toFun y := Submodule.Quotient.mk
    (Function.surjInv (targetVal07Q9_surjective S hV hW hVW f hW₂ F hF n e) y)
  map_zero' := by
    rw [← Submodule.Quotient.mk_zero, Submodule.Quotient.eq, sub_zero,
      ← targetVal07Q9_eq_zero_iff,
      Function.surjInv_eq (targetVal07Q9_surjective S hV hW hVW f hW₂ F hF n e)]
  map_add' y y' := by
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq, ← targetVal07Q9_eq_zero_iff]
    rw [map_sub, map_add, Function.surjInv_eq (targetVal07Q9_surjective S hV hW hVW f hW₂ F hF n e),
      Function.surjInv_eq (targetVal07Q9_surjective S hV hW hVW f hW₂ F hF n e),
      Function.surjInv_eq (targetVal07Q9_surjective S hV hW hVW f hW₂ F hF n e), sub_self]

/-- `targetLevelInv07Q9` inverts the reduction to the level. -/
theorem targetLevelInv07Q9_targetVal (n e : ℕ)
    (m : (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n) :
    targetLevelInv07Q9 S hV hW hVW f hW₂ F hF n e (targetVal07Q9 S hV hW hVW f hW₂ F hF n e m) =
      Submodule.Quotient.mk m := by
  change Submodule.Quotient.mk _ = _
  rw [Submodule.Quotient.eq, ← targetVal07Q9_eq_zero_iff, map_sub,
    Function.surjInv_eq (targetVal07Q9_surjective S hV hW hVW f hW₂ F hF n e), sub_self]

/-- The section ring of the level `e` of the system of `f⁻¹(W)` is `D'(n)/(p)^{N' + e}`. -/
abbrev sourceLevelRingEquiv07Q9 (n e : ℕ) :=
  openLevelRingEquiv07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f) g₂
    hg₂ n e


/-- The identification of the section ring of the level `e` of the system of `f⁻¹(W)` with
`D'(n)/(p)^{N' + e}`, read from the global sections of the ambient scheme. -/
def sourceLevelRingInv07Q9 (n e : ℕ) :
    Γ(((changeBase (overSituation S f) S (𝟙 S.S) f (overSituation_compat S f)).obj
        ((CrystallineThickening.ι (overSituation S f)).obj
          (sourceLevel07Q9 S hV hVW f hW₂ g₂ hg₂ n e))).thickening.target.scheme, ⊤) →+
      (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
          (restrict S V W hVW).p n ⧸ DividedPowers.pAdicIdeal (A := (envelopeDPAlgebra
            (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing (restrict S V W hVW).p n)
            (restrict S V W hVW).p ^ (openSystemShift07Q9 S hVW f hW₂ + e) :=
  (sourceLevelRingEquiv07Q9 S hV hVW f hW₂ g₂ hg₂ n e).symm.toAddMonoidHom

/-- `sourceLevelRingInv07Q9` inverts the scalars of the level. -/
theorem sourceLevelRingInv07Q9_scalars (n e : ℕ)
    (d : (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
      (restrict S V W hVW).p n) :
    sourceLevelRingInv07Q9 S hV hVW f hW₂ g₂ hg₂ n e
        (sourceScalarsTop07Q9 S hV hVW f hW₂ g₂ hg₂ n e d) = Ideal.Quotient.mk _ d :=
  (sourceLevelRingEquiv07Q9 S hV hVW f hW₂ g₂ hg₂ n e).symm_apply_apply _

/-- The bilinear map `Γ(T(n)_e) × ℱ(T'(n)_{e + N'}) → (D'(n) ⊗_{D(n)} M(n))/(p)^{N' + e}` through
the identifications of the two factors with the levels. -/
def baseChangeToSourceBil07Q9 (n e : ℕ) :
    Γ(((changeBase (overSituation S f) S (𝟙 S.S) f (overSituation_compat S f)).obj
        ((CrystallineThickening.ι (overSituation S f)).obj
          (sourceLevel07Q9 S hV hVW f hW₂ g₂ hg₂ n e))).thickening.target.scheme, ⊤) →+
      (sectionsOver F (targetLevel07Q9 S hV hW hVW f hW₂ n e) →+
        sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n ⧸
          sourceTensorLevel07Q9 S hV hW hVW f hW₂ g₂ F hF G n e) :=
  AddMonoidHom.mk'
    (fun t ↦ (sourcePairing07Q9 S hV hW hVW f hW₂ g₂ F hF G n e
        (sourceLevelRingInv07Q9 S hV hVW f hW₂ g₂ hg₂ n e t)).comp
      (targetLevelInv07Q9 S hV hW hVW f hW₂ F hF n e))
    (fun t t' ↦ by
      rw [map_add, map_add]
      exact AddMonoidHom.add_comp _ _ _)

/-- `baseChangeToSourceBil07Q9` on the reductions of `d` and `m` is the class of `d ⊗ m`. -/
theorem baseChangeToSourceBil07Q9_apply (n e : ℕ)
    (d : (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
      (restrict S V W hVW).p n)
    (m : (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n) :
    letI := G.completedAlgebra07Q9 (restrict S V W hVW).p n
    baseChangeToSourceBil07Q9 S hV hW hVW f hW₂ g₂ hg₂ F hF G n e
        (sourceScalarsTop07Q9 S hV hVW f hW₂ g₂ hg₂ n e d)
        (targetVal07Q9 S hV hW hVW f hW₂ F hF n e m) =
      Submodule.Quotient.mk (d ⊗ₜ m) := by
  change sourcePairing07Q9 S hV hW hVW f hW₂ g₂ F hF G n e
      (sourceLevelRingInv07Q9 S hV hVW f hW₂ g₂ hg₂ n e
        (sourceScalarsTop07Q9 S hV hVW f hW₂ g₂ hg₂ n e d))
      (targetLevelInv07Q9 S hV hW hVW f hW₂ F hF n e
        (targetVal07Q9 S hV hW hVW f hW₂ F hF n e m)) = _
  rw [sourceLevelRingInv07Q9_scalars, targetLevelInv07Q9_targetVal]
  rfl

/-- The scalars of the levels of the system of `f⁻¹(W)` are surjective. -/
theorem sourceScalarsTop07Q9_surjective (n e : ℕ) :
    Function.Surjective (sourceScalarsTop07Q9 S hV hVW f hW₂ g₂ hg₂ n e) :=
  openLevelScalars07Q9_surjective (overSituation S f) hV hW₂
    (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂ n e

include hG in
/-- **The inverse map `Γ(T(n)_e) ⊗_{Γ(T'(n)_{e + N'})} ℱ(T'(n)_{e + N'}) →
(D'(n) ⊗_{D(n)} M(n))/(p)^{N' + e}`**, `λ(d) ⊗ m_{e + N'} ↦ d ⊗ m`. -/
def baseChangeToSource07Q9 (n e : ℕ) :
    (ModuleCat.extendScalars (tauRing (sourceTau07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr n
        e)).hom).obj (sectionsOver F (targetLevel07Q9 S hV hW hVW f hW₂ n e)) →+
      sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n ⧸
        sourceTensorLevel07Q9 S hV hW hVW f hW₂ g₂ F hF G n e :=
  letI := G.completedAlgebra07Q9 (restrict S V W hVW).p n
  extendScalarsLift07Q9 _ (baseChangeToSourceBil07Q9 S hV hW hVW f hW₂ g₂ hg₂ F hF G n e)
    (fun c t y ↦ by
      have := isAffine_restrictX07Q9 S hW hVW
      have := isAffine_restrictS07Q9 S hV hVW
      obtain ⟨a, rfl⟩ : ∃ a, levelSectionsScalars (isNilpotent_prime_openSituation07Q9 S hW hVW)
          ⦋n⦌ (e + openSystemShift07Q9 S hVW f hW₂) a = c := by
        obtain ⟨a, ha⟩ := openLevelScalars07Q9_surjective S hV hW hVW (canonicalPresentation _)
          (canonicalPresentation_surjective _) n (e + openSystemShift07Q9 S hVW f hW₂) c
        exact ⟨a, (levelSectionsScalars_eq_openLevelScalars07Q9 S hV hW hVW n _ a).trans ha⟩
      obtain ⟨d, rfl⟩ := sourceScalarsTop07Q9_surjective S hV hVW f hW₂ g₂ hg₂ n e t
      obtain ⟨m, rfl⟩ := targetVal07Q9_surjective S hV hW hVW f hW₂ F hF n e y
      have h1 := (tauRing_levelSectionsScalars07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr n e a).trans
        (congrArg (sourceScalarsTop07Q9 S hV hVW f hW₂ g₂ hg₂ n e) (hG n a).symm)
      refine (congrArg (fun t ↦ baseChangeToSourceBil07Q9 S hV hW hVW f hW₂ g₂ hg₂ F hF G n e t
        (targetVal07Q9 S hV hW hVW f hW₂ F hF n e m))
          ((congrArg (· * sourceScalarsTop07Q9 S hV hVW f hW₂ g₂ hg₂ n e d) h1).trans
            (map_mul (sourceScalarsTop07Q9 S hV hVW f hW₂ g₂ hg₂ n e) _ d).symm)).trans ?_
      refine Eq.trans ?_ (congrArg (baseChangeToSourceBil07Q9 S hV hW hVW f hW₂ g₂ hg₂ F hF G n e
        (sourceScalarsTop07Q9 S hV hVW f hW₂ g₂ hg₂ n e d))
          (targetVal07Q9_smul S hV hW hVW f hW₂ F hF n e a m))
      rw [baseChangeToSourceBil07Q9_apply, baseChangeToSourceBil07Q9_apply]
      exact congrArg Submodule.Quotient.mk (TensorProduct.smul_tmul
        (show (envelopeDPAlgebra (openAffineSituation07Q9 S hW hVW)
          (canonicalPresentation _)).completedRing (restrict S V W hVW).p n from a) d m))

/-- **`baseChangeToSource07Q9` is a left inverse of `sourceToBaseChange07Q9` modulo
`(p)^{N' + e}`.** -/
theorem baseChangeToSource07Q9_sourceToBaseChange (n e : ℕ)
    (x : sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n) :
    baseChangeToSource07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e
        (sourceToBaseChange07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e x) =
      Submodule.Quotient.mk x := by
  let := G.completedAlgebra07Q9 (restrict S V W hVW).p n
  induction x using TensorProduct.inductionOn with
  | tmul d m => exact baseChangeToSourceBil07Q9_apply S hV hW hVW f hW₂ g₂ hg₂ F hF G n e d m
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]
    rfl

/-! #### The levelwise identification -/

/-- The tower `e ↦ ℱ'(T(n)_e)` of sections of the pulled back crystal over the levels of the Čech
system of `f⁻¹(W)` in degree `n`. -/
abbrev sourceTower07Q9 (n : ℕ) : ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (sectionSystem (openSystem07Q9 (overSituation S f) hV hW₂
    (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂)
    ((toAbelianSheaf (overSituation S f)).obj (sourceSheaf07Q9 S f F)).obj).obj ⦋n⦌

/-- The level maps as maps into the tower. -/
abbrev sourceTowerMap07Q9 (n e : ℕ) :
    sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n →+
      (sourceTower07Q9 S hV hVW f hW₂ g₂ hg₂ F n).obj (op e) :=
  sourceLevelMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e

/-- The maps into the tower kill `(p)^{N' + e}`. -/
theorem sourceTowerMap07Q9_eq_zero (n e : ℕ)
    (x : sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n)
    (hx : x ∈ (DividedPowers.pAdicIdeal (A := (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f
      hW₂) g₂).completedRing (restrict S V W hVW).p n) (restrict S V W hVW).p ^
        (openSystemShift07Q9 S hVW f hW₂ + e) • ⊤ :
          Submodule ((envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
            (restrict S V W hVW).p n) (sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n))) :
    sourceTowerMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e x = 0 :=
  sourceLevelMap07Q9_eq_zero S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e x hx

/-- The maps into the tower are compatible with its transition maps. -/
theorem sourceTowerMap07Q9_comp {n : ℕ} {e e' : ℕ} (h : e ≤ e')
    (x : sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n) :
    (sourceTower07Q9 S hV hVW f hW₂ g₂ hg₂ F n).map (homOfLE h).op
        (sourceTowerMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e' x) =
      sourceTowerMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e x :=
  sourceLevelMap07Q9_tower S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n h x

include hG in
/-- The map `D'(n) ⊗_{D(n)} M(n) → Γ(T(n)_e) ⊗_{Γ(T'(n)_{e + N'})} ℱ(T'(n)_{e + N'})` is
surjective. -/
private theorem sourceToBaseChange07Q9_surjective (n e : ℕ) :
    Function.Surjective
      (sourceToBaseChange07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e) := by
  intro x
  let := G.completedAlgebra07Q9 (restrict S V W hVW).p n
  induction x using TensorProduct.inductionOn with
  | tmul t s =>
    obtain ⟨d, rfl⟩ := sourceScalarsTop07Q9_surjective S hV hVW f hW₂ g₂ hg₂ n e t
    obtain ⟨m, rfl⟩ := targetVal07Q9_surjective S hV hW hVW f hW₂ F hF n e s
    exact ⟨d ⊗ₜ m, rfl⟩
  | add x x' hx hx' =>
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hx'
    exact ⟨y + y', map_add _ _ _⟩

/-- **The level map `(D'(n) ⊗_{D(n)} M(n))/(p)^{N' + e} → ℱ'(T(n)_e)` is bijective.** -/
theorem bijective_sourceLevelMap07Q9 (n e : ℕ) :
    Function.Bijective (AdicLevelCone07Q9.levelMap (DividedPowers.pAdicIdeal
      (A := (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
        (restrict S V W hVW).p n) (restrict S V W hVW).p)
      (sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n) (openSystemShift07Q9 S hVW f hW₂)
      (sourceTower07Q9 S hV hVW f hW₂ g₂ hg₂ F n)
      (sourceTowerMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n)
      (sourceTowerMap07Q9_eq_zero S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n) e) := by
  have := isAffine_target_openSystem07Q9 S hV hW hVW (canonicalPresentation _)
    (canonicalPresentation_surjective _) n (e + openSystemShift07Q9 S hVW f hW₂)
  have := isAffine_target_openSystem07Q9 (overSituation S f) hV hW₂
    (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂ n e
  have hBC := bijective_crisInverseImageBaseChange (S := overSituation S f) (S' := S) (𝟙 S.S) f
    (overSituation_compat S f) F (sourceTau07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr n e)
    (isLocallyQuasiCoherent_of_isQuasicoherentOnSite F hF.1) hF.2
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have h1 : sourceToBaseChange07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e y = 0 :=
      hBC.1 (by rwa [map_zero, crisInverseImageBaseChange_sourceToBaseChange07Q9])
    rw [← baseChangeToSource07Q9_sourceToBaseChange S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e,
      h1, map_zero]
  · intro w
    obtain ⟨x, rfl⟩ := hBC.2 w
    obtain ⟨y, rfl⟩ :=
      sourceToBaseChange07Q9_surjective S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e x
    exact ⟨Submodule.Quotient.mk y,
      (crisInverseImageBaseChange_sourceToBaseChange07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G
        hG n e y).symm⟩

/-! #### Compatibility with the cosimplicial structure -/

/-- **The restrictions `M(n) → ℱ'(T(n)_e)` are compatible with the cosimplicial structure.** -/
theorem sourceRestrict07Q9_simplicial {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) (e : ℕ)
    (x : (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n) :
    (sourceSheaf07Q9 S f F).val.map (((openSystem07Q9 (overSituation S f) hV hW₂
        (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂).map φ.op).app e).op
        (sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n e x) =
      sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF m e
        ((openCosimplicialModule07Q9 S hV hW hVW F hF).map φ x) := by
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  exact crisInverseImageRestrict_naturality (S := overSituation S f) (S' := S) (𝟙 S.S) f
    (overSituation_compat S f) F _ _ _ _ (openSystemMap07Q9_naturality_simplicial S hV hW hVW f
      hW₂ (canonicalPresentation _) (canonicalPresentation_surjective _) g₂ hg₂ r hr φ e) _

/-- The scalars of the levels of the system of `f⁻¹(W)` are compatible with the cosimplicial
structure. -/
theorem sourceScalars07Q9_simplicial {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) (e : ℕ)
    (a : (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
      (restrict S V W hVW).p n) :
    ((structureSheaf (overSituation S f)).obj.map (((openSystem07Q9 (overSituation S f) hV hW₂
        (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂).map φ.op).app e).op).hom
        (sourceScalars07Q9 S hV hVW f hW₂ g₂ hg₂ n e a) =
      sourceScalars07Q9 S hV hVW f hW₂ g₂ hg₂ m e
        ((envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRingMap
          (restrict S V W hVW).p φ a) :=
  openLevelScalars07Q9_simplicial (overSituation S f) hV hW₂
    (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂ φ e a

/-- **The level maps are compatible with the cosimplicial structure**: the transition of the base
change `D'(n) ⊗ M(n) → D'(m) ⊗ M(m)` followed by the level map in degree `m` is the level map in
degree `n` followed by the restriction of `ℱ'` along `T(φ)_e`. -/
theorem sourceLevelMap07Q9_simplicial {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) (e : ℕ)
    (y : sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n) :
    sourceLevelMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG m e
        ((openCosimplicialModule07Q9 S hV hW hVW F hF).pullbackTensorMap07Q9 G φ y) =
      (sourceSheaf07Q9 S f F).val.map (((openSystem07Q9 (overSituation S f) hV hW₂
        (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂).map φ.op).app e).op
        (sourceLevelMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e y) := by
  let := G.completedAlgebra07Q9 (restrict S V W hVW).p n
  let := G.completedAlgebra07Q9 (restrict S V W hVW).p m
  induction y using TensorProduct.inductionOn with
  | tmul d x =>
    refine Eq.trans (show _ = sourceScalars07Q9 S hV hVW f hW₂ g₂ hg₂ m e
        ((envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRingMap
          (restrict S V W hVW).p φ d) •
        sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF m e
          ((openCosimplicialModule07Q9 S hV hW hVW F hF).map φ x) from rfl) ?_
    refine Eq.trans ?_ (PresheafOfModules.map_smul (sourceSheaf07Q9 S f F).val
      (((openSystem07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f) g₂
        hg₂).map φ.op).app e).op (sourceScalars07Q9 S hV hVW f hW₂ g₂ hg₂ n e d)
      (sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n e x)).symm
    rw [sourceRestrict07Q9_simplicial]
    exact congrArg (fun t ↦ (show ((structureSheaf (overSituation S f)).obj.obj
      (op (sourceLevel07Q9 S hV hVW f hW₂ g₂ hg₂ m e)) : Type u) from t) •
        sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF m e
          ((openCosimplicialModule07Q9 S hV hW hVW F hF).map φ x))
      (sourceScalars07Q9_simplicial S hV hVW f hW₂ g₂ hg₂ φ e d).symm
  | add x y hx hy => simp only [map_add, hx, hy]; rfl

/-! #### The limit over the levels -/

/-- The cosimplicial module `M'(•)` of the base change of `M(•)` along `G`. -/
abbrev sourceModule07Q9 :=
  (openCosimplicialModule07Q9 S hV hW hVW F hF).pullback07Q9 G

/-- **`M'(n)` with the level maps is a cone over the sections of `ℱ'` over the levels.** -/
abbrev sourceCone07Q9 (n : ℕ) : Cone (sourceTower07Q9 S hV hVW f hW₂ g₂ hg₂ F n) :=
  AdicLevelCone07Q9.cone (DividedPowers.pAdicIdeal
      (A := (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
        (restrict S V W hVW).p n) (restrict S V W hVW).p)
    (sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n) (openSystemShift07Q9 S hVW f hW₂)
    (sourceTower07Q9 S hV hVW f hW₂ g₂ hg₂ F n)
    (sourceTowerMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n)
    (sourceTowerMap07Q9_eq_zero S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n)
    (sourceTowerMap07Q9_comp S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG)

/-- **`M'(n) = lim_e ℱ'(T(n)_e)`**: the cone is a limit cone. -/
def sourceConeIsLimit07Q9 (n : ℕ) : IsLimit (sourceCone07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G
    hG n) :=
  AdicLevelCone07Q9.isLimit _ _ _ _ _ _ _
    (bijective_sourceLevelMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n)

/-- **The degree-`n` term of the Čech sections of `ℱ'` over the system of `f⁻¹(W)` is `M'(n)`.** -/
def sourceSectionsLimitIso07Q9 (n : ℕ) :
    limit (sourceTower07Q9 S hV hVW f hW₂ g₂ hg₂ F n) ≅
      (sourceCone07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n).pt :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _)
    (sourceConeIsLimit07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n)

/-- The components of the inverse of `sourceSectionsLimitIso07Q9` are the level maps. -/
theorem sourceSectionsLimitIso07Q9_inv_π (n e : ℕ) :
    (sourceSectionsLimitIso07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n).inv ≫
        limit.π (sourceTower07Q9 S hV hVW f hW₂ g₂ hg₂ F n) (op e) =
      (sourceCone07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n).π.app (op e) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

/-- `sourceSectionsLimitIso07Q9_inv_π` on elements. -/
theorem sourceSectionsLimitIso07Q9_inv_π_apply (n e : ℕ)
    (x : ULift.{u + 1} (AdicCompletion (DividedPowers.pAdicIdeal
      (A := (envelopeDPAlgebra (openAffineSituation₂07Q9 S hVW f hW₂) g₂).completedRing
        (restrict S V W hVW).p n) (restrict S V W hVW).p)
      (sourceTensor07Q9 S hV hW hVW f hW₂ g₂ F hF G n))) :
    ConcreteCategory.hom (limit.π (sourceTower07Q9 S hV hVW f hW₂ g₂ hg₂ F n) (op e))
        (ConcreteCategory.hom
          (sourceSectionsLimitIso07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n).inv x) =
      AdicLevelCone07Q9.levelMap _ _ _ _
        (sourceTowerMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n)
        (sourceTowerMap07Q9_eq_zero S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n) e
        (x.down.val (openSystemShift07Q9 S hVW f hW₂ + e)) :=
  ConcreteCategory.congr_hom
    (sourceSectionsLimitIso07Q9_inv_π S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e) x

/-- The transitions of `M'(•)` on the levels: they are induced by the transitions of the
uncompleted base change. -/
theorem levelMap_sourceModule07Q9_map {n m : ℕ} (φ : ⦋n⦌ ⟶ ⦋m⦌) (e : ℕ)
    (x : (sourceModule07Q9 S hV hW hVW f hW₂ g₂ F hF G).carrier n) :
    AdicLevelCone07Q9.levelMap _ _ _ _
        (sourceTowerMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG m)
        (sourceTowerMap07Q9_eq_zero S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG m) e
        (((sourceModule07Q9 S hV hW hVW f hW₂ g₂ F hF G).map φ x).val
          (openSystemShift07Q9 S hVW f hW₂ + e)) =
      (sourceSheaf07Q9 S f F).val.map (((openSystem07Q9 (overSituation S f) hV hW₂
        (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂).map φ.op).app e).op
        (AdicLevelCone07Q9.levelMap _ _ _ _
          (sourceTowerMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n)
          (sourceTowerMap07Q9_eq_zero S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n) e
          (x.val (openSystemShift07Q9 S hVW f hW₂ + e))) := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x.val (openSystemShift07Q9 S hVW f hW₂ + e))
  have hx : ((sourceModule07Q9 S hV hW hVW f hW₂ g₂ F hF G).map φ x).val
      (openSystemShift07Q9 S hVW f hW₂ + e) = Submodule.Quotient.mk
        ((openCosimplicialModule07Q9 S hV hW hVW F hF).pullbackTensorMap07Q9 G φ y) := by
    change adicQuotientMap _ _ _ (x.val _) = _
    rw [← hy]
    rfl
  rw [hx, ← hy]
  exact sourceLevelMap07Q9_simplicial S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG φ e y

/-- The abelian sheaf underlying `ℱ' = f_cris^*ℱ`. -/
abbrev sourceAbelianSheaf07Q9 : Sheaf (smallTopology (overSituation S f)) AddCommGrpCat.{u + 1} :=
  (toAbelianSheaf (overSituation S f)).obj (sourceSheaf07Q9 S f F)

/-- The Čech system of `f⁻¹(W)` for the presentation `g₂`. -/
abbrev sourceSystem07Q9 : SimplicialObject (ℕ ⥤ CrystallineThickening (overSituation S f)) :=
  openSystem07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f) g₂ hg₂

/-- **The cosimplicial module `M'(•)` is the cosimplicial module of sections of `ℱ'` over the Čech
system of `f⁻¹(W)`**, as an isomorphism of cosimplicial abelian groups. -/
def sourceCarrierSectionsIso07Q9 :
    (sourceModule07Q9 S hV hW hVW f hW₂ g₂ F hF G).carrierCosimplicialSmall ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      cosimplicialSections (sourceSystem07Q9 S hV hVW f hW₂ g₂ hg₂)
        (sourceAbelianSheaf07Q9 S f F).obj :=
  NatIso.ofComponents
    (fun n ↦ (sourceSectionsLimitIso07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n.len).symm)
    (fun {n m} φ ↦ by
      refine limit.hom_ext fun e ↦ AddCommGrpCat.ext fun x ↦ ?_
      change ConcreteCategory.hom (limit.π (sourceTower07Q9 S hV hVW f hW₂ g₂ hg₂ F m.len) e)
          (ConcreteCategory.hom
            (sourceSectionsLimitIso07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG m.len).inv
            (ULift.up ((sourceModule07Q9 S hV hW hVW f hW₂ g₂ F hF G).map φ x.down))) =
        ConcreteCategory.hom (limit.π (sourceTower07Q9 S hV hVW f hW₂ g₂ hg₂ F m.len) e)
          (ConcreteCategory.hom (limMap ((sectionSystem (sourceSystem07Q9 S hV hVW f hW₂ g₂ hg₂)
            (sourceAbelianSheaf07Q9 S f F).obj).map φ))
            (ConcreteCategory.hom
              (sourceSectionsLimitIso07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n.len).inv x))
      rw [sourceSectionsLimitIso07Q9_inv_π_apply]
      have hl := ConcreteCategory.congr_hom (limMap_π ((sectionSystem (sourceSystem07Q9 S hV hVW f
        hW₂ g₂ hg₂) (sourceAbelianSheaf07Q9 S f F).obj).map φ) e)
        (ConcreteCategory.hom
          (sourceSectionsLimitIso07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n.len).inv x)
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hl
      refine (levelMap_sourceModule07Q9_map S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG
        (n := n.len) (m := m.len) φ e.unop x.down).trans (Eq.trans ?_ hl.symm)
      exact congrArg (fun z ↦ ConcreteCategory.hom (((sectionSystem (sourceSystem07Q9 S hV hVW f
        hW₂ g₂ hg₂) (sourceAbelianSheaf07Q9 S f F).obj).map φ).app e) z)
        (sourceSectionsLimitIso07Q9_inv_π_apply S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n.len
          e.unop x).symm)

/-- **The Čech sections of `ℱ' = f_cris^*ℱ` over the system of `f⁻¹(W)` are the Moore complex of
the base change `M'(•)` of the cosimplicial module of `ℱ|_W` along `G`**, lifted to the universe of
the crystalline cohomology. -/
def sourceSectionsMooreIso07Q9 :
    sectionsComplex (sourceSystem07Q9 S hV hVW f hW₂ g₂ hg₂)
        (sourceAbelianSheaf07Q9 S f F).obj ≅
      (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
          (sourceModule07Q9 S hV hW hVW f hW₂ g₂ F hF G).carrierCosimplicial) :=
  ((Stacks.CechPushforward.alternatingCofaceMapComplexCompMapHomologicalComplexIso
      AddCommGrpCat.uliftFunctor.{u + 1, u}).app
        (sourceModule07Q9 S hV hW hVW f hW₂ g₂ F hF G).carrierCosimplicial ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u + 1}).mapIso
      (Functor.isoWhiskerLeft
          (sourceModule07Q9 S hV hW hVW f hW₂ g₂ F hF G).carrierCosimplicialSmall
          addCommGrpUliftFunctorCompIso ≪≫
        sourceCarrierSectionsIso07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG)).symm

/-- The level maps of the image of a compatible family under `sourceSectionsLimitIso07Q9` are
the components of the family. -/
theorem levelMap_sourceSectionsLimitIso07Q9_hom (n e : ℕ)
    (y : ↑(limit (sourceTower07Q9 S hV hVW f hW₂ g₂ hg₂ F n))) :
    AdicLevelCone07Q9.levelMap _ _ _ _
        (sourceTowerMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n)
        (sourceTowerMap07Q9_eq_zero S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n) e
        ((ConcreteCategory.hom (sourceSectionsLimitIso07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF
          G hG n).hom y).down.val (openSystemShift07Q9 S hVW f hW₂ + e)) =
      ConcreteCategory.hom (limit.π (sourceTower07Q9 S hV hVW f hW₂ g₂ hg₂ F n) (op e)) y :=
  ConcreteCategory.congr_hom (IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _)
    (sourceConeIsLimit07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n) (op e)) y

/-- **`sourceSectionsMooreIso07Q9` on elements**: the image of a compatible family of sections in
the level `e` is the component of the family at `e`. -/
theorem levelMap_sourceSectionsMooreIso07Q9_hom (n e : ℕ)
    (y : ↑((sectionsComplex (sourceSystem07Q9 S hV hVW f hW₂ g₂ hg₂)
        (sourceAbelianSheaf07Q9 S f F).obj).X n)) :
    AdicLevelCone07Q9.levelMap _ _ _ _
        (sourceTowerMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n)
        (sourceTowerMap07Q9_eq_zero S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n) e
        ((ConcreteCategory.hom ((sourceSectionsMooreIso07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF
          G hG).hom.f n) y).down.down.val (openSystemShift07Q9 S hVW f hW₂ + e)) =
      ConcreteCategory.hom (limit.π (sourceTower07Q9 S hV hVW f hW₂ g₂ hg₂ F n) (op e)) y :=
  levelMap_sourceSectionsLimitIso07Q9_hom S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e y

/-! #### The square -/

/-- The morphism of Čech systems over `f` from the system of `f⁻¹(W)` to the system of `W`. -/
abbrev sourceCechSystemHom07Q9 :=
  openCechSystemHom07Q9 S hV hW hVW (canonicalPresentation _)
    (canonicalPresentation_surjective _) f hW₂ g₂ hg₂ r hr

/-- The module unit `ℱ ⟶ f_{cris, *}f_cris^*ℱ` on underlying abelian sheaves. -/
abbrev sourceUnit07Q9 :=
  crisModuleUnit (overSituation S f) S (𝟙 S.S) f (overSituation_compat S f) ((moduleULift S).obj F)

/-- **The Čech pullback of the module unit on the levels**: the component at the level `e` of the
image of a compatible family `z` of sections of `ℱ` over the system of `W` is the restriction of
the component of `z` at the level `e + N'` along `τ n e`. -/
theorem π_sectionsMap_sourceUnit07Q9 (n e : ℕ)
    (z : ↑((sectionsComplex (openSystem07Q9 S hV hW hVW (canonicalPresentation _)
      (canonicalPresentation_surjective _)) (abelianSheaf F).obj).X n)) :
    ConcreteCategory.hom (limit.π (sourceTower07Q9 S hV hVW f hW₂ g₂ hg₂ F n) (op e))
        (ConcreteCategory.hom
          (((sourceCechSystemHom07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr).sectionsMap
            (sourceUnit07Q9 S f F)).f n) z) =
      sourceRestrict07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n e
        (ConcreteCategory.hom ((openSectionsMooreIso07Q9 S hV hW hVW F hF).hom.f n)
          z).down.down := by
  have h1 := ConcreteCategory.congr_hom ((sourceCechSystemHom07Q9 S hV hW hVW f hW₂ g₂ hg₂ r
    hr).app_π (sourceAbelianSheaf07Q9 S f F) ⦋n⦌ e)
    (ConcreteCategory.hom (((cosimplicialSectionsFunctor (openSystem07Q9 S hV hW hVW
      (canonicalPresentation _) (canonicalPresentation_surjective _))).map
        (sourceUnit07Q9 S f F).hom).app ⦋n⦌) z)
  have h2 := ConcreteCategory.congr_hom (levelLimitFunctor_map_π ((openSystem07Q9 S hV hW hVW
    (canonicalPresentation _) (canonicalPresentation_surjective _)).obj (op ⦋n⦌))
    (sourceUnit07Q9 S f F).hom (op (e + openSystemShift07Q9 S hVW f hW₂))) z
  refine h1.trans ((ConcreteCategory.comp_apply _ _ _).trans ?_)
  refine (congrArg (ConcreteCategory.hom (crisDirectImageEval (overSituation S f) S (𝟙 S.S) f
    (overSituation_compat S f) ((sourceCechSystemHom07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr).τ ⦋n⦌
      e) (sourceAbelianSheaf07Q9 S f F)))
    (((ConcreteCategory.comp_apply _ _ _).symm.trans h2).trans
      (ConcreteCategory.comp_apply _ _ _))).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).symm.trans ?_
  refine (crisDirectImageEval_crisModuleUnit07Q9 (S := overSituation S f) (S' := S) (𝟙 S.S) f
    (overSituation_compat S f) F _ _).trans ?_
  unfold sourceRestrict07Q9
  rw [wholeSpaceSectionsVal_openSectionsMooreIso07Q9_hom]
  rfl

/-- **The inverse of `sourceSectionsMooreIso07Q9` on elements**: the component at the level `e` of
the family attached to an element of `M'(n)` is its image under the level map. -/
theorem π_sourceSectionsMooreIso07Q9_inv (n e : ℕ)
    (w : ↑(((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
          (sourceModule07Q9 S hV hW hVW f hW₂ g₂ F hF G).carrierCosimplicial)).X n)) :
    ConcreteCategory.hom (limit.π (sourceTower07Q9 S hV hVW f hW₂ g₂ hg₂ F n) (op e))
        (ConcreteCategory.hom ((sourceSectionsMooreIso07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF
          G hG).inv.f n) w) =
      AdicLevelCone07Q9.levelMap _ _ _ _
        (sourceTowerMap07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n)
        (sourceTowerMap07Q9_eq_zero S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n) e
        (w.down.down.val (openSystemShift07Q9 S hVW f hW₂ + e)) :=
  sourceSectionsLimitIso07Q9_inv_π_apply S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e
    (ULift.up w.down.down)

/-- **The square of [Stacks, Tag 07Q9] on Čech sections over `W`**: the Čech pullback of the module
unit `ℱ ⟶ f_{cris, *}f_cris^*ℱ`, read through `sourceSectionsMooreIso07Q9` and
`openSectionsMooreIso07Q9`, is the Moore complex map of the morphism of cosimplicial modules
`M(•) ⟶ M'(•)`, `m ↦ 1 ⊗ m`. -/
theorem sectionsMap_sourceSectionsMooreIso07Q9 :
    (sourceCechSystemHom07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr).sectionsMap
        (sourceUnit07Q9 S f F) ≫
        (sourceSectionsMooreIso07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG).hom =
      (openSectionsMooreIso07Q9 S hV hW hVW F hF).hom ≫
        (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).map
            (Functor.whiskerRight
              ((openCosimplicialModule07Q9 S hV hW hVW F hF).pullbackCarrierMapSmall07Q9 G)
              AddCommGrpCat.uliftFunctor)) := by
  refine (Iso.eq_comp_inv _).mp ?_
  refine HomologicalComplex.hom_ext _ _ fun n ↦ limit.hom_ext fun e ↦ AddCommGrpCat.ext fun z ↦ ?_
  refine (π_sectionsMap_sourceUnit07Q9 S hV hW hVW f hW₂ g₂ hg₂ r hr F hF n e.unop z).trans ?_
  refine Eq.trans ?_ (π_sourceSectionsMooreIso07Q9_inv S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG
    n e.unop _).symm
  exact (sourceLevelMap07Q9_one_tmul S hV hW hVW f hW₂ g₂ hg₂ r hr F hF G hG n e.unop _).symm

end Source

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
