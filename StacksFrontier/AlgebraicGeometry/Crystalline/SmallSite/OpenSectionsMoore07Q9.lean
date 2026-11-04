module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.WholeSpaceColumnZeroSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsQuasiCoherentToPairs
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenCechSystem07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentOfCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SheafCrystal

/-!
# The Čech sections over an affine open as the Moore complex of `M(•)`

Fix a global crystalline situation `(p, (S, I, γ), X)`, affine opens `V ⊆ S` and `W ⊆ X` with `W`
mapping into `V`, and a crystal in quasi-coherent `𝒪_{X/S}`-modules `F`.  The complex of
sections of `F` over the Čech system `openSystem07Q9` of `W` (for the tautological presentation of
`Γ(W)` over `Γ(V)`) is identified with the Moore complex of the cosimplicial module `M(•)` of
[Stacks, Tag 07LG] of the restriction of `F` to `Cris(W/S|_V)`, for the restricted situation
`(p, S|_V, W)`.

## Main definitions

* `sheafComparisonOfNatTrans07Q9` — the sheaf-level comparison morphism of a natural
  transformation, the generic form of `CohomologyRestriction.moduleComparisonSheaf`.
* `restrictCrystal07Q9` — the restriction of a quasi-coherent crystal to `Cris(W/S|_V)`, as a
  quasi-coherent crystal.
* `openCosimplicialModule07Q9` — the cosimplicial module `M(•)` of that restriction.
* `openSectionsMooreIso07Q9` — the complex of sections of `F` over `openSystem07Q9` is the lifted
  Moore complex of `M(•)`.

## Main results

* `isSheafCrystal_smallExtendSheafRestriction` — the restriction of a crystal is a crystal.
* `isQuasiCoherentCrystal_smallExtendSheafRestriction` — the restriction of a quasi-coherent
  crystal is a quasi-coherent crystal.
* `openSectionsMooreIso07Q9_inv_π`, `wholeSpaceSectionsVal_openSectionsMooreIso07Q9_hom` — the
  identification on elements.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
-/

@[expose] public section

universe v₃ v₄ u₃ u₄ u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

section Generic

variable {C₁ C₂ : Type u} [SmallCategory C₁] [SmallCategory C₂]
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂)
  {D : Type u₃} [Category.{v₃} D] {E : Type u₄} [Category.{v₄} E]

/-- The sheaf of rings `L^* R` on a site, for a functor `L` into a category carrying a presheaf
of rings `R` such that the composite is a sheaf. -/
abbrev sheafRingOf07Q9 (L : C₂ ⥤ D) (R : Dᵒᵖ ⥤ RingCat.{u})
    (h : Presheaf.IsSheaf J₂ (L.op ⋙ R)) : Sheaf J₂ RingCat.{u} :=
  ⟨L.op ⋙ R, h⟩

/-- The morphism of sheaves of rings of a natural transformation `η : P ⋙ L_A ⟶ L_B`. -/
abbrev sheafRingMapOf07Q9 {P : C₁ ⥤ C₂} [P.IsContinuous J₁ J₂] {LA : C₂ ⥤ D} {LB : C₁ ⥤ D}
    (η : P ⋙ LA ⟶ LB) (R : Dᵒᵖ ⥤ RingCat.{u}) (hA : Presheaf.IsSheaf J₂ (LA.op ⋙ R))
    (hB : Presheaf.IsSheaf J₁ (LB.op ⋙ R)) :
    sheafRingOf07Q9 J₁ LB R hB ⟶
      (P.sheafPushforwardContinuous RingCat.{u} J₁ J₂).obj (sheafRingOf07Q9 J₂ LA R hA) :=
  ⟨Functor.whiskerRight (NatTrans.op η) R⟩

/-- The sheaf of modules `L^* M` over `L^* R`. -/
abbrev sheafModuleOf07Q9 (L : C₂ ⥤ D) (R : Dᵒᵖ ⥤ RingCat.{u})
    (h : Presheaf.IsSheaf J₂ (L.op ⋙ R)) (M : PresheafOfModules.{u} R)
    (hM : Presheaf.IsSheaf J₂ ((PresheafOfModules.pushforward₀ L R).obj M).presheaf) :
    SheafOfModules.{u} (sheafRingOf07Q9 J₂ L R h) :=
  ⟨(PresheafOfModules.pushforward₀ L R).obj M, hM⟩

/-- **The sheaf-level comparison morphism of a natural transformation**: the adjoint transpose,
along the adjunction between pullback and pushforward of sheaves of modules, of the `f`-map
`PresheafOfModules.pushforwardOfNatTrans`. -/
def sheafComparisonOfNatTrans07Q9 {P : C₁ ⥤ C₂} [P.IsContinuous J₁ J₂] {LA : C₂ ⥤ D}
    {LB : C₁ ⥤ D} (η : P ⋙ LA ⟶ LB) (R : Dᵒᵖ ⥤ RingCat.{u})
    (hA : Presheaf.IsSheaf J₂ (LA.op ⋙ R)) (hB : Presheaf.IsSheaf J₁ (LB.op ⋙ R))
    [(SheafOfModules.pushforward.{u} (sheafRingMapOf07Q9 J₁ J₂ η R hA hB)).IsRightAdjoint]
    (M : PresheafOfModules.{u} R)
    (hMA : Presheaf.IsSheaf J₂ ((PresheafOfModules.pushforward₀ LA R).obj M).presheaf)
    (hMB : Presheaf.IsSheaf J₁ ((PresheafOfModules.pushforward₀ LB R).obj M).presheaf) :
    (SheafOfModules.pullback.{u} (sheafRingMapOf07Q9 J₁ J₂ η R hA hB)).obj
        (sheafModuleOf07Q9 J₁ LB R hB M hMB) ⟶ sheafModuleOf07Q9 J₂ LA R hA M hMA :=
  ((SheafOfModules.pullbackPushforwardAdjunction.{u}
      (sheafRingMapOf07Q9 J₁ J₂ η R hA hB)).homEquiv _ _).symm
    ⟨PresheafOfModules.pushforwardOfNatTrans η R M⟩

/-- Precomposing the coefficients with a functor `G` preserves invertibility of the sheaf-level
comparison morphism: if the comparison morphism of a natural transformation `η'` identified with
`Functor.whiskerRight η G` is an isomorphism, then so is that of `η` over the coefficients
`G.op ⋙ R`. -/
theorem isIso_sheafComparisonOfNatTrans07Q9_pushforward₀ {P : C₁ ⥤ C₂} [P.IsContinuous J₁ J₂]
    {LA : C₂ ⥤ D} {LB : C₁ ⥤ D} (η : P ⋙ LA ⟶ LB) (G : D ⥤ E) (R : Eᵒᵖ ⥤ RingCat.{u})
    (M : PresheafOfModules.{u} R) {LA' : C₂ ⥤ E} {LB' : C₁ ⥤ E} {η' : P ⋙ LA' ⟶ LB'}
    (hA : LA ⋙ G = LA') (hB : LB ⋙ G = LB') (hη : HEq (Functor.whiskerRight η G) η')
    (sA : Presheaf.IsSheaf J₂ (LA.op ⋙ G.op ⋙ R)) (sB : Presheaf.IsSheaf J₁ (LB.op ⋙ G.op ⋙ R))
    [(SheafOfModules.pushforward.{u} (sheafRingMapOf07Q9 J₁ J₂ η (G.op ⋙ R) sA sB)).IsRightAdjoint]
    (sMA : Presheaf.IsSheaf J₂ ((PresheafOfModules.pushforward₀ LA (G.op ⋙ R)).obj
      ((PresheafOfModules.pushforward₀ G R).obj M)).presheaf)
    (sMB : Presheaf.IsSheaf J₁ ((PresheafOfModules.pushforward₀ LB (G.op ⋙ R)).obj
      ((PresheafOfModules.pushforward₀ G R).obj M)).presheaf)
    (sA' : Presheaf.IsSheaf J₂ (LA'.op ⋙ R)) (sB' : Presheaf.IsSheaf J₁ (LB'.op ⋙ R))
    [(SheafOfModules.pushforward.{u} (sheafRingMapOf07Q9 J₁ J₂ η' R sA' sB')).IsRightAdjoint]
    (sMA' : Presheaf.IsSheaf J₂ ((PresheafOfModules.pushforward₀ LA' R).obj M).presheaf)
    (sMB' : Presheaf.IsSheaf J₁ ((PresheafOfModules.pushforward₀ LB' R).obj M).presheaf)
    (h : IsIso (sheafComparisonOfNatTrans07Q9 J₁ J₂ η' R sA' sB' M sMA' sMB')) :
    IsIso (sheafComparisonOfNatTrans07Q9 J₁ J₂ η (G.op ⋙ R) sA sB
      ((PresheafOfModules.pushforward₀ G R).obj M) sMA sMB) := by
  subst hA hB
  obtain rfl : Functor.whiskerRight η G = η' := eq_of_heq hη
  exact h

end Generic

section Restrict

variable (S : GlobalCrystallineSituation.{u}) (V : S.S.scheme.Opens) (W : S.X.Opens)
  (hVW : W ≤ sourceToBase S ⁻¹ᵁ V)

/-- **The restriction to `Cris(W/S|_V)` of a crystal in `𝒪_{X/S}`-modules is a crystal.** -/
theorem isSheafCrystal_smallExtendSheafRestriction (F : SheafOfModules.{u} (structureSheaf S))
    (hF : IsSheafCrystal F) : IsSheafCrystal (smallExtendSheafRestriction S V W hVW F) :=
  fun A B g => isIso_sheafComparisonOfNatTrans07Q9_pushforward₀ _ _
    (CohomologyRestriction.CrystallineThickening.restrictOpenFunctorMap g)
    (smallExtend S V W hVW) (crisRing S) F.val
    (LA' := CrystallineThickening.restrictOpenFunctor ((smallExtend S V W hVW).obj A))
    (LB' := CrystallineThickening.restrictOpenFunctor ((smallExtend S V W hVW).obj B))
    (η' := CohomologyRestriction.CrystallineThickening.restrictOpenFunctorMap
      ((smallExtend S V W hVW).map g))
    (restrictOpenFunctor_comp_smallExtend S V W hVW A)
    (restrictOpenFunctor_comp_smallExtend S V W hVW B)
    (heq_whiskerRight_restrictOpenFunctorMap S V W hVW g) _ _ _ _ _ _ _ _
    (hF _ _ ((smallExtend S V W hVW).map g))

/-- **The restriction to `Cris(W/S|_V)` of a crystal in quasi-coherent `𝒪_{X/S}`-modules is a
crystal in quasi-coherent modules.** -/
theorem isQuasiCoherentCrystal_smallExtendSheafRestriction
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsQuasiCoherentCrystal S F) :
    IsQuasiCoherentCrystal (restrict S V W hVW) (smallExtendSheafRestriction S V W hVW F) :=
  have hcrys := isSheafCrystal_smallExtendSheafRestriction S V W hVW F hF.2
  ⟨(isQuasicoherentOnSite_iff _).2
    ⟨isLocallyQuasiCoherent_smallExtendSheafRestriction S V W hVW F
      (isLocallyQuasiCoherent_of_isQuasicoherentOnSite F hF.1), hcrys⟩, hcrys⟩

/-- **The restriction of a crystal in quasi-coherent modules to a pair of opens**, as an object of
the category of crystals in quasi-coherent modules of the restricted situation. -/
def restrictCrystal07Q9 (F : SheafOfModules.{u} (structureSheaf S))
    (hF : IsQuasiCoherentCrystal S F) : QuasiCoherentCrystal (restrict S V W hVW) :=
  ⟨smallExtendSheafRestriction S V W hVW F,
    isQuasiCoherentCrystal_smallExtendSheafRestriction S V W hVW F hF⟩

/-- The underlying sheaf of `restrictCrystal07Q9` is `smallExtendSheafRestriction`. -/
@[simp] theorem restrictCrystal07Q9_obj (F : SheafOfModules.{u} (structureSheaf S))
    (hF : IsQuasiCoherentCrystal S F) :
    (restrictCrystal07Q9 S V W hVW F hF).obj = smallExtendSheafRestriction S V W hVW F := rfl

end Restrict

/-! ### The Čech sections over `W` as the Moore complex of `M(•)` -/

section Open

variable (S : GlobalCrystallineSituation.{u}) {V : S.S.scheme.Opens} {W : S.X.Opens}
  (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hVW : W ≤ sourceToBase S ⁻¹ᵁ V)
  (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsQuasiCoherentCrystal S F)

/-- **The cosimplicial module `M(•)` of a quasi-coherent crystal over an affine open `W`**: the
cosimplicial module `M(b) = lim_e Γ((W, T(b)_e, δ(b)), ℱ|_W)` of [Stacks, Tag 07LG] for the
restriction of `F` to the situation `(Γ(V), Γ(W))` of the pair of affine opens, over the completed
cosimplicial envelope of the tautological presentation of `Γ(W)` over `Γ(V)`. -/
abbrev openCosimplicialModule07Q9 :=
  haveI := isAffine_restrictX07Q9 S hW hVW
  haveI := isAffine_restrictS07Q9 S hV hVW
  wholeSpaceCosimplicialModule (isNilpotent_prime_openSituation07Q9 S hW hVW)
    (restrictCrystal07Q9 S V W hVW F hF)

/-- **The Čech sections of `F` over the system of the affine open `W` are the Moore complex of the
cosimplicial module `M(•)` of the restriction of `F` to `W`**, lifted to the universe of the
crystalline cohomology. -/
def openSectionsMooreIso07Q9 :
    sectionsComplex (openSystem07Q9 S hV hW hVW
        (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
        (canonicalPresentation_surjective _)) (abelianSheaf F).obj ≅
      (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
          (openCosimplicialModule07Q9 S hV hW hVW F hF).carrierCosimplicial) :=
  haveI := isAffine_restrictX07Q9 S hW hVW
  haveI := isAffine_restrictS07Q9 S hV hVW
  (wholeSpaceMooreComplexSectionsIso (isNilpotent_prime_openSituation07Q9 S hW hVW)
    (restrictCrystal07Q9 S V W hVW F hF)).symm

/-- **The inverse of `openSectionsMooreIso07Q9` on elements**: an element `m` of `M(n)` goes to
the compatible family of sections whose component at the level `e` is the component
`wholeSpaceSectionsVal m e` of `m`. -/
theorem openSectionsMooreIso07Q9_inv_π (n : ℕ)
    (m : (openCosimplicialModule07Q9 S hV hW hVW F hF).carrier n) (e : ℕ) :
    ConcreteCategory.hom (limit.π ((sectionSystem (openSystem07Q9 S hV hW hVW
        (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
        (canonicalPresentation_surjective _)) (abelianSheaf F).obj).obj ⦋n⦌) (op e))
      (ConcreteCategory.hom ((openSectionsMooreIso07Q9 S hV hW hVW F hF).inv.f n)
        (ULift.up (ULift.up m))) =
      haveI := isAffine_restrictX07Q9 S hW hVW
      haveI := isAffine_restrictS07Q9 S hV hVW
      ULift.up (wholeSpaceSectionsVal (isNilpotent_prime_openSituation07Q9 S hW hVW)
        (restrictCrystal07Q9 S V W hVW F hF) m e) :=
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  wholeSpaceSectionsLimitIso_inv_π (isNilpotent_prime_openSituation07Q9 S hW hVW)
    (restrictCrystal07Q9 S V W hVW F hF) ⦋n⦌ (ULift.up m) e

/-- **`openSectionsMooreIso07Q9` on elements**: the component at the level `e` of the element of
`M(n)` attached to a compatible family of sections is the component of the family at `e`. -/
theorem wholeSpaceSectionsVal_openSectionsMooreIso07Q9_hom (n : ℕ)
    (z : ↑((sectionsComplex (openSystem07Q9 S hV hW hVW
        (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
        (canonicalPresentation_surjective _)) (abelianSheaf F).obj).X n)) (e : ℕ) :
    haveI := isAffine_restrictX07Q9 S hW hVW
    haveI := isAffine_restrictS07Q9 S hV hVW
    wholeSpaceSectionsVal (isNilpotent_prime_openSituation07Q9 S hW hVW)
        (restrictCrystal07Q9 S V W hVW F hF)
        (ConcreteCategory.hom ((openSectionsMooreIso07Q9 S hV hW hVW F hF).hom.f n) z).down.down
        e =
      ULift.down (ConcreteCategory.hom (limit.π ((sectionSystem (openSystem07Q9 S hV hW hVW
        (canonicalPresentation (openAffineSituation07Q9 S hW hVW))
        (canonicalPresentation_surjective _)) (abelianSheaf F).obj).obj ⦋n⦌) (op e)) z) :=
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  wholeSpaceSectionsVal_limitIso_hom (isNilpotent_prime_openSituation07Q9 S hW hVW)
    (restrictCrystal07Q9 S V W hVW F hF) ⦋n⦌ z e

end Open

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
