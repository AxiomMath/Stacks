module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictSheafification
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.LocallyQuasicoherent

/-!
# The hypotheses of [Stacks, Tag 07JN] restrict to a restricted situation

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], an open `W` of `S`
and an open `V` of `X` whose image lies in `W`.  `Crystalline.GlobalCrystallineSituation.restrict`
is the restricted situation `(p, S|_W, V)` and
`Crystalline.GlobalCrystallineSituation.smallExtend` is change of divided power base
`Cris(V/S|_W) ⥤ Cris(X/S)` along the two open immersions, [Stacks, Tag 07KL].

A sheaf of `𝒪_{X/S}`-modules satisfying conditions (1) and (2) of [Stacks, Tag 07JN] — locally
quasi-coherent, [Stacks, Tag 07IS], with surjective comparison maps along closed immersions,
[Stacks, Tag 07IT] — restricts to a sheaf of `𝒪_{V/S|_W}`-modules satisfying them, whose
underlying presheaf of modules is the restriction of the given one.

## Main definitions

Apart from `PresheafOfModules.comparisonOfNatTrans`, everything lives in the namespace
`Crystalline.GlobalCrystallineSituation.SmallSite`.

* `smallExtendSheafRestriction` — the restriction along `smallExtend` of a sheaf of
  `𝒪_{X/S}`-modules on `Cris(X/S)` to a sheaf of `𝒪_{V/S|_W}`-modules on `Cris(V/S|_W)`.
* `PresheafOfModules.comparisonOfNatTrans` — the comparison morphism of [Stacks, Tag 07IP] for a
  natural transformation `η : P ⋙ L_A ⟶ L_B` of functors into a category carrying a presheaf of
  rings `R`: the adjoint transpose of `PresheafOfModules.pushforwardOfNatTrans η R M`.

## Main results

* `isLocallyQuasiCoherent_smallExtendSheafRestriction` — condition (1) of [Stacks, Tag 07JN]
  passes to the restricted situation.
* `isSurjectiveComparison_smallExtendSheafRestriction` — condition (2) of [Stacks, Tag 07JN]
  passes to the restricted situation.
* `exists_smallExtendRestriction_of_vanishingHypotheses` — a sheaf of `𝒪_{X/S}`-modules
  satisfying both conditions restricts to a sheaf of `𝒪_{V/S|_W}`-modules satisfying both, whose
  underlying presheaf of modules is the restriction of the given one.

## Implementation notes

Every identification here is a definitional equality between objects over different global
crystalline situations. For the comparison maps it is stated once, generically, as
`PresheafOfModules.comparisonOfNatTrans_pushforward₀`, where both sides are built from the same
variables, and instantiated through
`PresheafOfModules.isLocallySurjective_comparisonOfNatTrans_pushforward₀`.

## References

* [Stacks Project, Tag 07IP](https://stacks.math.columbia.edu/tag/07IP)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/
@[expose] public section

universe v₃ v₄ u₃ u₄ u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace PresheafOfModules

section

variable {C₁ C₂ : Type u} [SmallCategory C₁] [SmallCategory C₂] {D : Type u₃} [Category.{v₃} D]
  {E : Type u₄} [Category.{v₄} E]

/-- **The comparison morphism of a natural transformation**, [Stacks, Tag 07IP].  Let
`L_A : C₂ ⥤ D` and `L_B : C₁ ⥤ D` be functors into a category carrying a presheaf of rings `R`,
let `P : C₁ ⥤ C₂` and let `η : P ⋙ L_A ⟶ L_B`.  Precomposition with `L_A` and with `L_B` carries a
presheaf of `R`-modules `M` to presheaves of modules on `C₂` and on `C₁`, and `η` gives a map from
the second to the direct image of the first, `PresheafOfModules.pushforwardOfNatTrans`.  This is
its adjoint transpose, a map from the pullback along `η` of the presheaf of modules on `C₂` to the
one on `C₁`. -/
def comparisonOfNatTrans {P : C₁ ⥤ C₂} {LA : C₂ ⥤ D} {LB : C₁ ⥤ D} (η : P ⋙ LA ⟶ LB)
    (R : Dᵒᵖ ⥤ RingCat.{u}) (M : PresheafOfModules.{u} R) :
    (pullback (F := P) (Functor.whiskerRight (NatTrans.op η) R)).obj
        ((pushforward₀ LB R).obj M) ⟶
      (pushforward₀ LA R).obj M :=
  ((pullbackPushforwardAdjunction.{u} (F := P)
      (Functor.whiskerRight (NatTrans.op η) R)).homEquiv ((pushforward₀ LB R).obj M)
    ((pushforward₀ LA R).obj M)).symm (pushforwardOfNatTrans η R M)

/-- **The comparison morphism of a natural transformation is unchanged by precomposing the
coefficients with a functor**, on the nose: the comparison morphism of `η` for the presheaf of
modules obtained from `M` by precomposition with `G` is the comparison morphism of
`Functor.whiskerRight η G` for `M` itself. -/
theorem comparisonOfNatTrans_pushforward₀ {P : C₁ ⥤ C₂} {LA : C₂ ⥤ D} {LB : C₁ ⥤ D}
    (η : P ⋙ LA ⟶ LB) (G : D ⥤ E) (R : Eᵒᵖ ⥤ RingCat.{u}) (M : PresheafOfModules.{u} R) :
    comparisonOfNatTrans η (G.op ⋙ R) ((pushforward₀ G R).obj M) =
      comparisonOfNatTrans (LA := LA ⋙ G) (LB := LB ⋙ G) (Functor.whiskerRight η G) R M :=
  rfl

/-- The comparison morphism of `η` over coefficients precomposed with `G` is locally surjective if
the comparison morphism of a natural transformation identified with `Functor.whiskerRight η G` is
locally surjective. -/
theorem isLocallySurjective_comparisonOfNatTrans_pushforward₀ {P : C₁ ⥤ C₂} {LA : C₂ ⥤ D}
    {LB : C₁ ⥤ D} (η : P ⋙ LA ⟶ LB) (G : D ⥤ E) (R : Eᵒᵖ ⥤ RingCat.{u})
    (M : PresheafOfModules.{u} R) {LA' : C₂ ⥤ E} {LB' : C₁ ⥤ E} {η' : P ⋙ LA' ⟶ LB'}
    (hA : LA ⋙ G = LA') (hB : LB ⋙ G = LB')
    (hη : HEq (Functor.whiskerRight η G) η') (J : GrothendieckTopology C₂)
    (hs : Presheaf.IsLocallySurjective J
      ((toPresheaf (LA'.op ⋙ R)).map (comparisonOfNatTrans η' R M))) :
    Presheaf.IsLocallySurjective J
      ((toPresheaf (LA.op ⋙ (G.op ⋙ R))).map
        (comparisonOfNatTrans η (G.op ⋙ R) ((pushforward₀ G R).obj M))) := by
  subst hA hB
  obtain rfl : Functor.whiskerRight η G = η' := eq_of_heq hη
  exact hs

end

end PresheafOfModules

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-- **The comparison morphism of a morphism of `Cris(X/S)` is the generic comparison morphism of
the restrictions of that morphism to the opens of the ambient scheme of its target.** -/
theorem CohomologyRestriction.moduleComparison_eq_comparisonOfNatTrans
    {S : GlobalCrystallineSituation.{u}} (M : PresheafOfModules.{u} (crisRing S))
    {A B : CrystallineThickening S} (g : A ⟶ B) :
    moduleComparison M g =
      PresheafOfModules.comparisonOfNatTrans (CrystallineThickening.restrictOpenFunctorMap g)
        (crisRing S) M :=
  rfl

variable (S : GlobalCrystallineSituation.{u}) (W : S.S.scheme.Opens) (V : S.X.Opens)
  (hVW : V ≤ sourceToBase S ⁻¹ᵁ W)

/-- **The restriction to `Cris(V/S|_W)` of a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)`**: its
sections over an object of the restricted site are the sections of the given sheaf over the
extension of that object, and it is a module over the structure sheaf of the restricted
site. -/
def smallExtendSheafRestriction (F : SheafOfModules.{u} (structureSheaf S)) :
    SheafOfModules.{u} (structureSheaf (restrict S W V hVW)) where
  val := (smallExtendModuleRestriction S W V hVW).obj
    (F.val : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat))
  isSheaf := (smallExtend S W V hVW).op_comp_isSheaf_of_isSheaf _ _ _ F.isSheaf

/-- **Restricting an object of `Cris(V/S|_W)` to the opens of its ambient scheme commutes with
change of divided power base**, on the nose: the extension of the restriction of `A` to an open
of its ambient scheme is the restriction of the extension of `A` to that same open. -/
theorem restrictOpenFunctor_comp_smallExtend (A : CrystallineThickening (restrict S W V hVW)) :
    CrystallineThickening.restrictOpenFunctor A ⋙ smallExtend S W V hVW =
      CrystallineThickening.restrictOpenFunctor ((smallExtend S W V hVW).obj A) :=
  rfl

/-- **Restricting a morphism of `Cris(V/S|_W)` over the opens of the ambient scheme of its target
commutes with change of divided power base**, as a heterogeneous equality of natural
transformations. -/
theorem heq_whiskerRight_restrictOpenFunctorMap
    {A B : CrystallineThickening (restrict S W V hVW)} (g : A ⟶ B) :
    HEq (Functor.whiskerRight
        (CohomologyRestriction.CrystallineThickening.restrictOpenFunctorMap g)
        (smallExtend S W V hVW))
      (CohomologyRestriction.CrystallineThickening.restrictOpenFunctorMap
        ((smallExtend S W V hVW).map g)) :=
  HEq.rfl

/-- **Condition (1) of [Stacks, Tag 07JN] passes to the restricted situation**: the restriction
along `smallExtend` of a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules is locally
quasi-coherent, [Stacks, Tag 07IS]. -/
theorem isLocallyQuasiCoherent_smallExtendSheafRestriction
    (F : SheafOfModules.{u} (structureSheaf S)) (hqc : IsLocallyQuasiCoherent F) :
    IsLocallyQuasiCoherent (smallExtendSheafRestriction S W V hVW F) :=
  fun A ↦ hqc ((smallExtend S W V hVW).obj A)

/-- **The comparison morphism of a morphism of `Cris(V/S|_W)` for a restricted sheaf is the
generic comparison morphism of the restrictions of that morphism, over the coefficients of the
given sheaf precomposed with `smallExtend`.** -/
theorem moduleComparison_smallExtendSheafRestriction (F : SheafOfModules.{u} (structureSheaf S))
    {A B : CrystallineThickening (restrict S W V hVW)} (g : A ⟶ B) :
    CohomologyRestriction.moduleComparison (smallExtendSheafRestriction S W V hVW F).val g =
      PresheafOfModules.comparisonOfNatTrans
        (CohomologyRestriction.CrystallineThickening.restrictOpenFunctorMap g)
        ((smallExtend S W V hVW).op ⋙ crisRing S)
        ((PresheafOfModules.pushforward₀ (smallExtend S W V hVW) (crisRing S)).obj F.val) :=
  rfl

/-- **Condition (2) of [Stacks, Tag 07JN] passes to the restricted situation**: the restriction
along `smallExtend` of a sheaf of `𝒪_{X/S}`-modules with surjective closed immersion comparison
maps has surjective closed immersion comparison maps, [Stacks, Tag 07IT]. -/
theorem isSurjectiveComparison_smallExtendSheafRestriction
    (F : SheafOfModules.{u} (structureSheaf S))
    (hsurj : CohomologyRestriction.IsSurjectiveComparison F.val) :
    CohomologyRestriction.IsSurjectiveComparison
      (smallExtendSheafRestriction S W V hVW F).val := by
  intro A B g hg
  exact PresheafOfModules.isLocallySurjective_comparisonOfNatTrans_pushforward₀
    (CohomologyRestriction.CrystallineThickening.restrictOpenFunctorMap g)
    (smallExtend S W V hVW) (crisRing S) F.val
    (LA' := CrystallineThickening.restrictOpenFunctor ((smallExtend S W V hVW).obj A))
    (LB' := CrystallineThickening.restrictOpenFunctor ((smallExtend S W V hVW).obj B))
    (η' := CohomologyRestriction.CrystallineThickening.restrictOpenFunctorMap
      ((smallExtend S W V hVW).map g))
    (restrictOpenFunctor_comp_smallExtend S W V hVW A)
    (restrictOpenFunctor_comp_smallExtend S W V hVW B)
    (heq_whiskerRight_restrictOpenFunctorMap S W V hVW g) _
    (hsurj ((smallExtend S W V hVW).map g) hg)

/-- **A sheaf of `𝒪_{X/S}`-modules satisfying conditions (1) and (2) of [Stacks, Tag 07JN]
restricts to a sheaf of `𝒪_{V/S|_W}`-modules satisfying them, whose underlying presheaf of
modules is the restriction of the given one.** -/
theorem exists_smallExtendRestriction_of_vanishingHypotheses
    (F : SheafOfModules.{u} (structureSheaf S)) (hqc : IsLocallyQuasiCoherent F)
    (hsurj : CohomologyRestriction.IsSurjectiveComparison F.val) :
    ∃ F' : SheafOfModules.{u} (structureSheaf (restrict S W V hVW)),
      IsLocallyQuasiCoherent F' ∧
        CohomologyRestriction.IsSurjectiveComparison F'.val ∧
        Nonempty ((smallExtendModuleRestriction S W V hVW).obj
            (F.val : PresheafOfModules.{u}
              (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) ≅
          (F'.val : PresheafOfModules.{u}
            (structurePresheaf (restrict S W V hVW) ⋙ forget₂ CommRingCat RingCat))) :=
  ⟨smallExtendSheafRestriction S W V hVW F,
    isLocallyQuasiCoherent_smallExtendSheafRestriction S W V hVW F hqc,
    isSurjectiveComparison_smallExtendSheafRestriction S W V hVW F hsurj, ⟨Iso.refl _⟩⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end
