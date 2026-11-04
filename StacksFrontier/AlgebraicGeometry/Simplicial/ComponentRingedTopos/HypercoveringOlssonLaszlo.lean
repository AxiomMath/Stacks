module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringLocalSerreTotal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.OlssonLaszloSituation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyAlongAMorphismOfLocalizedSites
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfALocalizedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.ModuleCohomologyOverObjectVanishing
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumNaturality.SummandCohomology
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumNaturality.Exactness

/-!
# The two Olsson--Laszlo situations of Stacks 0DC7

Let `(C, O_C)` be a ringed site with a family `A_U` of weak Serre subcategories satisfying
conditions 0DC2, 0DC3 and 0DC4, and let `K` be a hypercovering. The proof of Stacks 0DC7
applies Stacks 0D7V to the augmentation `a : ((C/K)_total, O) ⟶ (C, O_C)`, whose assumptions (4)
and (5) are that `(C, O_C, A)` and `((C/K)_total, O, A_total)` satisfy the assumption of the
Olsson--Laszlo Situation 0D6R. This file constructs both situations.

* On `C` the data are those of condition 0DC4: the set `B`, the bounds `d_V` and the cofinal
  systems `Cov_V`. The vanishing `H^p(V_i, F) = 0` for `F` in `A` comes from the vanishing for
  `F|_V` in `A_V` that 0DC4 provides, since cohomology over `V_i` of `F` is cohomology over
  `V_i → V` of `F|_V` (Stacks 03F3).
* On the total site the source takes the objects `U/U_{n,i}` with `U` in `B`, with bound `d_U`
  and coverings `Cov_U`, read in the slice `C/U_{n,i}`. Cohomology over such an object of an
  `F` of `A_total` is cohomology over `U` of the component `F_{n,i}` (Stacks 0DBZ and 0DC0), and
  `F_{n,i}|_U` lies in `A_U` by 0DC2.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.baseOlssonLaszloSituation`: the situation on `C`.

## Main results

* `Stacks.Cohomology.isZero_moduleCohomology_iff_sections`: cohomology of a sheaf of modules over
  an object vanishes if and only if the cohomology of its underlying abelian sheaf does.
* `Stacks.Cohomology.isZero_moduleCohomology_pushforward_iff`: cohomology over `W` of the
  restriction of a sheaf of modules along a continuous functor `u` whose restriction functor of
  abelian sheaves is exact and preserves injectives is cohomology over `u W`.

## References

* [Stacks Project, Tag 0DC7](https://stacks.math.columbia.edu/tag/0DC7)
* [Stacks Project, Tag 0D6R](https://stacks.math.columbia.edu/tag/0D6R)
* [Stacks Project, Tag 0DC4](https://stacks.math.columbia.edu/tag/0DC4)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.SimplicialSiteSituation CategoryTheory.SimplicialSemiRepresentable
open Stacks.Cohomology.CohomologicalDescent Stacks.Cohomology

universe u

namespace Stacks.Cohomology

section Comparison

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} R)]

/-- **Cohomology of a sheaf of modules over an object vanishes exactly when the cohomology of its
underlying abelian sheaf does** (Stacks 03FD). Forgetting the module structure is exact and
faithful, evaluation followed by forgetting is sections of the underlying abelian sheaf, and
Stacks 03FD for sections over an object identifies the derived functors. -/
theorem isZero_moduleCohomology_iff_sections (U : C) (p : ℕ) (M : SheafOfModules.{u} R) :
    IsZero (moduleCohomology R U p M) ↔
      IsZero (((sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived p).obj
          ((SheafOfModules.toSheaf.{u} R).obj M)) := by
  let E : SheafOfModules.{u} R ⥤ ModuleCat.{u} (R.obj.obj (op U)) :=
    _root_.SheafOfModules.evaluation R (op U)
  let G := forget₂ (ModuleCat.{u} (R.obj.obj (op U))) AddCommGrpCat.{u}
  have hEadd : E.Additive := by
    dsimp [E, _root_.SheafOfModules.evaluation]
    infer_instance
  let Sec := (sheafSections J AddCommGrpCat.{u}).obj (op U)
  have hcomp : E ⋙ G ≅ SheafOfModules.toSheaf.{u} R ⋙ Sec := Iso.refl _
  have e : G.obj (moduleCohomology R U p M) ≅
      (Sec.rightDerived p).obj ((SheafOfModules.toSheaf.{u} R).obj M) :=
    rightDerivedExactPostcompositionIso E G M p ≪≫
      (rightDerivedIsoOfFunctorIso hcomp p).app M ≪≫
        (ModuleSheafCohomology.sectionsComparisonIso J R U p).app M
  exact ⟨fun h ↦ (G.map_isZero h).of_iso e.symm,
    fun h ↦ (IsZero.iff_id_eq_zero _).2 (G.map_injective ((h.of_iso e).eq_of_src _ _))⟩

end Comparison

section Pushforward

variable {𝒲 : Type u} [SmallCategory 𝒲] {𝒞 : Type u} [SmallCategory 𝒞]
  {JW : GrothendieckTopology 𝒲} {JC : GrothendieckTopology 𝒞}
  [HasSheafify JW AddCommGrpCat.{u}] [JW.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify JC AddCommGrpCat.{u}] [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (u : 𝒲 ⥤ 𝒞) [hu : u.IsContinuous JW JC]
  [hcol : PreservesFiniteColimits (u.sheafPushforwardContinuous AddCommGrpCat.{u} JW JC)]
  [hinj : (u.sheafPushforwardContinuous AddCommGrpCat.{u} JW JC).PreservesInjectiveObjects]
  {R : Sheaf JC RingCat.{u}} {S : Sheaf JW RingCat.{u}}
  [EnoughInjectives (SheafOfModules.{u} R)] [EnoughInjectives (SheafOfModules.{u} S)]
  (τ : S ⟶ (u.sheafPushforwardContinuous RingCat.{u} JW JC).obj R)

/-- **Cohomology of a restriction along a continuous functor.** If restriction of abelian sheaves
along `u` is exact and preserves injectives, then cohomology over `W` of the restriction of a
sheaf of modules `M` along `u` vanishes exactly when cohomology of `M` over `u W` does: on
underlying abelian sheaves both are cohomology of abelian sheaves, compared by Stacks 03YU. -/
theorem isZero_moduleCohomology_pushforward_iff (W : 𝒲) (p : ℕ) (M : SheafOfModules.{u} R) :
    IsZero (moduleCohomology S W p ((SheafOfModules.pushforward.{u} τ).obj M)) ↔
      IsZero (moduleCohomology R (u.obj W) p M) := by
  rw [isZero_moduleCohomology_iff_sections, isZero_moduleCohomology_iff_sections]
  exact Iso.isZero_iff ((SheafifiedHigherDirectImage.pushforwardRightDerivedSectionsIso
    AddCommGrpCat.{u} u p W).app ((SheafOfModules.toSheaf.{u} R).obj M))

end Pushforward

section RestrictScalars

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R R' : Sheaf J RingCat.{u}} [EnoughInjectives (SheafOfModules.{u} R)]
  [EnoughInjectives (SheafOfModules.{u} R')] (α : R ⟶ R')

/-- Restriction of scalars does not change the cohomology of a sheaf of modules over an object:
both are the cohomology of the same underlying abelian sheaf. -/
theorem isZero_moduleCohomology_restrictScalars_iff (U : C) (p : ℕ)
    (M : SheafOfModules.{u} R') :
    IsZero (moduleCohomology R U p ((SheafOfModules.restrictScalars α).obj M)) ↔
      IsZero (moduleCohomology R' U p M) := by
  rw [isZero_moduleCohomology_iff_sections, isZero_moduleCohomology_iff_sections]
  rfl

end RestrictScalars

section WeaklyInitial'

variable {𝒲 : Type u} [SmallCategory 𝒲] {𝒦 : Type u} [SmallCategory 𝒦]
  {JW : GrothendieckTopology 𝒲} {JK JK' : GrothendieckTopology 𝒦}
  [HasSheafify JK AddCommGrpCat.{u}]
  (s : 𝒲 ⥤ 𝒦) [hs : s.IsContinuous JW JK] [hs' : s.IsCocontinuous JW JK'] (h : JK' = JK)

include h in
/-- Restriction of abelian sheaves along a continuous and cocontinuous functor of small sites is
right exact. The cocontinuity may be given for a topology equal to the given one. -/
theorem preservesFiniteColimits_sheafPushforwardContinuous_of_eq :
    PreservesFiniteColimits (s.sheafPushforwardContinuous AddCommGrpCat.{u} JW JK) := by
  subst h
  exact SheafifiedHigherDirectImage.preservesFiniteColimits_pushforwardOfContinuous
    AddCommGrpCat.{u} s

/-- Restriction of abelian sheaves along a continuous functor of small sites whose comma
categories have weakly initial objects preserves injective objects: its left adjoint is exact
(Stacks 002X). -/
theorem preservesInjectiveObjects_sheafPushforwardContinuous_of_weaklyInitial
    (hw : ∀ (V : 𝒦) (x : StructuredArrow V s), ∃ W : StructuredArrow V s,
      (∀ {y : StructuredArrow V s}, (y ⟶ x) → Nonempty (W ⟶ y)) ∧
        ∀ {y : StructuredArrow V s} (q q' : W ⟶ y), q = q') :
    (s.sheafPushforwardContinuous AddCommGrpCat.{u} JW JK).PreservesInjectiveObjects := by
  have := Stacks.Sites.AbelianPullback.preservesMonomorphisms_sheafPullback_of_weaklyInitial s
    AddCommGrpCat.{u} JW JK hw
  exact SheafifiedHigherDirectImage.preservesInjectiveObjects_pushforwardOfContinuous
    AddCommGrpCat.{u} s

end WeaklyInitial'

end Stacks.Cohomology

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (J : Pretopology C)
  (OC : Sheaf J.toGrothendieck CommRingCat.{u})
  (T : LocalSerreFamily.{u} (pretopologyRingedSite J OC))

/-- **Cohomology over `V_i` of a module of `A` vanishes above `d_V`.** For `V` in the set `B`
of condition 0DC4 and a member `V_i` of a distinguished covering of `V`, `H^p(V_i, F)` is
`H^p(V_i → V, F|_V)` (Stacks 03F3), which vanishes for `p > d_V` because `F|_V` lies in `A_V`. -/
theorem isZero_moduleCohomology_of_globalProperty (V : C) (hV : T.bound.B V)
    (𝒰 : PreZeroHypercover.{u} V) (h𝒰 : (T.bound.coverings V hV).cov 𝒰) (i : 𝒰.I₀) (p : ℕ)
    (hp : T.bound.degreeBound V hV < (p : ℤ))
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf OC))
    (hF : LocalSerreFamily.globalProperty _ T F) :
    IsZero (moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf OC) (𝒰.X i) p F) := by
  let : HasSheafify (J.toGrothendieck.over V) AddCommGrpCat.{u} :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u, u, u}
  let : (J.toGrothendieck.over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u, u, u}
  have := Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overPullback.{u, u, u}
    J.toGrothendieck V
  have := Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback.{u, u, u}
    J.toGrothendieck V
  exact (isZero_moduleCohomology_pushforward_iff (Over.forget V)
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf OC).over V)) (Over.mk (𝒰.f i)) p F).1
      (T.bound.vanishing V hV 𝒰 h𝒰 i p hp _ (hF V))

/-- **Assumption (5) of Stacks 0D7V in the proof of Stacks 0DC7**: `(C, O_C, A)` satisfies the
assumption of the Olsson--Laszlo Situation 0D6R, with the set `B`, the bounds `d_V` and the
cofinal covering systems `Cov_V` of condition 0DC4. -/
def baseOlssonLaszloSituation : OlssonLaszloSituation.{u, u, u, u} where
  C := C
  J := J.toGrothendieck
  O := Stacks.SheafOfModules.Tensor.ringSheaf OC
  A := LocalSerreFamily.globalProperty _ T
  weakSerre := LocalSerreFamily.isWeakSerreClass_globalProperty _ T
  B := T.bound.B
  basis_cover := T.bound.basisCover
  degreeBound := T.bound.degreeBound
  coverings := T.bound.coverings
  vanishing := isZero_moduleCohomology_of_globalProperty J OC T

section Total

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

variable (H : HypercoveringOfTerminal.{u, u} J)

/-- **Cohomology over `V_k/U_{n,i}` of a module of `A_total` vanishes above `d_V`.** Let
`W : V ⟶ U_{n,i}` be an object of the summand slice with `V` in the set `B` of condition 0DC4,
and `V_k ⟶ V` a member of a distinguished covering of `V`. For `F` in `A_total`, cohomology over
the object `V_k/U_{n,i}` of the total site is cohomology over it of `F_n` on the component
(Stacks 0DBZ), which is cohomology over `V_k ⟶ U_{n,i}` of the component `F_{n,i}` on the slice
(Stacks 0DC0), which is cohomology over `V_k ⟶ V` of `F_{n,i}|_V` (Stacks 03F3). The last one
vanishes for `p > d_V`, because `F_{n,i}` lies in `A_{U_{n,i}}`, hence `F_{n,i}|_V` in `A_V` by
0DC2. -/
theorem isZero_moduleCohomology_totalLocalSerre (n : SimplexCategory)
    (i : (H.toSimplicialObject.obj (op n)).I) (W : Over ((H.toSimplicialObject.obj (op n)).obj i))
    (hW : T.bound.B W.left) (𝒱 : PreZeroHypercover.{u} W.left)
    (h𝒱 : (T.bound.coverings W.left hW).cov 𝒱) (k : 𝒱.I₀) (p : ℕ)
    (hp : T.bound.degreeBound W.left hW < (p : ℤ))
    (F : SheafOfModules.{u}
      ((hypercoveringSituation J H).totalRingSheaf (hypercoveringRingedAugmentation J H OC).O))
    (hF : totalLocalSerre J H OC T F) :
    letI : HasSheafify (hypercoveringSituation J H).totalTopology AddCommGrpCat.{u} :=
      Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u, u, u}
    IsZero (moduleCohomology
      ((hypercoveringSituation J H).totalRingSheaf (hypercoveringRingedAugmentation J H OC).O)
      ((componentFunctor (hypercoveringSituation J H) n).obj
        ((summandFunctor (pretopologyRingedSite J OC) H.toSimplicialObject n i).obj
          (Over.mk (𝒱.f k ≫ W.hom)))) p F) := by
  let : HasSheafify (hypercoveringSituation J H).totalTopology AddCommGrpCat.{u} :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u, u, u}
  let : HasSheafify ((hypercoveringSituation J H).componentTopology n) AddCommGrpCat.{u} :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u, u, u}
  let : ((hypercoveringSituation J H).componentTopology n).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u, u, u}
  let : ∀ V : C, HasSheafify (J.toGrothendieck.over V) AddCommGrpCat.{u} := fun _ ↦
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u, u, u}
  let : ∀ V : C, (J.toGrothendieck.over V).WEqualsLocallyBijective AddCommGrpCat.{u} := fun _ ↦
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u, u, u}
  let c := componentFunctor (hypercoveringSituation J H) n
  let s := summandFunctor (pretopologyRingedSite J OC) H.toSimplicialObject n i
  have hs := summandFunctor_isContinuous (pretopologyRingedSite J OC) H.toSimplicialObject n i
  let Fn := (componentModuleRestriction (hypercoveringSituation J H)
    ((hypercoveringSituation J H).totalRingSheaf (hypercoveringRingedAugmentation J H OC).O)
    n).obj F
  let G := (hypercoveringSummandRestriction J H OC n i).obj Fn
  have hE := T.bound.vanishing W.left hW 𝒱 h𝒱 k p hp
    ((SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf OC) W.hom).obj G)
    (T.restriction W.hom G (hF.2 n i))
  have hD := (isZero_moduleCohomology_pushforward_iff (Over.map W.hom)
    (hcol := Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overMapPullback
      J.toGrothendieck W.hom)
    (hinj := Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overMapPullback
      J.toGrothendieck W.hom)
    (Sheaf.pushforwardOverMapIso (Stacks.SheafOfModules.Tensor.ringSheaf OC) W.hom).inv
    (Over.mk (𝒱.f k)) p G).1 hE
  have hC := (isZero_moduleCohomology_pushforward_iff s
    (hu := hs)
    (hcol := preservesFiniteColimits_sheafPushforwardContinuous_of_eq s
      (hs := hs)
      (hs' := Stacks.Cohomology.SimplicialSummand.incl_isCocontinuous J.toGrothendieck
        (H.toSimplicialObject.obj (op n)) i)
      (componentTopology_eq J.toGrothendieck H.toSimplicialObject n).symm)
    (hinj := preservesInjectiveObjects_sheafPushforwardContinuous_of_weaklyInitial s
      (hs := hs)
      (Stacks.Cohomology.SimplicialSummand.weaklyInitial_structuredArrow_incl i))
    (summandRingMap (pretopologyRingedSite J OC) H.toSimplicialObject n i)
    ((Over.map W.hom).obj (Over.mk (𝒱.f k))) p
    ((SheafOfModules.restrictScalars (hypercoveringComponentRingMap J H OC n)).obj Fn)).1 hD
  have hB := (isZero_moduleCohomology_restrictScalars_iff (hypercoveringComponentRingMap J H OC n)
    (s.obj ((Over.map W.hom).obj (Over.mk (𝒱.f k)))) p Fn).1 hC
  exact (isZero_moduleCohomology_pushforward_iff c
    (hu := componentFunctor_isContinuous (hypercoveringSituation J H) n)
    (hcol := SheafifiedHigherDirectImage.preservesFiniteColimits_pushforwardOfContinuous
      AddCommGrpCat.{u} c)
    (hinj := SheafifiedHigherDirectImage.preservesInjectiveObjects_pushforwardOfContinuous
      AddCommGrpCat.{u} c)
    (𝟙 _) _ p F).1 hB

end Total

end Stacks.CategoryTheory.Hypercovering

end
