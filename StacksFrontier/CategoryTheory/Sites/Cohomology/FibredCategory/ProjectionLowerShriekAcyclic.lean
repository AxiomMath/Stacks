module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ProjectionLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.AbelianSheafification
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingAlongAFunctorEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicCriterion
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks
public import StacksFrontier.CategoryTheory.Sites.Stack.InheritedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriekAndPerfection.FibredCategorySection
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfALocalizedSite
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
import StacksCore.Tactic.StacksAttribute

/-!
# The acyclicity statement of Stacks 07AC for the projection of a fibred category

Let `p : C ⥤ D` be a fibred category over a site `(D, J)`, and give `C` the inherited topology of
Stacks 06NV. This file discharges the acyclicity statement of Stacks 07AC for the induced
morphism of topoi `π : Sh(C) ⟶ Sh(D)`, so that the left derived functor `Lπ_!` on abelian sheaves
exists with no hypothesis.

The route is the one of Stacks 07AC: by
`Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekAcyclic_of_ext_vanishing` the acyclicity
statement is the vanishing `Ext^n(j_{U!} ℤ_U, π⁻¹ I) = 0` for `n ≥ 1`, every object `U` of `C` and
every injective abelian sheaf `I` on `D`, which is Stacks 0D6X along `p`. Stacks proves 0D6X by a
Čech computation, using that coverings of a site have fibre products; a Grothendieck topology on
`D` need not have them, so the vanishing is proved here instead through the section of Stacks 08P9.
Restriction along the strongly cartesian lifts at `U`, `G ↦ (V ⟶ p(U)) ↦ G(V ×_{p(U)} U)`, is the
composite of `j_U⁻¹` with the inverse image `σ⁻¹ = π_{U,*}` of that section; it is exact, it
preserves injectives, it carries `π⁻¹ I` to `I|_{p(U)}`, which is injective, and its value at the
terminal object of `D/p(U)` is the sections over `U`, which are the morphisms out of `j_{U!} ℤ_U`.
Dimension shifting then gives the vanishing.

## Main results

* `Stacks.Cohomology.subsingleton_ext_of_injective_map`: the dimension shifting argument, for an
  exact functor preserving injectives.

The others are in the namespace `Stacks.Sites.FibredCategory.FibredCategorySituation`:

* `preservesCoveringPullbacks`: when the base has fibre products, the covering-pullback condition
  of Stacks 00WV for `p`.
* `subsingleton_ext_extensionByZeroUnitAb_abelianInverseImage`: Stacks 0D6X for `p`, over an
  object of `C`.
* `abelianLowerShriekAcyclic`: the acyclicity statement of Stacks 07AC for `π`.
* `hasPointwiseLeftDerivedFunctor_abelianLowerShriekOnHomotopy`: the existence of `Lπ_!`, as an
  instance.
* `derivedAbelianLowerShriekAdjunctionUnconditional`: **the `Lπ_!^{Ab}` of Stacks 09CY**, with its
  adjunction `Lπ_!^{Ab} ⊣ π^{-1}` and no hypothesis beyond Situation 08P8.

## References

* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 08PC](https://stacks.math.columbia.edu/tag/08PC)
* [Stacks Project, Tag 09CY](https://stacks.math.columbia.edu/tag/09CY)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 08P9](https://stacks.math.columbia.edu/tag/08P9)
* [Stacks Project, Tag 06N5](https://stacks.math.columbia.edu/tag/06N5)
* [Stacks Project, Tag 06NV](https://stacks.math.columbia.edu/tag/06NV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology

universe t

/-- **Dimension shifting against a restriction which sees injectives.** Let `R` be an exact functor
between abelian categories which preserves injective objects, and let `X` be an object such that
every morphism from `X` lifts along every morphism which `R` carries to a split epimorphism. Then
`Ext^n(X, Y) = 0` for every `n ≥ 1` and every `Y` with `R Y` injective.

Embed `Y` in an injective `I` with cokernel `Q`. Since `R Y` is injective, `R` of that short
exact sequence splits, so `R Q` is a retract of the injective `R I`, and `R` of the quotient map
is a split epimorphism. The lifting property kills `Ext^1(X, Y)`, and `Ext^{n+1}(X, Y)` is a
quotient of `Ext^n(X, Q)`, which vanishes by induction. -/
theorem subsingleton_ext_of_injective_map {B : Type*} [Category* B] [Abelian B] [HasExt.{t} B]
    [EnoughInjectives B] {A : Type*} [Category* A] [Abelian A] (R : B ⥤ A)
    [R.PreservesZeroMorphisms] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [R.PreservesInjectiveObjects] (X : B)
    (hX : ∀ ⦃Y Z : B⦄ (g : Y ⟶ Z), IsSplitEpi (R.map g) → ∀ f : X ⟶ Z, ∃ h : X ⟶ Y, h ≫ g = f)
    (n : ℕ) (hn : 1 ≤ n) (Y : B) (hY : Injective (R.obj Y)) :
    Subsingleton (Abelian.Ext.{t} X Y n) := by
  induction n generalizing Y with
  | zero => omega
  | succ n ih =>
    obtain ⟨ip⟩ := EnoughInjectives.presentation Y
    let S := ShortComplex.mk ip.f (cokernel.π ip.f) (cokernel.condition ip.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ip.f }
    have : Injective (S.map R).X₁ := hY
    let sp := (hS.map_of_exact R).splittingOfInjective
    have : Injective (R.obj ip.J) := R.injective_obj ip.J
    have hQ : Injective (R.obj S.X₃) :=
      Retract.injective (Y := R.obj S.X₂) ⟨sp.s, R.map S.g, sp.s_g⟩
    have : Injective S.X₂ := ip.injective
    refine subsingleton_of_forall_eq 0 fun z => ?_
    obtain ⟨q, hq⟩ := Abelian.Ext.covariant_sequence_exact₁ X hS z
      (Abelian.Ext.eq_zero_of_injective _) rfl
    rw [← hq]
    rcases n with _ | n
    · obtain ⟨h, hh⟩ := hX S.g (IsSplitEpi.mk' ⟨sp.s, sp.s_g⟩) (Abelian.Ext.addEquiv₀ q)
      have hq' : q = Abelian.Ext.mk₀ (h ≫ S.g) := by
        rw [hh]
        simp
      rw [hq', ← Abelian.Ext.mk₀_comp_mk₀_assoc]
      simp
    · rw [(ih (by omega) S.X₃ hQ).elim q 0, Abelian.Ext.zero_comp]

end Stacks.Cohomology

namespace Stacks.Sites.FibredCategory

universe uD vD uC vC w

namespace FibredCategorySituation

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})

/-- Abelian sheaves on the total category, with sections in the universe in which `π` is formed,
form a Grothendieck abelian category. -/
instance isGrothendieckAbelian_totalSheaves :
    IsGrothendieckAbelian.{max w uD vD uC vC}
      (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC}) :=
  isGrothendieckAbelian_sheaf_addCommGrpCat.{uC, vC, max w uD vD uC vC} s.topology

section CoveringPullbacks

variable [HasPullbacks s.base.C]

/-- **The covering-pullback condition of Stacks 00WV for the projection of a fibred category.**
Every covering sieve of the inherited topology contains a covering family of strongly cartesian
morphisms; a strongly cartesian morphism has a fibre product with every morphism to its target,
and `p` carries that fibre product square to a fibre product square (Stacks 06N5). -/
instance preservesCoveringPullbacks : Stacks.Sites.PreservesCoveringPullbacks s.topology s.p where
  exists_cover U S hS := by
    rw [topology, Functor.inheritedTopology_eq,
      Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
    obtain ⟨R, hR, hRS⟩ := hS
    refine ⟨R, Precoverage.generate_mem_toGrothendieck hR, hRS, fun V f hf W g => ?_⟩
    have : s.p.IsStronglyCartesian (s.p.map f) f := hR.1 f hf
    have : HasPullback f g := Functor.IsFibered.hasPullback_of_isStronglyCartesian s.p f g
    exact ⟨this, preservesLimit_of_preserves_limit_cone (pullbackIsPullback f g)
      ((isLimitMapConePullbackConeEquiv s.p pullback.condition).symm
        (Functor.IsFibered.map_isPullback_of_isStronglyCartesian s.p f g).isLimit)⟩

end CoveringPullbacks

section LocalizedRestriction

variable (U : s.C)

/-- The functor `D/p(U) ⥤ C` sending `V ⟶ p(U)` to the source of the chosen strongly cartesian
lift of `V ⟶ p(U)` with target `U`: the cartesian section of the localized projection of Stacks
08P9, followed by the localization functor `C/U ⥤ C`. -/
abbrev cartesianLiftRestrictionFunctor : Over (s.p.obj U) ⥤ s.C :=
  (localizedProjectionSection s U).cartesianSectionFunctor ⋙ Over.forget U

/-- **Restriction along the cartesian lifts at `U`**, `G ↦ (V ⟶ p(U)) ↦ G(V ×_{p(U)} U)`, from
abelian sheaves on the total category to abelian sheaves on the localized base `D/p(U)`: the
restriction `j_U⁻¹` to `C/U` followed by the inverse image `σ⁻¹ = π_{U,*}` of the section of
Stacks 08P9. -/
abbrev cartesianLiftRestriction :
    Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC} ⥤
      Sheaf (s.base.J.over (s.p.obj U)) AddCommGrpCat.{max w uD vD uC vC} :=
  letI := (localizedProjectionSection s U).cartesianSection_isContinuous
  s.topology.overPullback AddCommGrpCat.{max w uD vD uC vC} U ⋙
    (localizedProjectionSection s U).cartesianSectionFunctor.sheafPushforwardContinuous
      AddCommGrpCat.{max w uD vD uC vC} (s.base.J.over (s.p.obj U)) (s.topology.over U)

/-- The restriction along the cartesian lifts at `U` preserves finite limits, finite colimits and
injective objects. Both factors are restrictions along functors which are continuous and
cocontinuous, hence exact; `j_U⁻¹` preserves injectives because extension by zero is left exact,
and `σ⁻¹` because it is right adjoint to `π_U⁻¹`, restriction along the continuous localized
projection, which preserves monomorphisms. -/
theorem cartesianLiftRestriction_exact :
    PreservesFiniteLimits (s.cartesianLiftRestriction U) ∧
      PreservesFiniteColimits (s.cartesianLiftRestriction U) ∧
        (s.cartesianLiftRestriction U).PreservesInjectiveObjects := by
  let σ := localizedProjectionSection s U
  let A := AddCommGrpCat.{max w uD vD uC vC}
  let JU := s.topology.over U
  let K := s.base.J.over (s.p.obj U)
  have := σ.isContinuous
  have := σ.cartesianSection_isContinuous
  have := σ.cartesianSection_isCocontinuous
  have : ∀ V : s.C, HasSheafify (s.topology.over V) A := fun V =>
    hasSheafify_addCommGrpCat.{max uC vC, vC, max w uD vD uC vC} (s.topology.over V)
  have : HasSheafify K A := hasSheafify_addCommGrpCat.{max uD vD, vD, max w uD vD uC vC} K
  have : s.topology.WEqualsLocallyBijective A :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{uC, vC,
      max w uD vD uC vC} (J := s.topology)
  have : JU.WEqualsLocallyBijective A :=
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{max uC vC, vC,
      max w uD vD uC vC} (J := JU)
  let adj := σ.cartesianSection_adjunction.sheafPushforwardAdjunction A (J := JU) (K := K)
  have hj₁ : PreservesFiniteLimits (s.topology.overPullback A U) := inferInstance
  have hj₂ : PreservesFiniteColimits (s.topology.overPullback A U) :=
    Stacks.Cohomology.LocalizedSite.preservesFiniteColimits_overPullback.{vC, uC,
      max w uD vD uC vC} s.topology U
  have hj₃ : (s.topology.overPullback A U).PreservesInjectiveObjects :=
    Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback.{vC, uC,
      max w uD vD uC vC} s.topology U
  have hv₁ : PreservesFiniteLimits (σ.cartesianSectionFunctor.sheafPushforwardContinuous A K JU) :=
    Functor.preservesFiniteLimits_sheafPushforwardContinuous K JU _ A
  have hv₂ : PreservesFiniteColimits
      (σ.cartesianSectionFunctor.sheafPushforwardContinuous A K JU) :=
    Functor.preservesFiniteColimits_sheafPushforwardContinuous_of_isAlmostCocontinuous _ K JU
      (isAlmostCocontinuous_of_isCocontinuous _ K JU)
  have : PreservesFiniteLimits
      ((Over.post s.p : Over U ⥤ Over (s.p.obj U)).sheafPushforwardContinuous A JU K) :=
    Functor.preservesFiniteLimits_sheafPushforwardContinuous JU K _ A
  have : ((Over.post s.p : Over U ⥤ Over (s.p.obj U)).sheafPushforwardContinuous
      A JU K).PreservesMonomorphisms := preservesMonomorphisms_of_preservesLimitsOfShape _
  have : (σ.cartesianSectionFunctor.sheafPushforwardContinuous A K JU).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  exact ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _, inferInstance⟩

/-- The object of the total category reached from the terminal object of `D/p(U)`, the chosen
strongly cartesian lift of `𝟙 : p(U) ⟶ p(U)`, is isomorphic to `U`: a strongly cartesian morphism
lying over an isomorphism is an isomorphism. -/
def cartesianLiftRestrictionFunctorObjIso :
    (s.cartesianLiftRestrictionFunctor U).obj (Over.mk (𝟙 (s.p.obj U))) ≅ U :=
  let σ := localizedProjectionSection s U
  let T := Over.mk (𝟙 (s.p.obj U))
  have : IsIso (s.p.map (σ.cartesianSectionFunctor.obj T).hom) := by
    let e := σ.cartesianSection_base.app T
    have hw : e.hom.left = ((σ.cartesianSectionFunctor ⋙ Over.post s.p).obj T).hom := by
      simpa [T] using Over.w e.hom
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    change IsIso ((σ.cartesianSectionFunctor ⋙ Over.post s.p).obj T).hom
    rw [← hw]
    infer_instance
  have := σ.cartesianSection_isCartesian T
  have : IsIso (σ.cartesianSectionFunctor.obj T).hom :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso s.p
      (s.p.map (σ.cartesianSectionFunctor.obj T).hom) _
  asIso (σ.cartesianSectionFunctor.obj T).hom

/-- The restriction along the cartesian lifts at `U` of the inverse image `π⁻¹ I` of an abelian
sheaf on the base is the restriction `I|_{p(U)}` of `I` to the localized base, since composing the
cartesian section with the projection gives back the identity of `D/p(U)`. -/
def cartesianLiftRestrictionInverseImageIso (I : Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) :
    (s.cartesianLiftRestriction U).obj (s.abelianInverseImage.obj I) ≅
      (s.base.J.overPullback AddCommGrpCat.{max w uD vD uC vC} (s.p.obj U)).obj I :=
  let σ := localizedProjectionSection s U
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerRight (NatIso.op
      (Functor.isoWhiskerRight σ.cartesianSection_base (Over.forget (s.p.obj U))).symm) I.obj)

end LocalizedRestriction

/-- **Stacks 0D6X for the projection of a fibred category, over an object of the total
category.** The restriction `π⁻¹ I` of an injective abelian sheaf on the base has vanishing
cohomology `Ext^n(j_{U!} ℤ_U, π⁻¹ I)` over every object `U` of the total category in positive
degrees.

No fibre products are needed: restriction along the strongly cartesian lifts at `U`
(`cartesianLiftRestriction`) is exact, preserves injectives and carries `π⁻¹ I` to the injective
sheaf `I|_{p(U)}`, while morphisms out of `j_{U!} ℤ_U` are sections over `U`, which is the value
of that restriction at the terminal object of `D/p(U)`. Dimension shifting
(`Stacks.Cohomology.subsingleton_ext_of_injective_map`) concludes. -/
theorem subsingleton_ext_extensionByZeroUnitAb_abelianInverseImage (U : s.C)
    (I : Sheaf s.base.J AddCommGrpCat.{max w uD vD uC vC}) [Injective I] (n : ℕ) (hn : 0 < n) :
    Subsingleton (Abelian.Ext
      (Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{max w uD vD uC} s.topology U)
      (s.abelianInverseImage.obj I) n) := by
  let A := AddCommGrpCat.{max w uD vD uC vC}
  let T : Over (s.p.obj U) := Over.mk (𝟙 (s.p.obj U))
  let U' := (s.cartesianLiftRestrictionFunctor U).obj T
  obtain ⟨h₁, h₂, h₃⟩ := s.cartesianLiftRestriction_exact U
  have : ∀ V : s.base.C, HasSheafify (s.base.J.over V) A := fun V =>
    hasSheafify_addCommGrpCat.{max uD vD, vD, max w uD vD uC vC} (s.base.J.over V)
  have : (s.base.J.overPullback A (s.p.obj U)).PreservesInjectiveObjects :=
    Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback.{vD, uD,
      max w uD vD uC vC} s.base.J (s.p.obj U)
  have hI : Injective ((s.cartesianLiftRestriction U).obj (s.abelianInverseImage.obj I)) :=
    Injective.of_iso (s.cartesianLiftRestrictionInverseImageIso U I).symm
      ((s.base.J.overPullback A (s.p.obj U)).injective_obj I)
  let eU : Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{max w uD vD uC}
      s.topology U ≅
      Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAb.{max w uD vD uC} s.topology U' :=
    (Presheaf.freeAbelianSheaf.{max w uD vD uC vC} s.topology).mapIso
      (uliftYoneda.{max w uD vD uC}.mapIso (s.cartesianLiftRestrictionFunctorObjIso U).symm)
  refine Stacks.Cohomology.subsingleton_ext_of_iso eU n ?_
  have : EnoughInjectives (Sheaf s.topology A) := inferInstance
  have : (s.cartesianLiftRestriction U).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  refine Stacks.Cohomology.subsingleton_ext_of_injective_map (s.cartesianLiftRestriction U)
    _ (fun Y Z g hg f => ?_) n hn _ hI
  obtain ⟨⟨sec, hsec⟩⟩ := hg
  let E := fun F : Sheaf s.topology A =>
    Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAbHomEquiv.{max w uD vD uC}
      s.topology U' F
  let x : ((s.cartesianLiftRestriction U).obj Z).obj.obj (Opposite.op T) := E Z f
  let y : Y.obj.obj (Opposite.op U') := (sec.hom.app (Opposite.op T)).hom x
  refine ⟨(E Y).symm y, (E Z).injective ?_⟩
  rw [Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitAbHomEquiv_naturality]
  simp only [E, Equiv.apply_symm_apply]
  exact congrArg (fun φ => φ.hom.app (Opposite.op T) x) hsec

/-- **The acyclicity statement of Stacks 07AC for the projection of a fibred category,
discharged.** The lower-shriek functor `π_!` on abelian sheaves carries every bounded above
acyclic complex whose terms are direct sums of the free abelian sheaves `j_{U!} ℤ_U` to an acyclic
complex. By `Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekAcyclic_of_ext_vanishing`
this is the object-level vanishing of Stacks 0D6X, which is
`subsingleton_ext_extensionByZeroUnitAb_abelianInverseImage`. -/
theorem abelianLowerShriekAcyclic : s.AbelianLowerShriekAcyclic :=
  Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekAcyclic_of_ext_vanishing.{
    max w uD vD uC vC, max w uD vD uC, vC, uC, vD, uD} s.topology s.base.J s.p
    fun U I _ n hn => s.subsingleton_ext_extensionByZeroUnitAb_abelianInverseImage U I n hn

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 07AC for the projection of a fibred category**, existence, with no hypothesis: the
left derived functor `Lπ_!` of degreewise lower shriek exists at every object. -/
instance hasPointwiseLeftDerivedFunctor_abelianLowerShriekOnHomotopy :
    (s.abelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC})
        (ComplexShape.up ℤ)) :=
  s.hasPointwiseLeftDerivedAbelianLowerShriek s.abelianLowerShriekAcyclic

/-- **Stacks 09CY, the derived abelian `Lπ_!^{Ab}` of Situation 08P8.** Remark 09CY reduces
Situation 08P8 to Situation 08PA and reads off from Lemma 08PC the four functors `π_!`,
`π_!^{Ab}`, `Lπ_!` and `Lπ_!^{Ab}`. This is the third of them: `Lπ_!^{Ab} : D(Ab(C)) ⥤ D(Ab(D))`
is left adjoint to derived `π^{-1}`, which is part (3) of Stacks 08PC on abelian sheaves.

It is stated here rather than transported along the reduction because the acyclicity statement
of Stacks 07AC, which is what part (3) rests on, is discharged for `π` in this file, as
`abelianLowerShriekAcyclic`; the conditional form `derivedAbelianLowerShriekAdjunction` takes it
as an argument, and this is that argument supplied, so the adjunction holds under the hypotheses
of Situation 08P8 alone. -/
@[stacks 09CY "the derived abelian `Lπ_!^{Ab}` of Situation 08P8 and its adjunction \
`Lπ_!^{Ab} ⊣ π^{-1}`, with the acyclicity statement of Stacks 07AC discharged"]
def derivedAbelianLowerShriekAdjunctionUnconditional :
    s.derivedAbelianLowerShriek ⊣ s.derivedAbelianInverseImage :=
  s.derivedAbelianLowerShriekAdjunction s.abelianLowerShriekAcyclic

end Derived

end FibredCategorySituation

end Stacks.Sites.FibredCategory

end
