module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpSliceDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.SheafCriterion
public import StacksFrontier.CategoryTheory.Sites.Descent.StackForTransitivity
public import StacksFrontier.CategoryTheory.Sites.Descent.PrestackOfCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescent

/-!
# Stacks for the h topology from Zariski coverings and proper surjections

A pseudofunctor `F : LocallyDiscrete ((Sch/S)_h)ᵒᵖ ⥤ᵖ Cat` is a stack for the h topology as soon as
descent is effective along every Zariski covering family of the site and along every morphism of
the site which is proper, surjective and of finite presentation. This is the stack analogue of
the sufficiency direction of Stacks 0EU5, and it is proved from it: a property of objects of a
slice of the site which is local for Zariski coverings and for proper surjections of finite
presentation, and holds on one h covering, holds on the base
(`AlgebraicGeometry.BigHOver.of_localOnZariskiProper`), and the property is taken to be that `F`
is a prestack, resp. a stack, for every pullback of a fixed covering sieve. The step from the
local statement to the global one for stacks is the transitivity of effective descent,
`CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_of_isEquivalence_pullback`.

## Main results

* `AlgebraicGeometry.BigHOver.of_localOnZariskiProper`: the descent principle for properties.
* `AlgebraicGeometry.BigHOver.isStack_of_zariski_of_properFP`: the stack condition for the h
  topology; the prestack condition is proved first along the way, by the same descent
  principle with the property that `F` is a prestack for every pullback of a covering sieve.

## References

* [Stacks Project, Tag 0EU5](https://stacks.math.columbia.edu/tag/0EU5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v' u' u

namespace AlgebraicGeometry

namespace BigHOver

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Descending a property along the generators of the h topology -/

variable (B S hS) in
/-- **A property of objects of the slice at `U` which is local for Zariski coverings and for
proper surjections of finite presentation, and holds on one h covering of `U`, holds at `U`.**

The two hypotheses are the two conditions of Stacks 0EU5 for the subterminal presheaf of truth
values of `Ψ`, read on the big h category over the underlying scheme of `U`. -/
public theorem of_localOnZariskiProper (U : BigHOver B S hS)
    (Ψ : Over U → Prop)
    (hmono : ∀ {Y Y' : Over U}, (Y' ⟶ Y) → Ψ Y → Ψ Y')
    (hzar : ∀ (Y : Over U) (E : PreZeroHypercover.{u + 1} Y),
      (E.map (sliceToScheme B S hS U)).presieve₀ ∈
        Scheme.zariskiPrecoverage ((sliceToScheme B S hS U).obj Y) →
      (∀ i, Ψ (E.X i)) → Ψ Y)
    (hprop : ∀ (Y Y' : Over U) (g : Y' ⟶ Y),
      IsProper ((sliceToScheme B S hS U).map g) →
      Surjective ((sliceToScheme B S hS U).map g) →
      FinitePresentation ((sliceToScheme B S hS U).map g) →
      Ψ Y' → Ψ Y)
    {I : Type (u + 1)} {V : I → BigHOver B S hS} (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS U)
    (hV : ∀ i, Ψ (Over.mk (f i))) :
    Ψ (Over.mk (𝟙 U)) := by
  classical
  let β : Over U.left ⥤ Over U := Over.iteratedSliceBackward U
  set P := truthPresheaf B S hS U Ψ hmono with hP
  set G : (BigHOver B ((BigHOver.toScheme B S hS).obj U) U.left.property)ᵒᵖ ⥤ Type :=
    β.op ⋙ P with hG
  have hsub : ∀ Y, Subsingleton (G.obj Y) := fun Y ↦ inferInstanceAs
    (Subsingleton (P.obj (op (β.obj Y.unop))))
  have hiff : ∀ Y, Nonempty (G.obj (op Y)) ↔ Ψ (β.obj Y) :=
    fun Y ↦ ⟨fun ⟨x⟩ ↦ x.down, fun h ↦ ⟨⟨h⟩⟩⟩
  have hsheaf : Presheaf.IsSheaf
      (BigHOver.topology B ((BigHOver.toScheme B S hS).obj U) U.left.property) G := by
    refine (isSheaf_iff_isZariskiSheaf_and_isProperFinitePresentationSheaf _ _ _ G).2
      ⟨isZariskiSheaf_of_nonempty _ _ _ G ?_, ?_⟩
    · intro Y E hE hne
      exact (hiff Y).2 (hzar (β.obj Y) (E.map β) hE fun i ↦ (hiff (E.X i)).1 (hne i))
    · intro X Y g hproper hsurj hfp
      rw [Presieve.isSheafFor_iff_nonempty_of_subsingleton]
      intro hne
      exact (hiff X).2 (hprop (β.obj X) (β.obj Y) (β.map g) hproper hsurj hfp
        ((hiff Y).1 (hne g (Presieve.singleton_self g))))
  have hcov : Sieve.ofArrows (fun i ↦ Over.mk (f i).left)
      (fun i ↦ (Over.homMk (f i).left : Over.mk (f i).left ⟶ Over.mk (𝟙 U.left))) ∈
      BigHOver.topology B ((BigHOver.toScheme B S hS).obj U) U.left.property
        (Over.mk (𝟙 U.left)) := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hf
    exact hf
  have hmem : ∀ i, Nonempty (G.obj (op (Over.mk (f i).left))) := by
    intro i
    refine (hiff _).2 (hmono (Y := Over.mk (f i)) ?_ (hV i))
    have hw : 𝟙 (V i).left ≫ (V i).hom = (f i).left ≫ U.hom := by simp
    exact Over.homMk (Over.homMk (𝟙 (V i).left) hw) (Over.OverMorphism.ext
      (by change 𝟙 (V i).left ≫ (f i).left = (f i).left; simp))
  obtain ⟨x⟩ := nonempty_of_isSheaf_of_covering _ _ _ G hsheaf _ hcov hmem
  refine hmono (Y := β.obj (Over.mk (𝟙 U.left))) ?_ ((hiff _).1 ⟨x⟩)
  have hw : 𝟙 U.left ≫ (𝟙 U.left ≫ U.hom) = U.hom := by simp
  exact Over.homMk (Over.homMk (𝟙 U.left) hw) (Over.OverMorphism.ext
    (by change 𝟙 U.left ≫ 𝟙 U.left = 𝟙 U.left; simp))

/-! ### Base change of the generating families -/

/-- A Zariski covering family of the site generates a covering sieve of the h topology. -/
public theorem ofArrows_mem_topology_of_zariski {X : BigHOver B S hS}
    (E : PreZeroHypercover.{u + 1} X)
    (hE : (E.map (BigHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj X)) :
    Sieve.ofArrows E.X E.f ∈ BigHOver.topology B S hS X :=
  zariskiTopology_le_topology B S hS X (Precoverage.generate_mem_toGrothendieck ⟨E, rfl, hE⟩)

/-- A proper surjection of finite presentation of the site generates a covering sieve of the h
topology. -/
public theorem ofArrows_mem_topology_of_properFP {X Y : BigHOver B S hS} (g : Y ⟶ X)
    (hproper : IsProper ((BigHOver.toScheme B S hS).map g))
    (hsurj : Surjective ((BigHOver.toScheme B S hS).map g))
    (hfp : FinitePresentation ((BigHOver.toScheme B S hS).map g)) :
    Sieve.ofArrows (fun _ : Unit ↦ Y) (fun _ ↦ g) ∈ BigHOver.topology B S hS X := by
  have hE : IsHCovering
      ((PreZeroHypercover.singleton.{u + 1} g).map (BigHOver.toScheme B S hS)).X
      ((PreZeroHypercover.singleton.{u + 1} g).map (BigHOver.toScheme B S hS)).f :=
    (surjective_proper_isHCovering ((BigHOver.toScheme B S hS).map g) hfp).reindex
      (Equiv.ofUnique PUnit.{u + 2} Unit)
  have h := sieve₀_mem_topology_of_isHCovering B S hS (PreZeroHypercover.singleton.{u + 1} g) hE
  rw [PreZeroHypercover.presieve₀_singleton] at h
  have he : Sieve.ofArrows (fun _ : Unit ↦ Y) (fun _ ↦ g) =
      Sieve.generate (Presieve.singleton g) := by
    rw [← Presieve.ofArrows_pUnit.{0}]
  rwa [he]

/-! ### The prestack and stack conditions -/

/-- The sieve generated by the base change of all arrows of a sieve is the pulled back sieve. -/
public theorem _root_.CategoryTheory.Sieve.ofArrows_pullback_category {C : Type*} [Category C]
    [HasPullbacks C] {X Y : C} (T : Sieve X) (g : Y ⟶ X) :
    Sieve.ofArrows (fun a : T.arrows.category ↦ pullback a.obj.hom g)
      (fun a ↦ pullback.snd a.obj.hom g) = T.pullback g := by
  rw [Sieve.ofArrows, Presieve.ofArrows_pullback, Sieve.pullbackArrows_comm, ← Sieve.ofArrows,
    Sieve.ofArrows_category]

/-- Descent along the maximal sieve is effective. -/
public theorem _root_.CategoryTheory.Pseudofunctor.isStackFor_top {C : Type*} [Category C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) (Z : C) :
    F.IsStackFor (⊤ : Sieve Z).arrows := by
  have h : (⊤ : Sieve Z) = Sieve.generate (Presieve.ofArrows (fun _ : Unit ↦ Z) (fun _ ↦ 𝟙 Z)) := by
    symm
    rw [← Sieve.id_mem_iff_eq_top]
    exact ⟨Z, 𝟙 Z, 𝟙 Z, Presieve.ofArrows.mk (Y := fun _ : Unit ↦ Z) (f := fun _ ↦ 𝟙 Z) (), by simp⟩
  rw [h, F.IsStackFor_generate_iff, F.isStackFor_ofArrows_iff]
  exact Pseudofunctor.DescentData.isEquivalence_toDescentData_of_section F (𝟙 Z) (𝟙 Z) (by simp)

/-- A property `Q` of sieves holds along all pullbacks of `R` to the objects over `Y`. -/
private def PullbackProp (Q : ∀ Z : BigHOver B S hS, Sieve Z → Prop) {U : BigHOver B S hS}
    (R : Sieve U) (Y : Over U) : Prop :=
  ∀ ⦃Z : BigHOver B S hS⦄ (h : Z ⟶ Y.left), Q Z (R.pullback (h ≫ Y.hom))

/-- The square of a pullback of `f` along `h` commutes after composing to the common base. -/
private theorem pullback_snd_comp_comp {C : Type*} [Category C] [HasPullbacks C]
    {A B Z T : C} (f : A ⟶ B) (h : Z ⟶ B) (q : B ⟶ T) (p : A ⟶ T) (hf : f ≫ q = p) :
    pullback.snd f h ≫ h ≫ q = pullback.fst f h ≫ p := by
  rw [← Category.assoc, ← pullback.condition, Category.assoc, hf]

/-- The descent principle for properties of the form "`Q` holds on every pullback of the sieve
`R`", where `R` is a covering sieve. -/
private theorem pullbackProp_of_localOnZariskiProper {U : BigHOver B S hS} {R : Sieve U}
    (hR : R ∈ BigHOver.topology B S hS U) (Q : ∀ Z : BigHOver B S hS, Sieve Z → Prop)
    (hzar : ∀ (Y : Over U) (E : PreZeroHypercover.{u + 1} Y),
      (E.map (sliceToScheme B S hS U)).presieve₀ ∈
        Scheme.zariskiPrecoverage ((sliceToScheme B S hS U).obj Y) →
      (∀ i, PullbackProp Q R (E.X i)) → PullbackProp Q R Y)
    (hprop : ∀ (Y Y' : Over U) (g : Y' ⟶ Y),
      IsProper ((sliceToScheme B S hS U).map g) →
      Surjective ((sliceToScheme B S hS U).map g) →
      FinitePresentation ((sliceToScheme B S hS U).map g) →
      PullbackProp Q R Y' → PullbackProp Q R Y)
    (htop : ∀ (a : R.arrows.category) ⦃Z : BigHOver B S hS⦄ (h : Z ⟶ a.obj.left),
      Q Z (R.pullback (h ≫ a.obj.hom))) :
    Q U R := by
  have hmono : ∀ {Y Y' : Over U}, (Y' ⟶ Y) → PullbackProp Q R Y → PullbackProp Q R Y' := by
    intro Y Y' k hY Z h
    have e : h ≫ Y'.hom = (h ≫ k.left) ≫ Y.hom := by rw [Category.assoc, Over.w k]
    rw [e]
    exact hY _
  have key := of_localOnZariskiProper B S hS U (PullbackProp Q R) hmono hzar hprop
    (fun a : R.arrows.category ↦ a.obj.hom) (by rwa [Sieve.ofArrows_category]) htop
  simpa [PullbackProp] using key (𝟙 U)

section Stack

variable {F : Pseudofunctor (LocallyDiscrete (BigHOver B S hS)ᵒᵖ) Cat.{v', u'}}
  (hZ : ∀ (X : BigHOver B S hS) (E : PreZeroHypercover.{u + 1} X),
    (E.map (BigHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj X) →
    (F.toDescentData E.f).IsEquivalence)
  (hP : ∀ (X Y : BigHOver B S hS) (g : Y ⟶ X),
    IsProper ((BigHOver.toScheme B S hS).map g) →
    Surjective ((BigHOver.toScheme B S hS).map g) →
    FinitePresentation ((BigHOver.toScheme B S hS).map g) →
    (F.toDescentData (fun _ : Unit ↦ g)).IsEquivalence)

include hZ hP in
/-- **The stack condition for the h topology** from effective descent along Zariski coverings
and along proper surjections of finite presentation. -/
public theorem isStack_of_zariski_of_properFP : F.IsStack (BigHOver.topology B S hS) := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  have zariski_pullback₂ : ∀ {X Y : BigHOver B S hS} (E : PreZeroHypercover.{u + 1} X),
      (E.map (BigHOver.toScheme B S hS)).presieve₀ ∈
        Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj X) →
      ∀ g : Y ⟶ X, ((E.pullback₂ g).map (BigHOver.toScheme B S hS)).presieve₀ ∈
        Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj Y) := by
    intro X Y E hE g
    let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
    let : Limits.PreservesLimitsOfShape Limits.WalkingCospan (BigHOver.toScheme B S hS) :=
      inferInstance
    let Eb := E.map (BigHOver.toScheme B S hS)
    let Eb' := Eb.pullback₂ ((BigHOver.toScheme B S hS).map g)
    have hmem : Eb'.presieve₀ ∈ Scheme.zariskiPrecoverage
        ((BigHOver.toScheme B S hS).obj Y) :=
      Scheme.zariskiPrecoverage.mem_coverings_of_isPullback Eb.f (by simpa [Eb] using hE)
        ((BigHOver.toScheme B S hS).map g)
        (fun i => Limits.pullback.snd (Eb.f i) ((BigHOver.toScheme B S hS).map g))
        (fun i => Limits.pullback.fst (Eb.f i) ((BigHOver.toScheme B S hS).map g))
        (fun i => (IsPullback.of_hasPullback (Eb.f i)
          ((BigHOver.toScheme B S hS).map g)).flip)
    have hIso : (E.pullback₂ g).map (BigHOver.toScheme B S hS) ≅ Eb' := by
      refine PreZeroHypercover.isoMk (Equiv.refl (E.pullback₂ g).I₀)
        (fun i => Limits.PreservesPullback.iso (BigHOver.toScheme B S hS) (E.f i) g) ?_
      intro i
      exact Limits.PreservesPullback.iso_hom_snd (BigHOver.toScheme B S hS) (E.f i) g
    exact Eb'.presieve₀_mem_of_iso hIso.symm hmem
  have properSurjectiveFP_pullback_snd : ∀ {X Y Z : BigHOver B S hS} (f : Y ⟶ X)
      (g : Z ⟶ X), IsProper ((BigHOver.toScheme B S hS).map f) →
      Surjective ((BigHOver.toScheme B S hS).map f) →
      FinitePresentation ((BigHOver.toScheme B S hS).map f) →
      IsProper ((BigHOver.toScheme B S hS).map (Limits.pullback.snd f g)) ∧
        Surjective ((BigHOver.toScheme B S hS).map (Limits.pullback.snd f g)) ∧
        FinitePresentation ((BigHOver.toScheme B S hS).map (Limits.pullback.snd f g)) := by
    intro X Y Z f g hproper hsurj hfp
    let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
    let : Limits.PreservesLimitsOfShape Limits.WalkingCospan (BigHOver.toScheme B S hS) :=
      inferInstance
    let : IsProper ((BigHOver.toScheme B S hS).map f) := hproper
    let : Surjective ((BigHOver.toScheme B S hS).map f) := hsurj
    let : LocallyOfFinitePresentation ((BigHOver.toScheme B S hS).map f) := hfp.1
    let : QuasiCompact ((BigHOver.toScheme B S hS).map f) := hfp.2.1
    let : QuasiSeparated ((BigHOver.toScheme B S hS).map f) := hfp.2.2
    have heq : (BigHOver.toScheme B S hS).map (Limits.pullback.snd f g)
        = Limits.pullbackComparison (BigHOver.toScheme B S hS) f g
          ≫ Limits.pullback.snd ((BigHOver.toScheme B S hS).map f)
            ((BigHOver.toScheme B S hS).map g) :=
      (Limits.pullbackComparison_comp_snd _ _ _).symm
    rw [heq]
    exact ⟨inferInstance, inferInstance, ⟨inferInstance, inferInstance, inferInstance⟩⟩
  have : F.IsPrestack (BigHOver.topology B S hS) := by
    refine Pseudofunctor.IsPrestack.of_isPrestackFor (fun U R hR ↦ ?_)
    refine pullbackProp_of_localOnZariskiProper hR (fun _ T ↦ F.IsPrestackFor T.arrows) ?_ ?_ ?_
    · intro Y E hE hΨ Z h
      let E' := (E.map (Over.forget U)).pullback₂ h
      have hE' : (E'.map (BigHOver.toScheme B S hS)).presieve₀ ∈
          Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj Z) :=
        zariski_pullback₂ (E.map (Over.forget U)) (by exact hE) h
      have e : ∀ i : E.I₀, pullback.snd (E.f i).left h ≫ h ≫ Y.hom =
          pullback.fst (E.f i).left h ≫ (E.X i).hom :=
        fun i ↦ pullback_snd_comp_comp _ _ _ _ (Over.w (E.f i))
      refine Pseudofunctor.isPrestackFor_of_cover F E'.f
        (fun i j ↦ ChosenPullback.ofHasPullback _ _) _
        (Pseudofunctor.isPrestackFor_of_equivalence F _ (hZ Z E' hE'))
        (fun t ↦ Pseudofunctor.isPrestackFor_pullback_of_equivalence F E'.f t _ _ _
          (fun i ↦ (IsPullback.of_hasPullback (E'.f i) t).flip)
          (hZ _ (E'.pullback₂ t) (zariski_pullback₂ _ hE' t)))
        (fun (i : E.I₀) ↦ ?_) (fun (i j : E.I₀) ↦ ?_)
      · change F.IsPrestackFor ((R.pullback (h ≫ Y.hom)).pullback
          (pullback.snd (E.f i).left h)).arrows
        rw [← Sieve.pullback_comp, e i]
        exact hΨ i _
      · change F.IsPrestackFor ((R.pullback (h ≫ Y.hom)).pullback
          (pullback.fst (pullback.snd (E.f i).left h) (pullback.snd (E.f j).left h) ≫
            pullback.snd (E.f i).left h)).arrows
        rw [← Sieve.pullback_comp, Category.assoc, e i, ← Category.assoc]
        exact hΨ i _
    · intro Y Y' g hproper hsurj hfp hΨ Z h
      obtain ⟨hp', hs', hf'⟩ := properSurjectiveFP_pullback_snd g.left h hproper hsurj hfp
      have e : pullback.snd g.left h ≫ h ≫ Y.hom = pullback.fst _ _ ≫ Y'.hom :=
        pullback_snd_comp_comp _ _ _ _ (Over.w g)
      refine Pseudofunctor.isPrestackFor_of_cover F (fun _ : Unit ↦ pullback.snd g.left h)
        (fun i j ↦ ChosenPullback.ofHasPullback _ _) _
        (Pseudofunctor.isPrestackFor_of_equivalence F _ (hP _ _ _ hp' hs' hf'))
        (fun t ↦ ?_) (fun _ ↦ ?_) (fun _ _ ↦ ?_)
      · obtain ⟨hp'', hs'', hf''⟩ := properSurjectiveFP_pullback_snd _ t hp' hs' hf'
        exact Pseudofunctor.isPrestackFor_pullback_of_equivalence F _ t _ _ _
          (fun _ ↦ (IsPullback.of_hasPullback (pullback.snd g.left h) t).flip)
          (hP _ _ _ hp'' hs'' hf'')
      · rw [← Sieve.pullback_comp, e]
        exact hΨ _
      · change F.IsPrestackFor ((R.pullback (h ≫ Y.hom)).pullback
          (pullback.fst (pullback.snd g.left h) (pullback.snd g.left h) ≫
            pullback.snd g.left h)).arrows
        rw [← Sieve.pullback_comp, Category.assoc, e, ← Category.assoc]
        exact hΨ _
    · intro a Z h
      rw [Sieve.pullback_eq_top_of_mem _ (R.downward_closed a.property h)]
      exact (Pseudofunctor.isStackFor_top F Z).isPrestackFor
  refine Pseudofunctor.IsStack.of_isStackFor (fun U R hR ↦ ?_)
  refine pullbackProp_of_localOnZariskiProper hR (fun _ T ↦ F.IsStackFor T.arrows) ?_ ?_ ?_
  · intro Y E hE hΨ Z h
    let E' := (E.map (Over.forget U)).pullback₂ h
    have hE' : (E'.map (BigHOver.toScheme B S hS)).presieve₀ ∈
        Scheme.zariskiPrecoverage ((BigHOver.toScheme B S hS).obj Z) :=
      zariski_pullback₂ (E.map (Over.forget U)) (by exact hE) h
    have e : ∀ i : E.I₀, pullback.snd (E.f i).left h ≫ h ≫ Y.hom =
        pullback.fst (E.f i).left h ≫ (E.X i).hom :=
      fun i ↦ pullback_snd_comp_comp _ _ _ _ (Over.w (E.f i))
    have hT : R.pullback (h ≫ Y.hom) ∈ BigHOver.topology B S hS Z :=
      (BigHOver.topology B S hS).pullback_stable _ hR
    rw [Pseudofunctor.isStackFor_iff]
    have := hZ Z E' hE'
    refine Pseudofunctor.isEquivalence_toDescentData_of_isEquivalence_pullback
      (J := BigHOver.topology B S hS) _ (by rwa [Sieve.ofArrows_category]) E'.f
      (ofArrows_mem_topology_of_zariski E' hE') (fun (i : E.I₀) ↦ ?_)
    change (F.toDescentData (fun a : (R.pullback (h ≫ Y.hom)).arrows.category ↦
      pullback.snd a.obj.hom (pullback.snd (E.f i).left h))).IsEquivalence
    rw [← F.isStackFor_ofArrows_iff, ← F.IsStackFor_generate_iff]
    change F.IsStackFor (Sieve.ofArrows _ _).arrows
    rw [Sieve.ofArrows_pullback_category, ← Sieve.pullback_comp, e i]
    exact hΨ i _
  · intro Y Y' g hproper hsurj hfp hΨ Z h
    obtain ⟨hp', hs', hf'⟩ := properSurjectiveFP_pullback_snd g.left h hproper hsurj hfp
    have e : pullback.snd g.left h ≫ h ≫ Y.hom = pullback.fst _ _ ≫ Y'.hom :=
      pullback_snd_comp_comp _ _ _ _ (Over.w g)
    have hT : R.pullback (h ≫ Y.hom) ∈ BigHOver.topology B S hS Z :=
      (BigHOver.topology B S hS).pullback_stable _ hR
    rw [Pseudofunctor.isStackFor_iff]
    have := hP _ _ _ hp' hs' hf'
    refine Pseudofunctor.isEquivalence_toDescentData_of_isEquivalence_pullback
      (J := BigHOver.topology B S hS) _ (by rwa [Sieve.ofArrows_category])
      (fun _ : Unit ↦ pullback.snd g.left h)
      (ofArrows_mem_topology_of_properFP _ hp' hs' hf') (fun _ ↦ ?_)
    rw [← F.isStackFor_ofArrows_iff, ← F.IsStackFor_generate_iff]
    change F.IsStackFor (Sieve.ofArrows _ _).arrows
    rw [Sieve.ofArrows_pullback_category, ← Sieve.pullback_comp, e]
    exact hΨ _
  · intro a Z h
    rw [Sieve.pullback_eq_top_of_mem _ (R.downward_closed a.property h)]
    exact Pseudofunctor.isStackFor_top F Z

end Stack

end BigHOver

end AlgebraicGeometry

end
