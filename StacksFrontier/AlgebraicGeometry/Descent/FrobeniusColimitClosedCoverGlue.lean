module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectProperCoverDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpDescent
public import StacksFrontier.CategoryTheory.Sites.Descent.MonoPairCoverHom

/-!
# Gluing over a cover of the source by two closed subschemes, for Stacks Tag 0EXH

Let `fW : W ⟶ T` be a morphism of schemes in characteristic `p` with `T` quasi-compact and
quasi-separated, and let `W` be covered by two closed subschemes `W₁` and `W₂`, the second one the
inverse image `W ×_T T₂` of a closed subscheme `T₂ ⊆ T`. Suppose `W₁ ⟶ T` is proper and surjective
with geometrically connected fibres. If a finite locally free `colim_F 𝒪_W`-module `ℬ` restricts
on `W₁` to the pullback of some `ξ` on `T`, and on `W₂` to the pullback of some `ξ₂` on `T₂`, then
`ℬ` is the pullback of `ξ`.

This is the step of the proof of Stacks Tag 0EXH that glues the descent over the strict transform
and the descent over the exceptional part: `{W₁ ⟶ W, W₂ ⟶ W}` is an h covering by two closed
immersions, and in the stack of Stacks Tag 0EXE an isomorphism over `W₁` between `ℬ` and the
pullback of `ξ` extends uniquely over `W₂`, since over `W₂` both are pulled back from `T₂` along
a morphism which, as well as its restriction to `W₁ ×_W W₂`, has fully faithful pullback
(part (1) of Stacks Tag 0EXH); see `CategoryTheory.Pseudofunctor.exists_map_eq_of_monoPair`.

## Main results

* `AlgebraicGeometry.exists_frobeniusColimitVectorBundlesPullback_iso_of_closedCover`.
* `AlgebraicGeometry.mem_essImage_of_closedCover`: the same for `colim_F Vect`.

## References

* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable {W T W₁ W₂ T₂ : Scheme.{u}} {fW : W ⟶ T} {i₁ : W₁ ⟶ W} {i₂ : W₂ ⟶ W} {t : T₂ ⟶ T}
  {f₂ : W₂ ⟶ T₂}

/-- The source of a quasi-compact quasi-separated morphism to a quasi-compact quasi-separated
scheme is quasi-compact and quasi-separated. -/
private theorem compactSpace_and_quasiSeparatedSpace_of_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    CompactSpace X ∧ QuasiSeparatedSpace X :=
  ⟨QuasiCompact.compactSpace_of_compactSpace f, quasiSeparatedSpace_of_quasiSeparated f⟩

/-- **Gluing over a cover by two closed subschemes, for finite locally free
`colim_F 𝒪`-modules.** -/
theorem exists_frobeniusColimitVectorBundlesPullback_iso_of_closedCover
    (sq : IsPullback i₂ f₂ fW t) [IsClosedImmersion i₁] [IsClosedImmersion t]
    [LocallyOfFinitePresentation i₁] [LocallyOfFinitePresentation t]
    (hcov : Set.range i₁ ∪ Set.range i₂ = Set.univ) (p : ℕ) [Fact p.Prime]
    (hW : IsInCharacteristic W p) (hT : IsInCharacteristic T p)
    (hW₁ : IsInCharacteristic W₁ p) (hW₂ : IsInCharacteristic W₂ p)
    (hT₂ : IsInCharacteristic T₂ p) [CompactSpace T] [QuasiSeparatedSpace T]
    [IsProper (i₁ ≫ fW)] [Surjective (i₁ ≫ fW)] [GeometricallyConnected (i₁ ≫ fW)]
    (Bv : frobeniusColimitVectorBundles W p hW) (ξ : frobeniusColimitVectorBundles T p hT)
    (e₁ : (frobeniusColimitVectorBundlesPullback p (i₁ ≫ fW) hW₁ hT).obj ξ ≅
      (frobeniusColimitVectorBundlesPullback p i₁ hW₁ hW).obj Bv)
    (ξ₂ : frobeniusColimitVectorBundles T₂ p hT₂)
    (e₂ : (frobeniusColimitVectorBundlesPullback p f₂ hW₂ hT₂).obj ξ₂ ≅
      (frobeniusColimitVectorBundlesPullback p i₂ hW₂ hW).obj Bv) :
    Nonempty ((frobeniusColimitVectorBundlesPullback p fW hW hT).obj ξ ≅ Bv) := by
  classical
  have : IsClosedImmersion i₂ :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback sq.flip inferInstance
  have : LocallyOfFinitePresentation i₂ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) sq.flip inferInstance
  obtain ⟨B, hB⟩ := BigHSite.exists_containing ({W, T, W₁, W₂, T₂} : Set Scheme.{u})
  have hWB : B.Contains W := hB W (by simp)
  have hTB : B.Contains T := hB T (by simp)
  have hW₁B : B.Contains W₁ := hB W₁ (by simp)
  have hW₂B : B.Contains W₂ := hB W₂ (by simp)
  have hT₂B : B.Contains T₂ := hB T₂ (by simp)
  let Sc := BigHOver.toScheme B T hTB
  -- the objects and morphisms of the site over `T`
  let To : BigHOver B T hTB := Over.mk (𝟙 (B.obj T hTB))
  let Wo : BigHOver B T hTB := Over.mk (ObjectProperty.homMk fW : B.obj W hWB ⟶ B.obj T hTB)
  let W₁o : BigHOver B T hTB :=
    Over.mk (ObjectProperty.homMk (i₁ ≫ fW) : B.obj W₁ hW₁B ⟶ B.obj T hTB)
  let W₂o : BigHOver B T hTB :=
    Over.mk (ObjectProperty.homMk (i₂ ≫ fW) : B.obj W₂ hW₂B ⟶ B.obj T hTB)
  let T₂o : BigHOver B T hTB := Over.mk (ObjectProperty.homMk t : B.obj T₂ hT₂B ⟶ B.obj T hTB)
  let i₁o : W₁o ⟶ Wo := Over.homMk (ObjectProperty.homMk i₁) rfl
  let i₂o : W₂o ⟶ Wo := Over.homMk (ObjectProperty.homMk i₂) rfl
  let f₂o : W₂o ⟶ T₂o := Over.homMk (ObjectProperty.homMk f₂) (by
    apply ObjectProperty.hom_ext
    exact sq.w.symm)
  -- the stack of Stacks Tag 0EXE over `T`
  let 𝒢 := frobeniusVectorBundleGroupoidPseudofunctor B T hTB p hT
  have : 𝒢.IsStack (BigHOver.topology B T hTB) :=
    (isStack_frobeniusVectorBundleGroupoidFibration_iff B T hTB p hT _).1
      (Functor.isStack_of_isStackInGroupoids
        (frobeniusVectorBundleGroupoidFibration_isStackInGroupoids B T hTB p hT))
  -- the two members are monomorphisms of the site
  have : Mono i₁o := Sc.mono_of_mono_map (inferInstanceAs (Mono i₁))
  have : Mono i₂o := Sc.mono_of_mono_map (inferInstanceAs (Mono i₂))
  -- they form an h covering
  have hcovS : Sieve.ofArrows _ (Pseudofunctor.monoPairHom i₁o i₂o) ∈
      BigHOver.topology B T hTB Wo := by
    let E : PreZeroHypercover.{u + 1} Wo :=
      ⟨ULift Bool, fun b ↦ Pseudofunctor.monoPairObj (X₁ := W₁o) (X₂ := W₂o) b.down,
        fun b ↦ Pseudofunctor.monoPairHom i₁o i₂o b.down⟩
    have hE : IsHCovering (E.map Sc).X (E.map Sc).f := by
      refine (isHCovering_bool_of_isProper_of_range_union
        (fun b ↦ Sc.obj (Pseudofunctor.monoPairObj (X₁ := W₁o) (X₂ := W₂o) b))
        (fun b ↦ Sc.map (Pseudofunctor.monoPairHom i₁o i₂o b))
        (by
          rintro (_ | _)
          exacts [inferInstanceAs (LocallyOfFinitePresentation i₁),
            inferInstanceAs (LocallyOfFinitePresentation i₂)])
        (by
          rintro (_ | _)
          exacts [inferInstanceAs (IsProper i₁), inferInstanceAs (IsProper i₂)])
        hcov).reindex Equiv.ulift
    have h := BigHOver.sieve₀_mem_topology_of_isHCovering B T hTB E hE
    have hP : E.presieve₀ = Presieve.ofArrows _ (Pseudofunctor.monoPairHom i₁o i₂o) := by
      funext Y g
      exact propext ⟨fun ⟨b⟩ ↦ ⟨b.down⟩, fun ⟨b⟩ ↦ ⟨ULift.up b⟩⟩
    rwa [hP] at h
  have hff := 𝒢.fullyFaithfulToDescentData (J := BigHOver.topology B T hTB)
    (Pseudofunctor.monoPairHom i₁o i₂o) hcovS
  -- the intersection of the two members
  let P := pullback i₁o i₂o
  let j₁o := pullback.fst i₁o i₂o
  let j₂o := pullback.snd i₁o i₂o
  have hsqo : IsPullback j₁o j₂o i₁o i₂o := IsPullback.of_hasPullback i₁o i₂o
  have hsqS : IsPullback (Sc.map j₁o) (Sc.map j₂o) i₁ i₂ := hsqo.map Sc
  have hsqP : IsPullback (Sc.map j₁o) (Sc.map j₂o ≫ f₂) (i₁ ≫ fW) t := hsqS.paste_vert sq
  let ja := j₂o ≫ f₂o
  have : IsProper (Sc.map ja) :=
    MorphismProperty.of_isPullback (P := @IsProper) hsqP ‹_›
  have : Surjective (Sc.map ja) :=
    MorphismProperty.of_isPullback (P := @Surjective) hsqP ‹_›
  have : GeometricallyConnected (Sc.map ja) :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hsqP ‹_›
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_hom (X := Sc.obj T₂o) t
  obtain ⟨hfu, hfa⟩ := fullyFaithful_frobeniusColimitVectorBundlesPullback (Sc.map ja) p
    (isInCharacteristic_bigHOver B T hTB p hT P) (isInCharacteristic_bigHOver B T hTB p hT T₂o)
  have : (𝒢.map ja.op.toLoc).toFunctor.Full :=
    full_frobeniusVectorBundleGroupoidPseudofunctor_map B T hTB p hT ja
  -- objects of the stack from finite locally free modules, and isomorphisms
  let toG : ∀ {U : BigHOver B T hTB}, frobeniusColimitVectorBundles (Sc.obj U) p
      (isInCharacteristic_bigHOver B T hTB p hT U) → 𝒢.obj ⟨op U⟩ :=
    fun A ↦ ⟨⟨A.obj⟩, A.property⟩
  let toGIso : ∀ {U : BigHOver B T hTB} {A A' : frobeniusColimitVectorBundles (Sc.obj U) p
      (isInCharacteristic_bigHOver B T hTB p hT U)}, (A ≅ A') → (toG A ≅ toG A') :=
    fun i ↦ (ObjectProperty.fullyFaithfulι _).preimageIso
      (Core.isoMk ((ObjectProperty.ι _).mapIso i))
  let M : 𝒢.obj ⟨op Wo⟩ := toG (U := Wo) Bv
  let N : 𝒢.obj ⟨op Wo⟩ := toG (U := Wo) ((frobeniusColimitVectorBundlesPullback p fW hW hT).obj ξ)
  -- the isomorphism over `W₁`
  let x₁ : (𝒢.map i₁o.op.toLoc).toFunctor.obj M ⟶ (𝒢.map i₁o.op.toLoc).toFunctor.obj N :=
    (toGIso (U := W₁o) (e₁.symm ≪≫
      ((frobeniusColimitVectorBundlesPullbackComp p i₁ fW hW₁ hW hT).app ξ).symm)).hom
  -- the pullbacks to `W₂` come from `T₂`
  let eM : (𝒢.map i₂o.op.toLoc).toFunctor.obj M ≅
      (𝒢.map f₂o.op.toLoc).toFunctor.obj (toG (U := T₂o) ξ₂) :=
    toGIso (U := W₂o) e₂.symm
  let eN : (𝒢.map i₂o.op.toLoc).toFunctor.obj N ≅
      (𝒢.map f₂o.op.toLoc).toFunctor.obj
        (toG (U := T₂o) ((frobeniusColimitVectorBundlesPullback p t hT₂ hT).obj ξ)) :=
    toGIso (U := W₂o) ((frobeniusColimitVectorBundlesPullbackComp p i₂ fW hW₂ hW hT).app ξ ≪≫
      eqToIso (congrArg (fun k ↦ (frobeniusColimitVectorBundlesPullback p k hW₂ hT).obj ξ)
        sq.w) ≪≫
      ((frobeniusColimitVectorBundlesPullbackComp p f₂ t hW₂ hT₂ hT).app ξ).symm)
  obtain ⟨φ, -⟩ := Pseudofunctor.exists_map_eq_of_monoPair 𝒢 hsqo hff
    (Pseudofunctor.surjective_map_of_full 𝒢 j₂o f₂o ja rfl eM eN) x₁
  exact ⟨ObjectProperty.isoMk _ φ.hom.iso.symm⟩

/-- **Gluing over a cover by two closed subschemes, for `colim_F Vect`** (the exceptional-divisor
step of the proof of Stacks Tag 0EXH). Let `fW : W ⟶ T` with `T` quasi-compact quasi-separated, and
let `W` be covered by closed subschemes `W₁` and `W₂ = W ×_T T₂` with `T₂ ⊆ T` closed, `W₁ ⟶ T`
proper and surjective with geometrically connected fibres. If the pullback of `ℬ` to `W₁` comes
from `T` and its pullback to `W₂` comes from `T₂`, then `ℬ` comes from `T`. -/
theorem mem_essImage_of_closedCover (sq : IsPullback i₂ f₂ fW t) [IsClosedImmersion i₁]
    [IsClosedImmersion t] [LocallyOfFinitePresentation i₁] [LocallyOfFinitePresentation t]
    (hcov : Set.range i₁ ∪ Set.range i₂ = Set.univ) (p : ℕ) [Fact p.Prime]
    (hW : IsInCharacteristic W p) (hT : IsInCharacteristic T p)
    (hW₁ : IsInCharacteristic W₁ p) (hW₂ : IsInCharacteristic W₂ p)
    (hT₂ : IsInCharacteristic T₂ p) [CompactSpace T] [QuasiSeparatedSpace T] [QuasiCompact fW]
    [QuasiSeparated fW]
    [IsProper (i₁ ≫ fW)] [Surjective (i₁ ≫ fW)] [GeometricallyConnected (i₁ ≫ fW)]
    (A : frobeniusColimitVectModel W p hW)
    (h₁ : (frobeniusColimitVectModelPullback (i₁ ≫ fW) p hW₁ hT).essImage
      ((frobeniusColimitVectModelPullback i₁ p hW₁ hW).obj A))
    (h₂ : (frobeniusColimitVectModelPullback f₂ p hW₂ hT₂).essImage
      ((frobeniusColimitVectModelPullback i₂ p hW₂ hW).obj A)) :
    (frobeniusColimitVectModelPullback fW p hW hT).essImage A := by
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_hom fW
  have : IsClosedImmersion i₂ :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback sq.flip inferInstance
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_hom i₁
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_hom i₂
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_of_hom t
  have := fun (X : Scheme.{u}) hX [CompactSpace X] [QuasiSeparatedSpace X] ↦
    isEquivalence_frobeniusColimitVectComparison X p hX
  obtain ⟨B₁, ⟨b₁⟩⟩ := h₁
  obtain ⟨B₂, ⟨b₂⟩⟩ := h₂
  let Cmp := fun (X : Scheme.{u}) (hX : IsInCharacteristic X p) ↦
    frobeniusColimitVectComparison X p hX
  let e₁ : (frobeniusColimitVectorBundlesPullback p (i₁ ≫ fW) hW₁ hT).obj ((Cmp T hT).obj B₁) ≅
      (frobeniusColimitVectorBundlesPullback p i₁ hW₁ hW).obj ((Cmp W hW).obj A) :=
    frobeniusColimitVectComparisonPullbackObjIso p (i₁ ≫ fW) hW₁ hT B₁ ≪≫
      (Cmp W₁ hW₁).mapIso b₁ ≪≫ (frobeniusColimitVectComparisonPullbackObjIso p i₁ hW₁ hW A).symm
  let e₂ : (frobeniusColimitVectorBundlesPullback p f₂ hW₂ hT₂).obj ((Cmp T₂ hT₂).obj B₂) ≅
      (frobeniusColimitVectorBundlesPullback p i₂ hW₂ hW).obj ((Cmp W hW).obj A) :=
    frobeniusColimitVectComparisonPullbackObjIso p f₂ hW₂ hT₂ B₂ ≪≫
      (Cmp W₂ hW₂).mapIso b₂ ≪≫ (frobeniusColimitVectComparisonPullbackObjIso p i₂ hW₂ hW A).symm
  obtain ⟨e⟩ := exists_frobeniusColimitVectorBundlesPullback_iso_of_closedCover sq hcov p hW hT
    hW₁ hW₂ hT₂ ((Cmp W hW).obj A) ((Cmp T hT).obj B₁) e₁ ((Cmp T₂ hT₂).obj B₂) e₂
  exact ⟨B₁, ⟨(Functor.FullyFaithful.ofFullyFaithful (Cmp W hW)).preimageIso
    ((frobeniusColimitVectComparisonPullbackObjIso p fW hW hT B₁).symm ≪≫ e)⟩⟩

end AlgebraicGeometry

end
