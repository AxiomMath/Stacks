module

public import StacksFrontier.AlgebraicGeometry.Perfect.BottomRankChart
public import Mathlib.AlgebraicGeometry.Sites.Representability

/-!
# Existence of the bottom rank stratum of a perfect complex

Let `X` be a scheme, `E` an object of `D(𝒪_X)` which is perfect of Tor amplitude in `[a, b]`, and
`r` a natural number. The morphisms `f : Y ⟶ X` which are universally of bottom rank `r` for `E`
in degree `a` form a Zariski sheaf on the category of schemes. On a chart `Spec R ⟶ X` it is
represented by the rank `r` Fitting stratum of the dual cokernel sheaf of the chart, a locally
closed subscheme of `Spec R`. These open subfunctors cover the sheaf, so it is representable
([stacks 01JJ]) by a scheme `Z` with a monomorphism `j : Z ⟶ X`, and over each chart `j` is the
Fitting stratum of the chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.BottomRankStratum

variable {X : Scheme.{u}} (E : DerivedCategory X.Modules) (a : ℤ) (r : ℕ)

/-- **Being universally of bottom rank `r` is local on the source.** -/
theorem IsUniversallyFreeBottom.of_openCover {Y : Scheme.{u}} {f : Y ⟶ X} (𝒰 : Y.OpenCover)
    (h : ∀ i, IsUniversallyFreeBottom E a r (𝒰.f i ≫ f)) : IsUniversallyFreeBottom E a r f := by
  intro Y' g
  rw [← Scheme.Modules.isFiniteLocallyFreeOfRank_iff]
  refine isFiniteLocallyFreeOfRank_of_forall_exists_openImmersion _ r fun y => ?_
  refine ⟨_, pullback.fst g (𝒰.f (𝒰.idx (g.base y))), inferInstance, ?_, ?_⟩
  · rw [IsOpenImmersion.range_pullbackFst]
    exact 𝒰.covers (g.base y)
  · refine Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso
      (pullbackHomologyRestrictIso E a _ (g ≫ f)) ?_
    rw [pullback.condition_assoc, Scheme.Modules.isFiniteLocallyFreeOfRank_iff]
    exact h _ _ _

/-- **The subfunctor of morphisms universally of bottom rank `r`.** -/
def universallyFreeBottomSubfunctor : Subfunctor (yoneda.obj X) where
  obj Y := {f | IsUniversallyFreeBottom E a r (X := X) (Y := Y.unop) f}
  map i _ hf := hf.comp i.unop

/-- **The sheaf of morphisms universally of bottom rank `r`.** It is a subfunctor of the functor
of points of `X`, which is a Zariski sheaf, and the condition is local on the source. -/
def universallyFreeBottomSheaf : Sheaf Scheme.zariskiTopology.{u} (Type u) where
  obj := (universallyFreeBottomSubfunctor E a r).toFunctor
  property := by
    rw [isSheaf_iff_isSheaf_of_type, Subfunctor.isSheaf_iff _
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
        (J := Scheme.zariskiTopology) (yoneda.obj X))]
    intro Y f hf
    obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hf
    exact IsUniversallyFreeBottom.of_openCover E a r 𝒰 fun i => h𝒰 _ _ (Presieve.ofArrows.mk i)

/-! ### The stratum of a chart -/

namespace Chart

variable {E a} (c : Chart E a)

/-- **The stratum of a chart.** The rank `r` Fitting stratum of the dual cokernel sheaf of the
chart, a locally closed subscheme of `Spec R`. -/
abbrev stratum : Over (Spec c.R) := fittingRankStratum c.dualCoker r

/-- **The stratum of a chart represents the universal bottom rank condition on the chart.** -/
theorem factorsThrough_stratum_iff {T : Scheme.{u}} (t : T ⟶ Spec c.R) :
    (∃ u : T ⟶ (c.stratum r).left, u ≫ (c.stratum r).hom = t) ↔
      IsUniversallyFreeBottom E a r (t ≫ c.ι) := by
  rw [c.isUniversallyFreeBottom_comp_iff t r]
  obtain ⟨rep⟩ := rankRFunctor_representableBy_fittingRankStratum c.dualCoker r
  constructor
  · rintro ⟨u, hu⟩
    exact (rep.homEquiv (Over.homMk u hu : Over.mk t ⟶ c.stratum r)).down.down
  · intro h
    let v := rep.homEquiv.symm
      (⟨⟨h⟩⟩ : (rankRFunctor (Spec c.R) c.dualCoker r).obj (op (Over.mk t)))
    exact ⟨v.left, v.w⟩

/-- The stratum of a chart, as a point of the sheaf of morphisms universally of bottom rank. -/
def stratumPoint : (universallyFreeBottomSheaf E a r).obj.obj (op (c.stratum r).left) :=
  ⟨(c.stratum r).hom ≫ c.ι, (c.factorsThrough_stratum_iff r _).1 ⟨𝟙 _, Category.id_comp _⟩⟩

/-- The stratum of a chart, as a morphism from its functor of points. -/
def stratumHom : yoneda.obj (c.stratum r).left ⟶ (universallyFreeBottomSheaf E a r).obj :=
  yonedaEquiv.symm (c.stratumPoint r)

/-- The morphism `stratumHom` sends `z` to the composite of `z` with the stratum and the chart. -/
theorem stratumHom_app_val {V : Scheme.{u}ᵒᵖ} (z : V.unop ⟶ (c.stratum r).left) :
    ((c.stratumHom r).app V z).1 = z ≫ (c.stratum r).hom ≫ c.ι := rfl

/-- The structural morphism of the stratum of a chart composed with the chart is a
monomorphism. -/
instance : Mono ((c.stratum r).hom ≫ c.ι) := by
  have := isImmersion_fittingRankStratum c.dualCoker r
  infer_instance

/-- A morphism into `X` restricted to the preimage of the image of a chart lifts to `Spec R`. -/
private theorem exists_comp_chart_eq {T : Scheme.{u}} (t : T ⟶ X) :
    ∃ s : (t ⁻¹ᵁ c.ι.opensRange).toScheme ⟶ Spec c.R,
      s ≫ c.ι = (t ⁻¹ᵁ c.ι.opensRange).ι ≫ t :=
  ⟨IsOpenImmersion.lift c.ι _ (by rintro _ ⟨x, rfl⟩; exact x.2), IsOpenImmersion.lift_fac _ _ _⟩

/-- A morphism universally of bottom rank, restricted to the preimage of a chart, factors through
the stratum of the chart. -/
private theorem exists_stratum_lift_aux {T : Scheme.{u}} (t : T ⟶ X)
    (ht : IsUniversallyFreeBottom E a r t) :
    ∃ u : (t ⁻¹ᵁ c.ι.opensRange).toScheme ⟶ (c.stratum r).left,
      u ≫ (c.stratum r).hom ≫ c.ι = (t ⁻¹ᵁ c.ι.opensRange).ι ≫ t := by
  obtain ⟨s, hs⟩ := c.exists_comp_chart_eq t
  obtain ⟨u, hu⟩ := (c.factorsThrough_stratum_iff r s).2 (by rw [hs]; exact ht.comp _)
  exact ⟨u, by rw [← Category.assoc, hu, hs]⟩

/-- **The stratum of a chart is an open subfunctor of the sheaf of morphisms universally of bottom
rank.** The pullback along a point `t : T ⟶ X` is the open subscheme `t⁻¹(Spec R)` of `T`: a
morphism into it lands in the chart, and there it factors uniquely through the stratum. -/
theorem isOpenImmersion_presheaf_stratumHom :
    IsOpenImmersion.presheaf (c.stratumHom r) := by
  refine MorphismProperty.relative.of_exists fun T g => ?_
  set t := (yonedaEquiv g).1
  have ht : IsUniversallyFreeBottom E a r t := (yonedaEquiv g).2
  have hg (V : Scheme.{u}ᵒᵖ) (w : V.unop ⟶ T) : (g.app V w).1 = w ≫ t := by
    have h := NatTrans.naturality_apply g w.op (𝟙 T)
    rw [show (yoneda.obj T).map w.op (𝟙 T) = w from Category.comp_id w] at h
    rw [h]
    rfl
  let U := t ⁻¹ᵁ c.ι.opensRange
  obtain ⟨u, huj⟩ := c.exists_stratum_lift_aux r t ht
  refine ⟨U.toScheme, yoneda.map u, U.ι, ?_, inferInstance⟩
  refine IsPullback.of_forall_isPullback_app fun V => ?_
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext s
    apply Subtype.ext
    show ((c.stratumHom r).app V (s ≫ u)).1 = (g.app V (s ≫ U.ι)).1
    rw [stratumHom_app_val, hg, Category.assoc, huj, Category.assoc]
  · rintro s₁ s₂ ⟨-, h₂⟩
    exact (cancel_mono U.ι).1 h₂
  · intro z w hzw
    have hzw' : z ≫ (c.stratum r).hom ≫ c.ι = w ≫ t := by
      rw [← stratumHom_app_val, ← hg]
      exact congrArg Subtype.val hzw
    have hw : Set.range w.base ⊆ Set.range U.ι.base := by
      rintro _ ⟨v, rfl⟩
      rw [Scheme.Opens.range_ι]
      show t.base (w.base v) ∈ c.ι.opensRange
      rw [← Scheme.Hom.comp_apply, ← hzw', Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    refine ⟨IsOpenImmersion.lift U.ι w hw, ?_, IsOpenImmersion.lift_fac _ _ _⟩
    show IsOpenImmersion.lift U.ι w hw ≫ u = z
    refine (cancel_mono ((c.stratum r).hom ≫ c.ι)).1 ?_
    rw [Category.assoc, huj, ← Category.assoc, IsOpenImmersion.lift_fac, hzw']

/-- A morphism universally of bottom rank, restricted to the preimage of a chart, factors through
the stratum of the chart. -/
theorem exists_stratum_lift {T : Scheme.{u}} (t : T ⟶ X) (ht : IsUniversallyFreeBottom E a r t) :
    ∃ u : (t ⁻¹ᵁ c.ι.opensRange).toScheme ⟶ (c.stratum r).left,
      u ≫ (c.stratum r).hom ≫ c.ι = (t ⁻¹ᵁ c.ι.opensRange).ι ≫ t := by
  exact c.exists_stratum_lift_aux r t ht

end Chart

/-! ### Gluing the strata of the charts -/

section Glue

variable {E a} (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
  (b : ℤ) (htor : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace E a b)

/-- A chart around a point. -/
def chartAt (x : X) : Chart E a := (Chart.exists_mem E hE a b htor x).choose

/-- The chart `chartAt x` contains the point `x` in its image. -/
theorem mem_range_chartAt (x : X) : x ∈ Set.range (chartAt hE b htor x).ι.base :=
  let ⟨y, hy, _⟩ := (Chart.exists_mem E hE a b htor x).choose_spec
  ⟨y, hy⟩

/-- The degree `i` term of the complex of the chart `chartAt x` is free of rank the derived fibre
Betti number of `E` at `x` in degree `i`. -/
theorem nonempty_chartAt_X_equiv (x : X) (i : ℤ) :
    Nonempty ((chartAt hE b htor x).P.X i ≃ₗ[(chartAt hE b htor x).R]
      (Fin (DerivedFibreBetti.derivedFiberBetti X E
        (Scheme.Modules.isPseudoCoherent_of_isPerfect E hE) i x) →
          (chartAt hE b htor x).R)) :=
  let ⟨_, _, h⟩ := (Chart.exists_mem E hE a b htor x).choose_spec
  h i

/-- The strata of the charts `chartAt x`, for `x : X`, jointly cover the sheaf of morphisms
universally of bottom rank `r` Zariski locally. -/
instance isLocallySurjective_sigmaDesc_stratumHom :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc fun x : X => (chartAt hE b htor x).stratumHom r) where
  imageSieve_mem {T} s := by
    set t := s.1
    have ht : IsUniversallyFreeBottom E a r t := s.2
    let c := fun y : T => chartAt hE b htor (t.base y)
    let 𝒰 : T.OpenCover := Scheme.Cover.mkOfCovers T
      (fun y => (t ⁻¹ᵁ (c y).ι.opensRange).toScheme) (fun y => (t ⁻¹ᵁ (c y).ι.opensRange).ι)
      (fun y => ⟨y, ⟨y, mem_range_chartAt hE b htor (t.base y)⟩, rfl⟩)
    refine Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, ?_⟩
    rintro _ _ ⟨y⟩
    obtain ⟨u, hu⟩ := (c (show T from y)).exists_stratum_lift r t ht
    refine ⟨(Sigma.ι (fun x : X => yoneda.obj ((chartAt hE b htor x).stratum r).left)
      (t.base (show T from y))).app _ u, ?_⟩
    change ((Sigma.ι (fun x : X => yoneda.obj ((chartAt hE b htor x).stratum r).left)
      (t.base (show T from y)) ≫
        Sigma.desc fun x : X => (chartAt hE b htor x).stratumHom r).app _) u = _
    rw [Sigma.ι_desc]
    exact Subtype.ext hu

/-- **The bottom rank stratum exists.** There is a scheme `Z` with a monomorphism `j : Z ⟶ X`
through which a morphism factors exactly when it is universally of bottom rank `r`. -/
theorem exists_mono_factorsThrough_iff
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (b : ℤ) (htor : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace E a b) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X), Mono j ∧
      ∀ (Y : Scheme.{u}) (f : Y ⟶ X), (∃ g : Y ⟶ Z, g ≫ j = f) ↔
        IsUniversallyFreeBottom E a r f := by
  let rep := Scheme.LocalRepresentability.representableBy
    (fun x : X => (chartAt hE b htor x).isOpenImmersion_presheaf_stratumHom r)
  set Z := (Scheme.LocalRepresentability.glueData
    (fun x : X => (chartAt hE b htor x).isOpenImmersion_presheaf_stratumHom r)).glued
  set j : Z ⟶ X := (rep.homEquiv (𝟙 Z)).1
  have hrep {Y : Scheme.{u}} (g : Y ⟶ Z) : (rep.homEquiv g).1 = g ≫ j := by
    have := rep.homEquiv_comp g (𝟙 Z)
    rw [Category.comp_id] at this
    rw [this]
    rfl
  refine ⟨Z, j, ⟨fun g₁ g₂ h => rep.homEquiv.injective (Subtype.ext (by rw [hrep, hrep, h]))⟩,
    fun Y f => ⟨?_, fun hf => ?_⟩⟩
  · rintro ⟨g, rfl⟩
    rw [← hrep]
    exact (rep.homEquiv g).2
  · let σ : (universallyFreeBottomSheaf E a r).obj.obj (op Y) := ⟨f, hf⟩
    refine ⟨rep.homEquiv.symm σ, ?_⟩
    rw [← hrep]
    exact congrArg Subtype.val (rep.homEquiv.apply_symm_apply σ)

/-- **Two monomorphisms through which the same morphisms factor are isomorphic over the
target.** -/
theorem exists_iso_of_forall_factorsThrough_iff {A A' B : Scheme.{u}} (m : A ⟶ B) (m' : A' ⟶ B)
    [Mono m] [Mono m']
    (h : ∀ (T : Scheme.{u}) (t : T ⟶ B), (∃ v : T ⟶ A, v ≫ m = t) ↔ ∃ v : T ⟶ A', v ≫ m' = t) :
    ∃ e : A ≅ A', e.hom ≫ m' = m := by
  obtain ⟨g₁, hg₁⟩ := (h A m).1 ⟨𝟙 A, Category.id_comp m⟩
  obtain ⟨g₂, hg₂⟩ := (h A' m').2 ⟨𝟙 A', Category.id_comp m'⟩
  refine ⟨⟨g₁, g₂, ?_, ?_⟩, hg₁⟩
  · exact (cancel_mono m).1 (by rw [Category.assoc, hg₂, hg₁, Category.id_comp])
  · exact (cancel_mono m').1 (by rw [Category.assoc, hg₁, hg₂, Category.id_comp])

/-- **Over a chart, the representing monomorphism is the stratum of the chart.** -/
theorem exists_iso_pullback_snd_stratum {Z : Scheme.{u}} (j : Z ⟶ X) [Mono j]
    (hj : ∀ (Y : Scheme.{u}) (f : Y ⟶ X), (∃ g : Y ⟶ Z, g ≫ j = f) ↔
      IsUniversallyFreeBottom E a r f) (c : Chart E a) :
    ∃ e : pullback j c.ι ≅ (c.stratum r).left,
      e.hom ≫ (c.stratum r).hom = pullback.snd j c.ι := by
  have := isImmersion_fittingRankStratum c.dualCoker r
  refine exists_iso_of_forall_factorsThrough_iff _ _ fun T t => ?_
  rw [c.factorsThrough_stratum_iff r t, ← hj]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v ≫ pullback.fst j c.ι, by rw [Category.assoc, pullback.condition, Category.assoc]⟩
  · rintro ⟨g, hg⟩
    exact ⟨pullback.lift g t hg, pullback.lift_snd _ _ _⟩

/-- **A property local at the target holds for the representing monomorphism when it holds for
the strata of the charts.** -/
theorem prop_of_forall_chartAt
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (b : ℤ) (htor : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace E a b)
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P] {Z : Scheme.{u}} (j : Z ⟶ X)
    [Mono j]
    (hj : ∀ (Y : Scheme.{u}) (f : Y ⟶ X), (∃ g : Y ⟶ Z, g ≫ j = f) ↔
      IsUniversallyFreeBottom E a r f)
    (h : ∀ x : X, P ((chartAt hE b htor x).stratum r).hom) : P j := by
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers X (fun x => Spec (chartAt hE b htor x).R)
    (fun x => (chartAt hE b htor x).ι) (fun x => ⟨x, mem_range_chartAt hE b htor x⟩)
  refine IsZariskiLocalAtTarget.of_openCover 𝒰 fun x => ?_
  obtain ⟨e, he⟩ := exists_iso_pullback_snd_stratum r j hj (chartAt hE b htor x)
  refine (P.arrow_mk_iso_iff (Arrow.isoMk e (Iso.refl _) ?_)).2 (h x)
  show e.hom ≫ (Chart.stratum r (chartAt hE b htor x)).hom ≫ 𝟙 _ = pullback.snd j _
  rw [Category.comp_id, he]

/-- **Under the Betti bound `β_a ≤ r`, plain local freeness of the bottom cohomology is the
universal condition.** -/
theorem isUniversallyFreeBottom_of_isFiniteLocallyFreeOfRank
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (b : ℤ) (htor : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace E a b)
    (hβ : ∀ x : X, DerivedFibreBetti.derivedFiberBetti X E
      (Scheme.Modules.isPseudoCoherent_of_isPerfect E hE) a x ≤ r)
    {Y : Scheme.{u}} (f : Y ⟶ X)
    (h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (pullbackHomology E a f) r) :
    IsUniversallyFreeBottom E a r f := by
  let c := fun y : Y => chartAt hE b htor (f.base y)
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y
    (fun y => (f ⁻¹ᵁ (c y).ι.opensRange).toScheme) (fun y => (f ⁻¹ᵁ (c y).ι.opensRange).ι)
    (fun y => ⟨y, ⟨y, mem_range_chartAt hE b htor (f.base y)⟩, rfl⟩)
  refine IsUniversallyFreeBottom.of_openCover E a r 𝒰 fun y => ?_
  let U := f ⁻¹ᵁ (c y).ι.opensRange
  obtain ⟨t, ht⟩ := (c y).exists_comp_chart_eq f
  show IsUniversallyFreeBottom E a r (U.ι ≫ f)
  rw [← ht, (c y).isUniversallyFreeBottom_comp_iff t r]
  refine (c y).isFiniteLocallyFreeOfRank_pullback_dualCoker_of_isGeneratedByNear t r
    (fun z => ((c y).isGeneratedByNear_dualCoker_iff _ r z).2 (hβ _)) ?_
  rw [ht, ← Scheme.Modules.isFiniteLocallyFreeOfRank_iff] at *
  exact (h.restrict U.ι).of_iso (pullbackHomologyRestrictIso E a U.ι f).symm

end Glue

end AlgebraicGeometry.BottomRankStratum

end
