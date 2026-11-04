module

public import Mathlib.Algebra.Category.Grp.Basic
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Situation
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalIsSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalPullbacks
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismDefs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Component inclusions in a simplicial site

In either form of the simplicial-site situation, the inclusion of a component category into the
total category is continuous and cocontinuous. The cocontinuous functor therefore induces a
canonical morphism from the component topos to the total topos, and inverse image along that
morphism has a left adjoint: the sheafified left Kan extension along the opposite of the
component inclusion.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentFunctor`: the inclusion of one component
  into the total category.
* `CategoryTheory.SimplicialSiteSituation.componentMorphism`: the induced morphism of topoi.
* `CategoryTheory.SimplicialSiteSituation.componentLowerShriek`: the left adjoint of inverse
  image along the component morphism.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentFunctor_isContinuous` and
  `.componentFunctor_isCocontinuous`: the component inclusion is continuous and cocontinuous.
* `CategoryTheory.SimplicialSiteSituation.componentLowerShriek_adjunction_restriction`: lower
  shriek is left adjoint to restriction, in an independent universe of values.
* `CategoryTheory.SimplicialSiteSituation.componentLowerShriek_adjunction`: lower shriek is left
  adjoint to the inverse image of the component morphism of topoi.

## Implementation notes

The component functor is the fibre inclusion into Mathlib's `CoGrothendieck` construction in
case (A), and into its `Grothendieck` construction in case (B). The two independent assertions
of the source are the two instance lemmas. Continuity in case (A) comes from the fibrewise
pullbacks of the total site, and in case (B) from the family-based site axioms of the total
category, repackaged as a `Coverage` so that the induction over `Coverage.Saturate` is
available.

The value universe `w` of `componentLowerShriek` is independent of the site universe `u`. The
construction needs sheafification on the total site and left Kan extensions along the opposite
component inclusion, which are automatic when `w = u`; the adjunction to restriction needs
neither sheafification on the component nor the right Kan extensions used to build the morphism
of topoi.

The `@[stacks 09WG]` annotations below cover two assertions of the tag: the component inclusion
itself — the functor, its continuity and cocontinuity, and the induced morphism of topoi — and
the sheaf-level left adjoint of inverse image, with its adjunction. Two further assertions are
realized by existing declarations rather than new ones, and are recorded at the end of the file:
`CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous` identifies
inverse image along the component inclusion with restriction, while
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback` with
`CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous` is the left adjoint
of inverse image on abelian sheaves. Stacks 09WG asserts in addition that that left adjoint is
exact, that it satisfies a coproduct formula on sheaves of sets and a sum formula on abelian
sheaves, and that it preserves finite connected limits. Those four assertions are proved, each
in its own module rather than here: exactness is
`CategoryTheory.SimplicialSiteSituation.componentLowerShriek_exactFunctor` in
`StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentExact`, the coproduct formula on sheaves of
sets is `CategoryTheory.SimplicialSiteSituation.componentLowerShriek_restrictIsoCoproduct` in
`StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSheafSumFormula`, the sum formula on
abelian sheaves is
`CategoryTheory.SimplicialSiteSituation.componentLowerShriekRestrictionIsoCoproduct` in
`StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumFormula`, and the commutation with
finite connected limits is
`CategoryTheory.SimplicialSiteSituation.componentLowerShriek_preservesLimitsOfShape` in
`StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentConnectedLimits`.

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor

universe u w

namespace CategoryTheory

attribute [local implicit_reducible] CategoryTheory.Grothendieck.ι
  CategoryTheory.SimplicialSite.totalPseudofunctor
  CategoryTheory.Functor.toPseudofunctor' CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc

namespace SimplicialSiteSituation

/-- Turn a family-based site into Mathlib's coverage, recording its base-change axiom as the
pullback compatibility needed by `Coverage`. -/
def coverageFromIsSite {C : Type u} [Category.{u} C]
    (Cov : Covering.{u, u, u} C → Prop) (hCov : IsSite Cov) : Coverage C where
  coverings X := {R | ∃ E : PreZeroHypercover X, Cov ⟨X, E⟩ ∧ E.presieve₀ = R}
  pullback := by
    rintro X Y f _ ⟨E, hE, rfl⟩
    obtain ⟨P, p₁, p₂, hpb, hCov'⟩ := hCov.2.2 ⟨X, E⟩ hE Y f
    let E' : PreZeroHypercover Y := ⟨E.I₀, P, p₂⟩
    refine ⟨E'.presieve₀, ⟨E', hCov', rfl⟩, ?_⟩
    rintro Z g ⟨i⟩
    exact ⟨E.X i, p₁ i, E.f i, ⟨i⟩, (hpb i).w⟩

/-- A functor that sends generating covering families back into a coverage pulls all covering
sieves back to covering sieves. The proof follows the inductive construction of the topology
associated to a coverage. -/
private theorem coverageFunctor_isCocontinuous
    {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)
    (J : Coverage C) (K : Coverage D)
    (hcover : ∀ X (R : Presieve (F.obj X)), R ∈ K (F.obj X) →
      ∃ R' : Presieve X, R' ∈ J X ∧ R'.map F = R) :
    F.IsCocontinuous J.toGrothendieck K.toGrothendieck := by
  constructor
  intro X S hS
  suffices hs : ∀ {Y : D} {T : Sieve Y}, K.Saturate Y T →
      ∀ (X : C) (e : F.obj X = Y),
        J.Saturate X ((e ▸ T).functorPullback F) from
    hs ((Coverage.mem_toGrothendieck (K := K)).mp hS) X rfl
  intro Y T hT
  induction hT with
  | of Y R hR =>
    rintro X rfl
    obtain ⟨R', hR', hmap⟩ := hcover X R hR
    apply Coverage.saturate_of_superset J ?_ (Coverage.Saturate.of X R' hR')
    rw [Sieve.generate_le_iff]
    intro Z f hf
    change (Sieve.generate R) (F.map f)
    rw [← hmap]
    exact Sieve.le_generate _ _ _ (Presieve.map_map hf)
  | top Y =>
    rintro X rfl
    exact Coverage.Saturate.top X
  | transitive Y R T hR hlocal ihR ihlocal =>
    rintro X rfl
    exact Coverage.Saturate.transitive X (R.functorPullback F) (T.functorPullback F)
      (ihR X rfl) fun Z f hf => by simpa [Sieve.functorPullback_pullback] using ihlocal hf Z rfl

/-- If a functor takes the generating presieves of a coverage to covering sieves, it
preserves all covering sieves of the generated topology. -/
private theorem coverageFunctor_isCoverPreserving
    {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)
    (J : Coverage C) (K : Coverage D)
    (hcover : ∀ X (R : Presieve X), R ∈ J X →
      Sieve.generate (R.map F) ∈ K.toGrothendieck (F.obj X)) :
    CoverPreserving J.toGrothendieck K.toGrothendieck F := by
  constructor
  intro X S hS
  suffices hs : ∀ {Y : C} {T : Sieve Y}, J.Saturate Y T →
      T.functorPushforward F ∈ K.toGrothendieck (F.obj Y) from
    hs ((Coverage.mem_toGrothendieck (K := J)).mp hS)
  intro Y T hT
  induction hT with
  | of Y R hR =>
    rw [← Sieve.generate_map_eq_functorPushforward]
    exact hcover Y R hR
  | top Y =>
    simp
  | transitive Y R T hR hlocal ihR ihlocal =>
    apply K.toGrothendieck.transitive ihR _
    intro Z f hf
    obtain ⟨W, a, b, hb, hfac⟩ := hf
    apply K.toGrothendieck.superset_covering ?_
      (K.toGrothendieck.pullback_stable b (ihlocal hb))
    intro V g hg
    obtain ⟨W', a', b', hS', hcomp⟩ := hg
    refine ⟨W', a' ≫ a, b', hS', ?_⟩
    rw [hfac, reassoc_of% hcomp, Functor.map_comp]

/-- **Stacks 09WG.** The canonical inclusion of the category in simplicial degree `n` into the
total category. -/
@[stacks 09WG "component_inclusion"]
def componentFunctor (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    S.component n ⥤ S.totalCategory :=
  match S with
  | ⟨Sum.inl C⟩ => CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)
  | ⟨Sum.inr C⟩ => Grothendieck.ι C.underlying (Opposite.op n)

/-- **Stacks 09WG.** The inclusion of a component in the total site is cocontinuous. -/
@[stacks 09WG "component_inclusion"]
instance componentFunctor_isCocontinuous (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) :
    (componentFunctor S n).IsCocontinuous (S.componentTopology n) S.totalTopology := by
  cases S with
  | mk c =>
    cases c with
    | inl C =>
      let F : C.underlying.obj n ⥤ CoGrothendieck C.totalPseudofunctor :=
        componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n
      change F.IsCocontinuous ((C.coverage n).toGrothendieck) C.totalTopology
      have : C.totalCoverage.HasIsos := C.totalCoverage_hasIsos
      have : C.totalCoverage.HasPullbacks := C.totalCoverage_hasPullbacks
      have : C.totalCoverage.IsStableUnderBaseChange := C.totalCoverage_isStableUnderBaseChange
      have : C.totalCoverage.IsStableUnderComposition := C.totalCoverage_isStableUnderComposition
      constructor
      intro X R hR
      change R ∈ C.totalCoverage.toGrothendieck (F.obj X) at hR
      obtain ⟨T, hT, hTR⟩ := (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition
        (J := C.totalCoverage)).mp hR
      change ∃ Q : Presieve X, Q ∈ C.coverage n X ∧
        Q.map (CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)) = T at hT
      obtain ⟨Q, hQ, hmap⟩ := hT
      change Q.map F = T at hmap
      apply (C.coverage n).toGrothendieck.superset_covering ?_
        (Precoverage.generate_mem_toGrothendieck hQ)
      rw [Sieve.generate_le_iff]
      intro Y f hf
      change R.arrows (F.map f)
      apply hTR
      rw [← hmap]
      exact Presieve.map_map hf
    | inr C =>
      change (Grothendieck.ι C.underlying (Opposite.op n)).IsCocontinuous
        (topologyOfCoverings (C.coverage (Opposite.op n)))
        (SimplicialCoverings.totalTopology C.underlying C.coverage)
      let F := Grothendieck.ι C.underlying (Opposite.op n)
      let J := coverageFromIsSite (C.coverage (Opposite.op n)) (C.isSite (Opposite.op n))
      let K := coverageFromIsSite (SimplicialCoverings.total C.underlying C.coverage)
        (SimplicialCoverings.total_isSite C.underlying C.coverage C.isSite C.isCocontinuous
          C.hasCoverPullbacks)
      have hJ : J.toGrothendieck = topologyOfCoverings (C.coverage (Opposite.op n)) := by
        rw [← Coverage.toGrothendieck_toPrecoverage J]; rfl
      have hK : K.toGrothendieck =
          SimplicialCoverings.totalTopology C.underlying C.coverage := by
        rw [← Coverage.toGrothendieck_toPrecoverage K]; rfl
      rw [← hJ, ← hK]
      refine coverageFunctor_isCocontinuous F J K fun X R hR => ?_
      change ∃ E : PreZeroHypercover (F.obj X),
        SimplicialCoverings.total C.underlying C.coverage ⟨F.obj X, E⟩ ∧ E.presieve₀ = R at hR
      obtain ⟨E, hCov, hR⟩ := hR
      dsimp [SimplicialCoverings.total, F, Grothendieck.ι] at hCov
      obtain ⟨E', hE', hE⟩ := hCov
      have hE' : C.coverage (Opposite.op n) ⟨X, E'⟩ := by simpa using hE'
      have hE : E'.map F = E := by simpa [F, Grothendieck.ι] using hE.symm
      refine ⟨E'.presieve₀, ⟨E', hE', rfl⟩, ?_⟩
      rw [← hR, ← hE, ← PreZeroHypercover.presieve₀_map]

/-- **Stacks 09WG**, case (A). The inclusion of a component into the total category preserves
the pullback of any two members of a covering family of that component.

This is the pullback clause of the continuity criterion of Stacks 00WW for the component
inclusion, and it is what `CategoryTheory.SimplicialSiteSituation.componentFunctor_isContinuous`
feeds to that criterion in case (A). It is stated separately because a functor out of the total
category also needs it: for a morphism between simplicial sites in the continuous case, the
functor between the total categories is continuous because the component inclusions are, and
the argument goes through the preserved pullback of this lemma rather than through continuity
itself. -/
@[stacks 09WG "component_inclusion"]
theorem componentFunctor_pullbacksPreservedBy_inl (C : SimplicialSite.{u})
    (n : SimplexCategory) :
    (C.coverage n).PullbacksPreservedBy
      (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n) :=
  C.coverage_pullbacksPreservedBy_ι n

/-- **Stacks 09WG.** The inclusion of a component in the total site is continuous. -/
@[stacks 09WG "component_inclusion", sga "4 VI 7.4.4" "1)"]
instance componentFunctor_isContinuous (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) :
    (componentFunctor S n).IsContinuous (S.componentTopology n) S.totalTopology := by
  cases S with
  | mk c =>
    cases c with
    | inl C =>
      let F : C.underlying.obj n ⥤ CoGrothendieck C.totalPseudofunctor :=
        componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n
      change F.IsContinuous ((C.coverage n).toGrothendieck) C.totalTopology
      have : (C.coverage n).HasIsos := C.coverage_hasIsos n
      have : (C.coverage n).HasPullbacks := C.coverage_hasPullbacks n
      have : (C.coverage n).IsStableUnderBaseChange := C.coverage_isStableUnderBaseChange n
      have hcover : C.coverage n ≤ C.totalCoverage.comap F := by
        intro X R hR
        change R.map F ∈ C.totalCoverage (F.obj X)
        exact ⟨R, hR, rfl⟩
      have : (C.coverage n).PullbacksPreservedBy F :=
        componentFunctor_pullbacksPreservedBy_inl C n
      exact F.isContinuous_toGrothendieck_of_pullbacksPreservedBy
        (C.coverage n) C.totalCoverage hcover
    | inr C =>
      change (Grothendieck.ι C.underlying (Opposite.op n)).IsContinuous
        (topologyOfCoverings (C.coverage (Opposite.op n)))
        (SimplicialCoverings.totalTopology C.underlying C.coverage)
      let F := Grothendieck.ι C.underlying (Opposite.op n)
      let J := coverageFromIsSite (C.coverage (Opposite.op n)) (C.isSite (Opposite.op n))
      let K := coverageFromIsSite (SimplicialCoverings.total C.underlying C.coverage)
        (SimplicialCoverings.total_isSite C.underlying C.coverage C.isSite C.isCocontinuous
          C.hasCoverPullbacks)
      have hJ : J.toGrothendieck = topologyOfCoverings (C.coverage (Opposite.op n)) := by
        rw [← Coverage.toGrothendieck_toPrecoverage J]; rfl
      have hK : K.toGrothendieck =
          SimplicialCoverings.totalTopology C.underlying C.coverage := by
        rw [← Coverage.toGrothendieck_toPrecoverage K]; rfl
      rw [← hJ, ← hK]
      have hcompat : CompatiblePreserving K.toGrothendieck F := by
        constructor
        intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ heq
        have hmapId : (C.underlying.map (𝟙 (Opposite.op n))).toFunctor =
            𝟭 (C.underlying.obj (Opposite.op n)) :=
          congrArg Cat.Hom.toFunctor (C.underlying.map_id (Opposite.op n))
        obtain ⟨α₁, u₁⟩ := f₁
        obtain ⟨α₂, u₂⟩ := f₂
        change X.base ⟶ Opposite.op n at α₁ α₂
        change (C.underlying.map α₁).toFunctor.obj X.fiber ⟶ Y₁ at u₁
        change (C.underlying.map α₂).toFunctor.obj X.fiber ⟶ Y₂ at u₂
        have hb : α₁ ≫ 𝟙 (Opposite.op n) = α₂ ≫ 𝟙 (Opposite.op n) :=
          congrArg (fun q : X ⟶ F.obj Z => q.base) heq
        obtain rfl : α₁ = α₂ := by simpa using hb
        have hE : (C.underlying.map (α₁ ≫ 𝟙 (Opposite.op n))).toFunctor.obj X.fiber =
            (C.underlying.map (𝟙 (Opposite.op n))).toFunctor.obj
              ((C.underlying.map α₁).toFunctor.obj X.fiber) := by simp
        have hF₁ : (C.underlying.map (𝟙 (Opposite.op n))).toFunctor.obj Y₁ = Y₁ := by simp
        have hF₂ : (C.underlying.map (𝟙 (Opposite.op n))).toFunctor.obj Y₂ = Y₂ := by simp
        have h : eqToHom hE ≫ (C.underlying.map (𝟙 (Opposite.op n))).toFunctor.map u₁ ≫
              eqToHom hF₁ ≫ g₁ =
            eqToHom (rfl :
                (C.underlying.map (α₁ ≫ 𝟙 (Opposite.op n))).toFunctor.obj X.fiber =
                  (C.underlying.map (α₁ ≫ 𝟙 (Opposite.op n))).toFunctor.obj X.fiber) ≫
              eqToHom hE ≫ (C.underlying.map (𝟙 (Opposite.op n))).toFunctor.map u₂ ≫
                eqToHom hF₂ ≫ g₂ :=
          Grothendieck.congr heq
        have hfiber : u₁ ≫ g₁ = u₂ ≫ g₂ := by
          simp only [eqToHom_refl, Category.id_comp] at h
          have h' := (cancel_epi (eqToHom hE)).mp h
          simp only [Functor.congr_hom hmapId u₁, Functor.congr_hom hmapId u₂, Category.assoc,
            Functor.id_map, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at h'
          exact (cancel_epi (eqToHom (Functor.congr_obj hmapId
            ((C.underlying.map α₁).toFunctor.obj X.fiber)))).mp h'
        let v : X ⟶ (⟨Opposite.op n,
            (C.underlying.map α₁).toFunctor.obj X.fiber⟩ : Grothendieck C.underlying) :=
          ⟨α₁, 𝟙 _⟩
        have hA : (C.underlying.map (𝟙 (Opposite.op n))).toFunctor.obj
            ((C.underlying.map α₁).toFunctor.obj X.fiber) =
              (C.underlying.map α₁).toFunctor.obj X.fiber := by simp
        have hfac : ∀ {Y} (u : (C.underlying.map α₁).toFunctor.obj X.fiber ⟶ Y),
            (⟨α₁, u⟩ : X ⟶ F.obj Y) = v ≫ F.map u := by
          intro Y u
          refine Grothendieck.ext _ _ (Category.comp_id α₁).symm ?_
          have hR : (F.map u).fiber = eqToHom hA ≫ u := rfl
          simp only [v, Grothendieck.comp_fiber, Functor.map_id, Category.id_comp, hR,
            eqToHom_trans_assoc]
        change ℱ.obj.map (Quiver.Hom.op (⟨α₁, u₁⟩ : X ⟶ F.obj Y₁)) (x g₁ hg₁) =
          ℱ.obj.map (Quiver.Hom.op (⟨α₁, u₂⟩ : X ⟶ F.obj Y₂)) (x g₂ hg₂)
        rw [hfac u₁, hfac u₂]
        calc
          _ = ℱ.obj.map v.op ((F.op ⋙ ℱ.obj).map u₁.op (x g₁ hg₁)) := by
            simp only [op_comp, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
              Functor.map_comp_apply]
          _ = ℱ.obj.map v.op ((F.op ⋙ ℱ.obj).map u₂.op (x g₂ hg₂)) :=
            congrArg (fun s => ℱ.obj.map v.op s) (hx u₁ u₂ hg₁ hg₂ hfiber)
          _ = _ := by
            simp only [op_comp, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
              Functor.map_comp_apply]
      have hcover : ∀ X (R : Presieve X), R ∈ J X →
          Sieve.generate (R.map F) ∈ K.toGrothendieck (F.obj X) := by
        rintro X _ ⟨E, hE, rfl⟩
        have hKcov : E.presieve₀.map F ∈ K (F.obj X) := by
          change ∃ E' : PreZeroHypercover (F.obj X),
            SimplicialCoverings.total C.underlying C.coverage ⟨F.obj X, E'⟩ ∧
              E'.presieve₀ = E.presieve₀.map F
          refine ⟨E.map F, ?_, ?_⟩
          · change ∃ E₀ : PreZeroHypercover X,
              C.coverage (Opposite.op n) ⟨X, E₀⟩ ∧
                E.map F = E₀.map (Grothendieck.ι C.underlying (Opposite.op n))
            exact ⟨E, hE, rfl⟩
          · rw [← PreZeroHypercover.presieve₀_map]
        exact (Coverage.mem_toGrothendieck (K := K)).mpr
          (Coverage.Saturate.of (F.obj X) _ hKcov)
      exact Functor.isContinuous_of_coverPreserving hcompat
        (coverageFunctor_isCoverPreserving F J K hcover)

/-- Restriction of an abelian sheaf on the total site to the component in simplicial degree `n`,
i.e. the inverse image `g_n^{-1}` of Stacks 09WG on abelian sheaves. -/
abbrev restrictAb (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    Sheaf S.totalTopology Ab.{u} ⥤ Sheaf (S.componentTopology n) Ab.{u} :=
  (componentFunctor S n).sheafPushforwardContinuous Ab.{u}
    (S.componentTopology n) S.totalTopology

/-- **Stacks 09WG.** The morphism `g_n : Sh(C_n) ⟶ Sh(C_total)` induced by the cocontinuous
component inclusion. -/
@[stacks 09WG "component_inclusion"]
noncomputable def componentMorphism (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)
    [(componentFunctor S n).IsCocontinuous (S.componentTopology n) S.totalTopology] :
    MorphismOfTopoi
      (Sheaf (S.componentTopology n) (Type u))
      (Sheaf S.totalTopology (Type u)) :=
  { pushforward := gStar _ _ (S.componentTopology n) S.totalTopology
      (componentFunctor S n)
    inverseImage := gInv _ _ (S.componentTopology n) S.totalTopology
      (componentFunctor S n)
    adj := gAdjunction _ _ (S.componentTopology n) S.totalTopology
      (componentFunctor S n)
    preservesFiniteLimits := main_left_exact _ _ (S.componentTopology n) S.totalTopology
      (componentFunctor S n) }

/-- The lower-shriek functor from sheaves on a simplicial component to sheaves on the total
site. -/
@[stacks 09WG "sheaf_left_adjoint"]
noncomputable def componentLowerShriek (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)
    [HasWeakSheafify S.totalTopology (Type w)]
    [∀ G : (S.component n)ᵒᵖ ⥤ Type w, (componentFunctor S n).op.HasLeftKanExtension G] :
    Sheaf (S.componentTopology n) (Type w) ⥤ Sheaf S.totalTopology (Type w) :=
  Functor.sheafPullbackConstruction.sheafPullback (componentFunctor S n) (Type w)
    (S.componentTopology n) S.totalTopology

/-- Lower shriek is left adjoint to restriction, with an independent value universe. -/
noncomputable def componentLowerShriek_adjunction_restriction
    (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)
    [HasWeakSheafify S.totalTopology (Type w)]
    [∀ G : (S.component n)ᵒᵖ ⥤ Type w, (componentFunctor S n).op.HasLeftKanExtension G] :
    componentLowerShriek.{u, w} S n ⊣
      (componentFunctor S n).sheafPushforwardContinuous (Type w)
        (S.componentTopology n) S.totalTopology :=
  (componentFunctor S n).sheafAdjunctionLowerShriek _ _ _

/-- The lower-shriek functor is left adjoint to inverse image along the morphism of topoi
associated to a simplicial component. -/
@[stacks 09WG "sheaf_left_adjoint"]
noncomputable def componentLowerShriek_adjunction (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) :
    componentLowerShriek.{u, u} S n ⊣ (componentMorphism S n).inverseImage := by
  simpa [componentMorphism, gInv_eq_sheafPullbackCocontinuous] using
    (componentLowerShriek_adjunction_restriction.{u, u} S n).ofNatIsoRight
      ((componentFunctor S n).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
        _ _ _).symm

end SimplicialSiteSituation

end CategoryTheory

/-! ## The two assertions realized by existing declarations

Inverse image along the component inclusion is restriction, which for a continuous and
cocontinuous functor is the general natural isomorphism
`CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous`; and on abelian
sheaves the left adjoint of restriction and its adjunction are the general construction
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback` and
`CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`, instantiated at
the component inclusion. The tag is recorded against those declarations rather than restating
specializations of them. -/

add_to_stacks 09WG "restriction"
  CategoryTheory.Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous

add_to_stacks 09WG "abelian_left_adjoint"
  CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback

add_to_stacks 09WG "abelian_left_adjoint"
  CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous

end
