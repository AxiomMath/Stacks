module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.SourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmoothCoverings

/-!
# Transferring source locality of a property of scheme morphisms to algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, let `P` be a property of morphisms of
schemes which is étale local on the source and target (**Stacks 04QZ**), and let `τ` be one of
the five topologies of **Stacks 03YH**. **Stacks 03MJ** turns `P` into the property
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart B S hS P` of morphisms of algebraic spaces
over `S`, and **Stacks 06ER** says that if `P` is local on the source for the counterpart of
`τ` on schemes, then the associated property of morphisms of algebraic spaces is local on the
source for `τ`.

The argument is the source's. Given `f : X ⟶ Y` and a `τ`-covering `{Zᵢ ⟶ X}`, choose a
surjective étale scheme atlas `V ⟶ Y`, lift it to a surjective étale chart `T₀ ⟶ X` over a
morphism `α : T₀ ⟶ V` of the site (**Stacks 02X1**), base-change the covering along `T₀ ⟶ X`,
choose a surjective étale scheme atlas `Wᵢ ⟶ Zᵢ ×_X T₀` of each member, and compose. The
resulting family `{Wᵢ ⟶ T₀}` is a family of morphisms of the *site*, and a `τ`-covering family
of algebraic spaces whose members and target are all representable is a covering family of the
representing schemes for the counterpart of `τ`
(`AlgebraicGeometry.Space.Topology.isCovering_yoneda`). With both sides of the equivalence now
expressed on schemes, source locality of `P` gives the two implications, and Stacks 03MJ
carries them back.

The two steps which depend on `τ` are the base change and the composition of covering
families; they are the hypothesis `AlgebraicGeometry.Space.Topology.HasCoveringStability`
below, whose two clauses are Stacks 03MR for the fpqc topology, Stacks 03Y9 for the fppf
topology, Stacks 041D for the smooth topology and Stacks 041F for the étale topology.

## Main definitions

* `AlgebraicGeometry.Space.Topology.HasCoveringStability`: the `τ`-covering families compose
  and are stable under base change.

## Main results

* `AlgebraicGeometry.Space.Topology.isCovering_of_isEtaleCovering`: an étale covering family
  is a `τ`-covering family, for every one of the five topologies.
* `AlgebraicGeometry.Space.Topology.hasCoveringStability_fppf`,
  `AlgebraicGeometry.Space.Topology.hasCoveringStability_smooth` and
  `AlgebraicGeometry.Space.Topology.hasCoveringStability_etale`: the hypothesis holds for the
  fppf, the smooth and the étale topology.
* `AlgebraicGeometry.Space.Topology.isLocalAtSource_of_schemes`: the transfer.

## Implementation notes

`isLocalAtSource_of_schemes` is **deliberately not tagged** `@[stacks 06ER]`. Stacks 06ER
asserts the transfer for all five topologies of Stacks 03YH at once, and the hypothesis
`Topology.HasCoveringStability` is recorded here for three of them. The fpqc case of the
transfer is available separately, in a self-contained form, as
`AlgebraicGeometry.Space.isLocalAtSource_fpqc_of_schemes`; its base-change clause is
`AlgebraicGeometry.Space.isFpqcCovering_pullback_fst`, which is stated downstream of this
module, so the fpqc instance of the hypothesis is not recorded here either. The syntomic case
is missing because syntomicity of a morphism of algebraic spaces is not yet known to be stable
under composition and base change; that rests on
`AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget @Syntomic` (**Stacks 04R3**, syntomic case),
whose only missing input is
`CategoryTheory.MorphismProperty.IsLocalAtSource @Syntomic Scheme.etalePrecoverage` — the
syntomic case of **Stacks 02KM**. The tag belongs on whatever proves all five.

Both clauses of `Topology.HasCoveringStability` are stated at the fibre product of presheaves,
which is the underlying presheaf of the fibre product of algebraic spaces of Stacks 02X2, so
that no choice of pullback object is involved; the square a consumer needs is then
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct`. The composition clause composes a
covering family with a *one-member* covering family of each of its members, which is all the
transfer uses — those members are étale atlases — and is what makes the composed family
indexed by `Σ _ : I, PUnit`.

The index type `I` of a covering family lives in its own universe `v`, independent of the
universe `u` of the schemes, as in `AlgebraicGeometry.Space.Topology.precoverage`.

## References

* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 06ER](https://stacks.math.columbia.edu/tag/06ER)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

/-! ### Étale covering families are covering families for every topology -/

section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An étale covering family of algebraic spaces over `S` is a covering family for every one of
the five topologies of Stacks 03YH: this is the chain of implications of Tags 0DFA, 0DFB, 0DFC
and 0DFQ. -/
theorem Topology.isCovering_of_isEtaleCovering (τ : Topology) {I : Type v}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (f : ∀ i, X i ⟶ F) (hf : IsEtaleCovering B S hS X f) :
    τ.IsCovering B S hS X f := by
  refine ⟨hf.target_isAlgebraicSpace, hf.source_isAlgebraicSpace, ?_⟩
  cases τ with
  | fpqc => exact isFpqcCovering_of_isEtaleCovering B S hS X f hf
  | fppf => exact isFppfCovering_of_isEtaleCovering B S hS hf
  | syntomic => exact isSyntomicCovering_of_isEtaleCovering B S hS hf
  | smooth => exact isSmoothCovering_of_isEtaleCovering B S hS hf
  | etale => exact hf

end

/-! ### Composition and base change of covering families -/

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search for these pullbacks times out at the default budget since Lean v4.35.0.
/-- The two stability properties of the `τ`-covering families of algebraic spaces over `S`
which the transfer of source locality from schemes uses: a covering family composed with a
one-member covering family of each of its members is a covering family, and the first
projections of the fibre products of a covering family with a morphism into its target form a
covering family of the source of that morphism.

For the fpqc topology these two clauses are Stacks 03MR, for the fppf topology Stacks 03Y9,
for the smooth topology Stacks 041D and for the étale topology Stacks 041F. -/
structure Topology.HasCoveringStability (τ : Topology)
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop where
  /-- A `τ`-covering family composed with a one-member `τ`-covering family of each of its
  members is a `τ`-covering family. -/
  comp {I : Type v} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Xi Xij : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : ∀ i, Xi i ⟶ X) (g : ∀ i, Xij i ⟶ Xi i) (hf : τ.IsCovering B S hS Xi f)
    (hg : ∀ i, τ.IsCovering B S hS (fun _ : PUnit.{v + 1} => Xij i) (fun _ => g i)) :
    τ.IsCovering B S hS (fun p : Σ _ : I, PUnit.{v + 1} => Xij p.1)
      (fun p => g p.1 ≫ f p.1)
  /-- The first projections of the fibre products of a `τ`-covering family with a morphism `g`
  into its target form a `τ`-covering family of the source of `g`. -/
  pullback {I : Type v} {X X' : AlgebraicSpaces B S hS} (Xi : I → AlgebraicSpaces B S hS)
    (f : ∀ i, Xi i ⟶ X) (g : X' ⟶ X)
    (hf : τ.IsCovering B S hS (fun i => (Xi i).obj) (fun i => (f i).hom)) :
    τ.IsCovering B S hS (fun i => Limits.pullback g.hom (f i).hom)
      (fun i => Limits.pullback.fst g.hom (f i).hom)

section

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03Y9.** The fppf covering families of algebraic spaces over `S` compose and are
stable under base change. -/
theorem Topology.hasCoveringStability_fppf :
    Topology.HasCoveringStability.{u, v} .fppf B S hS := by
  constructor
  · intro I X Xi Xij f g hf hg
    exact ⟨hf.1, fun p => (hg p.1).2.1 PUnit.unit,
      isFppfCovering_comp B S hS I (fun _ => PUnit.{v + 1}) Xi (fun i _ => Xij i) f
        (fun i _ => g i) hf.2.2 fun i => (hg i).2.2⟩
  · intro I X X' Xi f g hf
    exact ⟨X'.property, fun i => isAlgebraicSpace_pullback B S hS g.hom (f i).hom
      X'.property (Xi i).property hf.1,
      isFppfCovering_fibreProduct B S hS Xi f g hf.2.2⟩

/-- **Stacks 041D.** The smooth covering families of algebraic spaces over `S` compose and are
stable under base change. -/
theorem Topology.hasCoveringStability_smooth :
    Topology.HasCoveringStability.{u, v} .smooth B S hS := by
  constructor
  · intro I X Xi Xij f g hf hg
    exact ⟨hf.1, fun p => (hg p.1).2.1 PUnit.unit,
      isSmoothCovering_comp B S hS (J := fun _ => PUnit.{v + 1}) Xi f
        (fun i _ => Xij i) (fun i _ => g i) hf.2.2 fun i => (hg i).2.2⟩
  · intro I X X' Xi f g hf
    exact ⟨X'.property, fun i => isAlgebraicSpace_pullback B S hS g.hom (f i).hom
      X'.property (Xi i).property hf.1,
      isSmoothCovering_fiberProduct B S hS Xi f g hf.2.2⟩

/-- **Stacks 041F.** The étale covering families of algebraic spaces over `S` compose and are
stable under base change. -/
theorem Topology.hasCoveringStability_etale :
    Topology.HasCoveringStability.{u, v} .etale B S hS := by
  constructor
  · intro I X Xi Xij f g hf hg
    exact ⟨hf.1, fun p => (hg p.1).2.1 PUnit.unit,
      isEtaleCovering_comp B S hS (fun _ => PUnit.{v + 1}) Xi f (fun i _ => Xij i)
        (fun i _ => g i) hf.2.2 fun i => (hg i).2.2⟩
  · intro I X X' Xi f g hf
    exact ⟨X'.property, fun i => isAlgebraicSpace_pullback B S hS g.hom (f i).hom
      X'.property (Xi i).property hf.1,
      isEtaleCovering_pullback B S hS g.hom X'.property (fun i => (Xi i).obj)
        (fun i => (f i).hom) hf.2.2⟩

/-! ### Two constructions of covering families used by the transfer -/

/-- Composing a `τ`-covering family of algebraic spaces over `S` with a surjective étale scheme
atlas of each of its members gives a `τ`-covering family, indexed by the members paired with a
one-element type. -/
theorem Topology.isCovering_etaleAtlases_comp (τ : Topology)
    (hτ : Topology.HasCoveringStability.{u, v} τ B S hS) {I : Type v}
    (Z : I → AlgebraicSpaces B S hS) (V : AlgebraicSpaces B S hS) (g : ∀ i, Z i ⟶ V)
    (hbase : τ.IsCovering B S hS (fun i => (Z i).obj) (fun i => (g i).hom))
    (U : I → BigFppfOver B S hS) (a : ∀ i, yoneda.obj (U i) ⟶ (Z i).obj)
    (hsurj : ∀ i, (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a i))
    (hetale : ∀ i, (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a i)) :
    τ.IsCovering B S hS (fun p : Σ _ : I, PUnit.{v + 1} => yoneda.obj (U p.1))
      (fun p => a p.1 ≫ (g p.1).hom) :=
  hτ.comp (fun i => (g i).hom) a hbase fun i =>
    Topology.isCovering_of_isEtaleCovering B S hS τ _ _
      (isEtaleCovering_atlas B S hS (hbase.2.1 i) (hsurj i) (hetale i))

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the fibre products of algebraic spaces in the statement is heavy
/-- Base change of a `τ`-covering family of algebraic spaces over `S` along a chart of its
target: the fibre products form a `τ`-covering family of the chart, and each of them sits in a
pullback square over the chart and the corresponding member of the original family. -/
theorem Topology.isCovering_baseChange_of_chart (τ : Topology)
    (hτ : Topology.HasCoveringStability.{u, v} τ B S hS) {I : Type v}
    {X : AlgebraicSpaces B S hS} (Zi : I → AlgebraicSpaces B S hS) (gi : ∀ i, Zi i ⟶ X)
    (hcover : τ.IsCovering B S hS (fun i => (Zi i).obj) (fun i => (gi i).hom))
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.obj) :
    ∃ (Ai : I → AlgebraicSpaces B S hS)
      (qi : ∀ i, Ai i ⟶ representedAlgebraicSpace B S hS U) (projZ : ∀ i, Ai i ⟶ Zi i),
        τ.IsCovering B S hS (fun i => (Ai i).obj) (fun i => (qi i).hom) ∧
        ∀ i, IsPullback (qi i) (projZ i)
          (ObjectProperty.homMk a : representedAlgebraicSpace B S hS U ⟶ X) (gi i) := by
  let au : representedAlgebraicSpace B S hS U ⟶ X := ObjectProperty.homMk a
  exact ⟨fun i => AlgebraicSpaces.fiberProduct B S hS au (gi i),
    fun i => ObjectProperty.homMk (Limits.pullback.fst au.hom (gi i).hom),
    fun i => ObjectProperty.homMk (Limits.pullback.snd au.hom (gi i).hom),
    hτ.pullback Zi gi au hcover,
    fun i => AlgebraicSpaces.isPullback_fiberProduct B S hS au (gi i)⟩

/-- Refining a `τ`-covering family `{Zᵢ ⟶ X}` of algebraic spaces over `S` along an étale chart
`a : U ⟶ X` by surjective étale atlases of the fibre products gives morphisms `Wᵢ ⟶ U` of the
site forming a covering family of schemes for the counterpart of `τ`, together with étale charts
`Wᵢ ⟶ Zᵢ` compatible with `a`, which are surjective when `a` is. -/
theorem Topology.exists_isCovering_yoneda_of_chart (τ : Topology)
    (hτ : Topology.HasCoveringStability.{u, v} τ B S hS) {I : Type v}
    {X : AlgebraicSpaces B S hS} (Zi : I → AlgebraicSpaces B S hS) (gi : ∀ i, Zi i ⟶ X)
    (hcover : τ.IsCovering B S hS (fun i => (Zi i).obj) (fun i => (gi i).hom))
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.obj)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    ∃ (W : I → BigFppfOver B S hS) (d : ∀ p : Σ _ : I, PUnit.{v + 1}, W p.1 ⟶ U)
      (c : ∀ i, yoneda.obj (W i) ⟶ (Zi i).obj),
      Presieve.ofArrows (fun p => (BigFppfOver.toScheme B S hS).obj (W p.1))
        (fun p => (BigFppfOver.toScheme B S hS).map (d p)) ∈
        τ.schemePrecoverage ((BigFppfOver.toScheme B S hS).obj U) ∧
      (∀ i, yoneda.map (d ⟨i, PUnit.unit⟩) ≫ a = c i ≫ (gi i).hom) ∧
      (∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (c i)) ∧
      ((MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a →
        ∀ i, (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (c i)) := by
  obtain ⟨Ai, qi, projZ, hAi, hpb⟩ :=
    Topology.isCovering_baseChange_of_chart B S hS τ hτ Zi gi hcover U a
  choose W w hsurjW hetaleW using fun i => (Ai i).property.exists_atlas
  let d : ∀ p : Σ _ : I, PUnit.{v + 1}, W p.1 ⟶ U :=
    fun p => yoneda.preimage (w p.1 ≫ (qi p.1).hom)
  have hd (p : Σ _ : I, PUnit.{v + 1}) : yoneda.map (d p) = w p.1 ≫ (qi p.1).hom := by
    simp [d]
  have hcov : τ.IsCovering B S hS (fun p : Σ _ : I, PUnit.{v + 1} => yoneda.obj (W p.1))
      (fun p => yoneda.map (d p)) := by
    simpa only [hd] using
      Topology.isCovering_etaleAtlases_comp B S hS τ hτ Ai _ qi hAi W w hsurjW hetaleW
  have hproj (i : I) : IsEtale B S hS (projZ i).hom :=
    isEtale_of_isPullback B S hS (qi i) (projZ i) _ (gi i) (hpb i)
      (chart_map_isEtale B S hS U a ha)
  refine ⟨W, d, fun i => w i ≫ (projZ i).hom,
    Topology.isCovering_yoneda B S hS τ (fun p : Σ _ : I, PUnit.{v + 1} => W p.1) U d hcov,
    fun i => ?_, fun i => (isEtale_iff_presheaf_of_yoneda B S hS _).1
      (isEtale_comp B S hS (chart_map_isEtale B S hS (W i) (w i) (hetaleW i)) (hproj i)),
    fun haSurj i => (surjective_iff_surjective_pointsMap B S hS _ (Zi i).property _ _).mpr
      (isSurjective_comp B S hS
        ((surjective_iff_surjective_pointsMap B S hS _ (Ai i).property _ _).mp (hsurjW i))
        (isSurjective_of_isPullback B S hS (hpb i)
          ((surjective_iff_surjective_pointsMap B S hS _ X.property _ _).mp haSurj)))⟩
  have hbase : (qi i).hom ≫ a = (projZ i).hom ≫ (gi i).hom :=
    congrArg (fun k => k.hom) (hpb i).w
  simp only [hd, Category.assoc, hbase]

/-- A property of morphisms respecting isomorphisms holds for every member of a family composed
with `f` as soon as it holds for every member of another family generating the same presieve. -/
private theorem comp_of_ofArrows_eq {C : Type*} [Category C] (Q : MorphismProperty C)
    [Q.RespectsIso] {X Y : C} {I J : Type*} {A : I → C} {B : J → C} (a : ∀ i, A i ⟶ X)
    (b : ∀ j, B j ⟶ X) (h : Presieve.ofArrows A a = Presieve.ofArrows B b) (f : X ⟶ Y)
    (hb : ∀ j, Q (b j ≫ f)) (i : I) : Q (a i ≫ f) := by
  obtain ⟨j, _, hij⟩ := Presieve.ofArrows_surj b (a i) (h ▸ Presieve.ofArrows.mk i)
  rw [hij, Category.assoc]
  exact MorphismProperty.RespectsIso.precomp Q _ _ (hb j)

/-! ### Stacks 06ER, for a topology whose covering families compose and base-change -/

/-- If `P` is local on the source for the counterpart of `τ` on schemes, then the property of
Stacks 03MJ associated with `P` passes from `f` to its composite with every member of a
`τ`-covering family. -/
theorem Topology.holdsOnEveryEtaleChart_comp_of_isCovering (τ : Topology)
    (hτ : Topology.HasCoveringStability.{u, v} τ B S hS) (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P) [P.IsLocalAtSource τ.schemePrecoverage]
    {I : Type v} {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (Zi : I → AlgebraicSpaces B S hS)
    (gi : ∀ i, Zi i ⟶ X)
    (hcover : τ.IsCovering B S hS (fun i => (Zi i).obj) (fun i => (gi i).hom))
    (hf : HoldsOnEveryEtaleChart B S hS P f.hom) (j : I) :
    HoldsOnEveryEtaleChart B S hS P (gi j ≫ f).hom := by
  obtain ⟨V, b, hbSurj, hbEtale⟩ := Y.property.exists_atlas
  obtain ⟨T0, t, alpha, hα, htSurj, htEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS
      X.property Y.property f.hom V b hbSurj hbEtale
  obtain ⟨W, d, c, hcov, hsq, hc, hcSurj⟩ :=
    Topology.exists_isCovering_yoneda_of_chart B S hS τ hτ Zi gi hcover T0 t htEtale
  refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP (Zi j).property
    Y.property _).2 ⟨W j, V, c j, b, d ⟨j, PUnit.unit⟩ ≫ alpha, hc j, hbEtale,
      hcSurj htSurj j, ?_, ?_⟩
  · change _ = c j ≫ (gi j).hom ≫ f.hom
    rw [Functor.map_comp, Category.assoc, ← hα, reassoc_of% hsq j]
  · rw [Functor.map_comp]
    exact (‹P.IsLocalAtSource τ.schemePrecoverage›).comp hcov
      ((BigFppfOver.toScheme B S hS).map (d ⟨j, PUnit.unit⟩))
      (.mk (⟨j, PUnit.unit⟩ : Σ _ : I, PUnit.{v + 1}))
      (hf T0 V t b alpha htEtale hbEtale hα.symm)

/-- If `P` is local on the source for the counterpart of `τ` on schemes, then the property of
Stacks 03MJ associated with `P` holds for `f` as soon as it holds for the composite of `f` with
every member of a `τ`-covering family. -/
theorem Topology.holdsOnEveryEtaleChart_of_isCovering (τ : Topology)
    (hτ : Topology.HasCoveringStability.{u, v} τ B S hS) (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource τ.schemePrecoverage] {I : Type v} {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (Zi : I → AlgebraicSpaces B S hS) (gi : ∀ i, Zi i ⟶ X)
    (hcover : τ.IsCovering B S hS (fun i => (Zi i).obj) (fun i => (gi i).hom))
    (hall : ∀ j, HoldsOnEveryEtaleChart B S hS P (gi j ≫ f).hom) :
    HoldsOnEveryEtaleChart B S hS P f.hom := by
  intro U V a b h ha hb hcomm
  obtain ⟨W, d, c, hcov, hsq, hc, -⟩ :=
    Topology.exists_isCovering_yoneda_of_chart B S hS τ hτ Zi gi hcover U a ha
  refine (‹P.IsLocalAtSource τ.schemePrecoverage›).of_forall_comp hcov fun _ k hk => ?_
  rcases hk with ⟨⟨i, ⟨⟩⟩⟩
  rw [← Functor.map_comp]
  exact hall i (W i) V (c i) b _ (hc i) hb
    (show yoneda.map (d ⟨i, PUnit.unit⟩ ≫ h) ≫ b = c i ≫ (gi i).hom ≫ f.hom by
      rw [Functor.map_comp, Category.assoc, hcomm, reassoc_of% hsq i])

/-- Let `P` be a property of morphisms of schemes which is étale local on the source and
target, and let `τ` be one of the five topologies of Stacks 03YH whose covering families
compose and are stable under base change. If `P` is local on the source for the counterpart of
`τ` on schemes, then the associated property of morphisms of algebraic spaces over `S` of
Stacks 03MJ is local on the source for `τ`.

This is **Stacks 06ER** for such a `τ`; see the implementation notes of this module for why it
is not tagged. -/
theorem Topology.isLocalAtSource_of_schemes (τ : Topology)
    (hτ : Topology.HasCoveringStability.{u, v} τ B S hS) (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P) [P.IsLocalAtSource τ.schemePrecoverage] :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        HoldsOnEveryEtaleChart B S hS P f.hom)
      (Topology.precoverage.{u, v} τ B S hS) := by
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun {F G} f => HoldsOnEveryEtaleChart B S hS P f.hom
  have : Q.RespectsIso := holdsOnEveryEtaleChart_respectsIso B S hS P
  refine MorphismProperty.IsLocalAtSource.mk_of_iff_of_zeroHypercover fun f E => ?_
  obtain ⟨I, Zi, gi, hpres, hcover⟩ := E.mem₀
  exact ⟨fun hf => comp_of_ofArrows_eq Q E.f gi hpres f
      (Topology.holdsOnEveryEtaleChart_comp_of_isCovering B S hS τ hτ P hP f Zi gi hcover hf),
    fun hall => Topology.holdsOnEveryEtaleChart_of_isCovering B S hS τ hτ P f Zi gi hcover
      (comp_of_ofArrows_eq Q gi E.f hpres.symm f hall)⟩

end

end AlgebraicGeometry.Space

end
