module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.MorphismFiniteness

/-!
# Descent of flatness and local finite presentation along a jointly surjective family

Let `f j : X j ⟶ Y`, `j ∈ J`, be morphisms of algebraic spaces over `S` and let `g : Y ⟶ Z` be a
morphism of presheaves. Suppose the family is *jointly* surjective as a family of morphisms of
fppf sheaves: every section of `Y` over an object `U` of the site lifts, over the members of a
covering sieve of `U`, to a section of some `X j`, that is, the supremum of the image sieves
`CategoryTheory.Presheaf.imageSieve` of the members covers `U`. If every composite `f j ≫ g` is
flat (resp. locally of finite presentation), then so is `g`. This is Stacks 06NR with the single
surjection of sheaves `X ⟶ Y` replaced by a jointly surjective family.

## Main results

* `AlgebraicGeometry.prop_of_comp_of_fppf_refinement_family`: a property of morphisms of schemes
  which is Zariski local at the source and descends along one fppf refinement descends from the
  composites `f i ≫ g` to `g` when the `f i` are refined by an fppf covering.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_comp_of_jointlyLocallySurjective`: such a
  property descends, in the chart sense, along a jointly surjective family of morphisms of
  algebraic spaces.
* `AlgebraicGeometry.Space.isFlat_of_comp_of_jointlyLocallySurjective` and
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_comp_of_jointlyLocallySurjective`:
  the cases of flatness and of local finite presentation.

## References

* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- Let `P` be a property of morphisms of schemes which is Zariski local at the source and
which descends from a composite `f ≫ g` to `g` whenever the singleton `{f}` is refined by an fppf
covering. Let `g : Y ⟶ Z`, let `𝒰` be an fppf covering of `Y`, and suppose every member `𝒰.f i`
factors as `k i ≫ f i` with `f i ≫ g` having `P`. Then `g` has `P`. -/
theorem prop_of_comp_of_fppf_refinement_family (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtSource P]
    (hdesc : ∀ {A B' C : Scheme.{u}} (f : A ⟶ B') (g : B' ⟶ C),
      P (f ≫ g) →
      (∃ 𝒰 : Scheme.Cover.{u + 1, u} Scheme.fppfPrecoverage B',
        Nonempty (𝒰.toPreZeroHypercover.Hom
          (PreZeroHypercover.singleton.{u + 1, u, u + 1} f))) → P g)
    {Y Z : Scheme.{u}} (g : Y ⟶ Z) (𝒰 : Scheme.Cover.{v, u} Scheme.fppfPrecoverage Y)
    {X : 𝒰.I₀ → Scheme.{u}} (f : ∀ i, X i ⟶ Y) (k : ∀ i, 𝒰.X i ⟶ X i)
    (hk : ∀ i, k i ≫ f i = 𝒰.f i) (hfg : ∀ i, P (f i ≫ g)) : P g := by
  classical
  have hmem := (Scheme.presieve₀_mem_precoverage_iff 𝒰.toPreZeroHypercover).1 𝒰.mem₀
  choose a ha using hmem.1
  let F : (∐ fun y : Y => X (a y)) ⟶ Y := Sigma.desc fun y => f (a y)
  have hF : P (F ≫ g) := by
    have hFg : F ≫ g = Sigma.desc fun y => f (a y) ≫ g := by
      ext y
      simp [F]
    rw [hFg]
    exact IsZariskiLocalAtSource.sigmaDesc fun y => hfg (a y)
  let 𝒱 : Scheme.Cover.{u + 1, u} Scheme.fppfPrecoverage Y :=
    Scheme.Cover.mkOfCovers (ULift.{u + 1} Y) (fun y => 𝒰.X (a y.down))
      (fun y => 𝒰.f (a y.down))
      (fun x => by
        obtain ⟨z, hz⟩ := ha x
        exact ⟨⟨x⟩, z, hz⟩)
      (fun y => hmem.2 (a y.down))
  refine hdesc F g hF ⟨𝒱, ⟨{
    s₀ := fun _ => PUnit.unit
    h₀ := fun y => k (a y.down) ≫ Sigma.ι (fun y : Y => X (a y)) y.down
    w₀ := fun y => ?_ }⟩⟩
  change (k (a y.down) ≫ Sigma.ι (fun y : Y => X (a y)) y.down) ≫ F = 𝒰.f (a y.down)
  simp [F, hk]

namespace Space

/-- A property of morphisms of schemes which is Zariski local at the source and descends from a
composite to its second factor whenever the first factor is refined by an fppf covering
descends, in the chart sense of Stacks 03MJ, from the composites `f j ≫ g` to `g` whenever the
family of morphisms of algebraic spaces `f j : X j ⟶ Y` is jointly surjective as a family of
morphisms of fppf sheaves. -/
theorem holdsOnEveryEtaleChart_of_comp_of_jointlyLocallySurjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    (hdesc : ∀ {A B' C : Scheme.{u}} (f : A ⟶ B') (g : B' ⟶ C),
      P (f ≫ g) →
      (∃ 𝒰 : Scheme.Cover.{u + 1, u} Scheme.fppfPrecoverage B',
        Nonempty (𝒰.toPreZeroHypercover.Hom
          (PreZeroHypercover.singleton.{u + 1, u, u + 1} f))) → P g)
    {J : Type v} {X : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : ∀ j, IsAlgebraicSpace B S hS (X j))
    (hY : IsAlgebraicSpace B S hS Y)
    (f : ∀ j, X j ⟶ Y) (g : Y ⟶ Z)
    (hfg : ∀ j, HoldsOnEveryEtaleChart B S hS P (f j ≫ g))
    (hf : ∀ (U : BigFppfOver B S hS) (s : Y.obj (Opposite.op U)),
      (⨆ j, Presheaf.imageSieve (f j) s) ∈ BigFppfOver.topology B S hS U) :
    HoldsOnEveryEtaleChart B S hS P g := by
  classical
  let Tsch : BigFppfOver B S hS ⥤ Scheme.{u} := BigFppfOver.toScheme B S hS
  let Et : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) Tsch
  have : Et.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
  have : Et.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS Etale.etale_isStableUnderBaseChange
  have : Et.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition Et
  have : Et.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange Et
  intro U V a b h hUa hVb hab
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  let aElem : Y.obj (Opposite.op U) := yonedaEquiv a
  obtain ⟨E, hE, hEimage⟩ :=
    BigFppfOver.exists_isCovering_of_mem_topology B S hS (hf U aElem)
  let coverU : Scheme.Cover.{u + 1, u} Scheme.fppfPrecoverage (Tsch.obj U) := by
    have hFppf : AlgebraicGeometry.IsFppfCovering
        ⟨(BigFppfOver.forget B S hS).obj U, E.map (BigFppfOver.forget B S hS)⟩ :=
      B.isFppfCovering_of_isCovering hE
    rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff] at hFppf
    refine ⟨E.map Tsch, ?_⟩
    simpa [Tsch, PreZeroHypercover.map, PreZeroHypercover.presieve₀] using hFppf
  have hEimage' : ∀ i, ∃ (j : J) (x : (X j).obj (Opposite.op (E.X i))),
      (f j).app _ x = Y.map (E.f i).op aElem := by
    intro i
    obtain ⟨_, ⟨j, rfl⟩, x, hx⟩ := (Sieve.sSup_apply (Ss := Set.range
      (fun j => Presheaf.imageSieve (f j) aElem)) (E.f i)).1 (hEimage i)
    exact ⟨j, x, hx⟩
  choose jj xiElem hxi using hEimage'
  have hT : ∀ i, IsAlgebraicSpace B S hS (pullback a (f (jj i))) := fun i =>
    isAlgebraicSpace_pullback B S hS a (f (jj i)) hU (hX (jj i)) hY
  choose Q atlasT hatlasTSurj hatlasTEtale using fun i => (hT i).exists_atlas
  let qUsite : (i : E.I₀) → Q i ⟶ U := fun i => yoneda.preimage (atlasT i ≫ pullback.fst _ _)
  have hqX : ∀ i, Et.presheaf (atlasT i) := hatlasTEtale
  have hQtoX : ∀ i, Et.presheaf (atlasT i ≫ pullback.snd a (f (jj i))) := fun i =>
    MorphismProperty.comp_mem Et.presheaf (atlasT i) (pullback.snd a (f (jj i))) (hqX i)
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback a (f (jj i))) hUa)
  let xi : (i : E.I₀) → yoneda.obj (E.X i) ⟶ X (jj i) :=
    fun i => (yonedaEquiv (X := E.X i) (F := X (jj i))).symm (xiElem i)
  have htri (i : E.I₀) : yoneda.map (E.f i) ≫ a = xi i ≫ f (jj i) := by
    apply (yonedaEquiv (X := E.X i) (F := Y)).injective
    rw [← yonedaEquiv_naturality a (E.f i), yonedaEquiv_comp]
    simpa [aElem, xi] using (hxi i).symm
  let mi : (i : E.I₀) → yoneda.obj (E.X i) ⟶ pullback a (f (jj i)) :=
    fun i => pullback.lift (yoneda.map (E.f i)) (xi i) (htri i)
  let li : (i : E.I₀) → yoneda.obj ((hqX i).rep.pullback (mi i)) ⟶ yoneda.obj (Q i) :=
    fun i => (hqX i).rep.fst (mi i)
  let ri : (i : E.I₀) → (hqX i).rep.pullback (mi i) ⟶ E.X i :=
    fun i => (hqX i).rep.snd (mi i)
  have hAtlasPB (i : E.I₀) :
      IsPullback (li i) (yoneda.map (ri i)) (atlasT i) (mi i) := by
    simpa [li, ri] using (hqX i).rep.isPullback (mi i)
  have hriEtale (i : E.I₀) : Etale (Tsch.map (ri i)) :=
    (hqX i).property (mi i) (li i) (ri i) (hAtlasPB i)
  have hriSurj (i : E.I₀) : Surjective (Tsch.map (ri i)) :=
    (hatlasTSurj i).property (mi i) (li i) (ri i) (hAtlasPB i)
  let localCover (i : E.I₀) :
      Scheme.Cover.{u + 1, u} Scheme.fppfPrecoverage (Tsch.obj (E.X i)) := by
    let : Etale (Tsch.map (ri i)) := hriEtale i
    let : Surjective (Tsch.map (ri i)) := hriSurj i
    refine ⟨PreZeroHypercover.singleton (Tsch.map (ri i)), ?_⟩
    simpa only [PreZeroHypercover.presieve₀_singleton] using
      Scheme.Hom.singleton_mem_fppfPrecoverage (Tsch.map (ri i))
  let refinedCover : Scheme.Cover.{u + 1, u} Scheme.fppfPrecoverage (Tsch.obj U) :=
    coverU.bind localCover
  have hfactor' (i : E.I₀) : yoneda.preimage (li i) ≫ qUsite i = ri i ≫ E.f i :=
    yoneda.map_injective (by
      have hpb := congrArg (fun k => k ≫ pullback.fst a (f (jj i))) (hAtlasPB i).w
      dsimp only [mi] at hpb
      simp only [Category.assoc, pullback.lift_fst] at hpb
      simpa [qUsite, Category.assoc] using hpb)
  have hchart (i : E.I₀) :
      yoneda.map (qUsite i ≫ h) ≫ b = (atlasT i ≫ pullback.snd a (f (jj i))) ≫ f (jj i) ≫ g := by
    simp only [Functor.map_comp, Category.assoc, hab,
      show yoneda.map (qUsite i) = atlasT i ≫ pullback.fst a (f (jj i)) from by simp [qUsite]]
    change (atlasT i ≫ pullback.fst a (f (jj i))) ≫ a ≫ g =
      (atlasT i ≫ pullback.snd a (f (jj i))) ≫ f (jj i) ≫ g
    simp only [Category.assoc, pullback.condition_assoc]
  exact prop_of_comp_of_fppf_refinement_family P hdesc (Tsch.map h) refinedCover
    (X := fun ij => Tsch.obj (Q ij.1)) (fun ij => Tsch.map (qUsite ij.1))
    (fun ij => Tsch.map (yoneda.preimage (li ij.1)))
    (fun ij => by
      change Tsch.map (yoneda.preimage (li ij.1)) ≫ Tsch.map (qUsite ij.1) =
        Tsch.map (ri ij.1) ≫ Tsch.map (E.f ij.1)
      simpa only [Functor.map_comp] using congrArg Tsch.map (hfactor' ij.1))
    (fun ij => by
      simpa only [Functor.map_comp] using
        hfg (jj ij.1) (Q ij.1) V (atlasT ij.1 ≫ pullback.snd a (f (jj ij.1))) b
          (qUsite ij.1 ≫ h) (hQtoX ij.1) hVb (hchart ij.1))

/-- Let `f j : X j ⟶ Y` be morphisms of algebraic spaces over `S` which are jointly surjective
as a family of morphisms of fppf sheaves, and let `g : Y ⟶ Z`. If every composite `f j ≫ g` is
flat, then `g` is flat. -/
theorem isFlat_of_comp_of_jointlyLocallySurjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {J : Type v} {X : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : ∀ j, IsAlgebraicSpace B S hS (X j))
    (hY : IsAlgebraicSpace B S hS Y)
    (f : ∀ j, X j ⟶ Y) (g : Y ⟶ Z)
    (hfg : ∀ j, IsFlat B S hS (f j ≫ g))
    (hf : ∀ (U : BigFppfOver B S hS) (s : Y.obj (Opposite.op U)),
      (⨆ j, Presheaf.imageSieve (f j) s) ∈ BigFppfOver.topology B S hS U) :
    IsFlat B S hS g := by
  have : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat.{u})
  exact holdsOnEveryEtaleChart_of_comp_of_jointlyLocallySurjective B S hS
    (@Flat.{u} : MorphismProperty Scheme.{u})
    (fun f' g' _ hcover => flat_of_comp_of_fppf_refinement f' g' hcover) hX hY f g hfg hf

/-- Let `f j : X j ⟶ Y` be morphisms of algebraic spaces over `S` which are jointly surjective
as a family of morphisms of fppf sheaves, and let `g : Y ⟶ Z`. If every composite `f j ≫ g` is
locally of finite presentation, then so is `g`. -/
theorem isLocallyOfFinitePresentation_of_comp_of_jointlyLocallySurjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {J : Type v} {X : J → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : ∀ j, IsAlgebraicSpace B S hS (X j))
    (hY : IsAlgebraicSpace B S hS Y)
    (f : ∀ j, X j ⟶ Y) (g : Y ⟶ Z)
    (hfg : ∀ j, IsLocallyOfFinitePresentation B S hS (f j ≫ g))
    (hf : ∀ (U : BigFppfOver B S hS) (s : Y.obj (Opposite.op U)),
      (⨆ j, Presheaf.imageSieve (f j) s) ∈ BigFppfOver.topology B S hS U) :
    IsLocallyOfFinitePresentation B S hS g := by
  have : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{u})
  exact holdsOnEveryEtaleChart_of_comp_of_jointlyLocallySurjective B S hS
    (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
    (fun f' g' _ hcover => locallyOfFinitePresentation_of_comp_of_fppf_refinement f' g' hcover)
    hX hY f g hfg hf

end Space

end AlgebraicGeometry

end
