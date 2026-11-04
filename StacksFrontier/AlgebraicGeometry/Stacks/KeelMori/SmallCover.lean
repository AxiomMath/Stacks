module

public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.SmallCoverTheorem
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.ModuliFiniteTypeWellNighAffine
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackChartOver
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointSmoothChart
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.StabilizerPreservingUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Size.SmoothCover

/-!
# Small Keel–Mori covers (the set-theoretic footnote of Stacks 0DUT)

The proof of the Keel–Mori theorem (Stacks 0DUT) takes the disjoint union `U = ∐ Mᵢ` of the
moduli spaces of the members of a cover as in Stacks 0DUE, and the source's footnote asks the
reader to make sure that the index set is not too large. Here the cover is refined to one indexed
by the points of a single smooth surjective chart `U₀ ⟶ 𝒳`, and the charts of its members are
bounded uniformly by `2 ^ 2 ^ size U₀`: a quasi-compact scheme `Z` with a 1-morphism to `𝒳` locally
of finite type is covered, through the smooth surjective projection of a smooth chart of
`Z ×_𝒳 U₀`, by finitely many affine opens of that chart, which are locally of finite type over
`U₀`. This makes the cover small (`AlgebraicGeometry.Stack.KeelMoriCover.IsSmall`).

## Main results

* `AlgebraicGeometry.Stack.surjective_siteMap_of_isSurjective`: a surjective 1-morphism of
  represented algebraic stacks comes from a surjective morphism of schemes.
* `AlgebraicGeometry.Stack.size_le_of_isLocallyOfFiniteType_of_smooth_surjective`: a
  quasi-compact scheme locally of finite type over an algebraic stack has size at most
  `2 ^ 2 ^ size U₀` for any smooth surjective chart `U₀`.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_chart_comp_of_isEtale`: the chart of a well-nigh
  affine stack followed by an étale 1-morphism representable by algebraic spaces is locally of
  finite type.
* `AlgebraicGeometry.Stack.exists_keelMoriCover_isSmall`: every cover as in Stacks 0DUE contains
  a small Keel–Mori cover.
* `AlgebraicGeometry.Stack.exists_keelMoriModuliSpace_of_cover`: the Keel–Mori theorem
  (Stacks 0DUT) from a cover as in Stacks 0DUE.
-/

@[expose] public section

open CategoryTheory Cardinal

universe u w

namespace AlgebraicGeometry

namespace Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A surjective 1-morphism of represented algebraic stacks comes from a surjective morphism of
schemes.** -/
theorem surjective_siteMap_of_isSurjective {U V : BigFppfOver B S hS}
    (c : schemeStack.{u, w} B S hS U ⟶ schemeStack.{u, w} B S hS V)
    (hc : IsSurjective B S hS c) :
    Surjective ((BigFppfOver.toScheme B S hS).map (siteMap B S hS c)) := ⟨fun t => by
  let := pointTopology B S hS (schemeFibredCategory B S hS U)
  let := pointTopology B S hS (schemeFibredCategory B S hS V)
  obtain ⟨w, hw⟩ := hc ((pointsHomeomorphScheme B S hS V).symm t)
  refine ⟨pointsHomeomorphScheme B S hS U w, ?_⟩
  rw [← pointsHomeomorphScheme_naturality]
  have hpts := AlgebraicStacks.pointsMap_eq_of_iso B S hS (schemeStackMapIso B S hS c)
  show (pointsHomeomorphScheme B S hS V)
    (AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS (siteMap B S hS c)) w) = t
  rw [← hpts, hw, Homeomorph.apply_symm_apply]⟩

variable (B S hS)

/-- **A quasi-compact scheme with a 1-morphism locally of finite type to an algebraic stack is
bounded by any smooth surjective chart `U₀` of the stack**: its size is at most
`2 ^ 2 ^ size U₀`. A smooth surjective chart `Q` of `Z ×_𝒳 U₀` is smooth and surjective over `Z`
(Stacks 04ZU) and locally of finite type over `U₀`. -/
theorem size_le_of_isLocallyOfFiniteType_of_smooth_surjective (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {U₀ : BigFppfOver B S hS} (a₀ : schemeStack.{u, w} B S hS U₀ ⟶ 𝒳)
    (ha₀ : AlgebraicStacks.IsSmooth B S hS a₀) (ha₀s : IsSurjective B S hS a₀)
    {Z : BigFppfOver B S hS} [CompactSpace ((BigFppfOver.toScheme B S hS).obj Z)]
    (c : schemeStack.{u, w} B S hS Z ⟶ 𝒳) (hc : AlgebraicStacks.IsLocallyOfFiniteType B S hS c) :
    ((BigFppfOver.toScheme B S hS).obj Z).size ≤
      (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ ((BigFppfOver.toScheme B S hS).obj U₀).size := by
  let P := twoFibreProductSquareAlgebraicStacks B S hS c a₀
  have hP : Bicategory.IsTwoFibreProduct P :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS c a₀
  have hPfst : AlgebraicStacks.IsSmooth B S hS P.fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS a₀ c P hP ha₀
  have hPfsts : IsSurjective B S hS P.fst :=
    isSurjective_of_isTwoFibreProduct B S hS P.swap (Bicategory.isTwoFibreProduct_swap hP) ha₀s
  have hPsnd : AlgebraicStacks.IsLocallyOfFiniteType B S hS P.snd :=
    AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS c a₀ P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hc
  obtain ⟨Q, q, hq, hqs⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS P.pt
  have := smooth_siteMap_of_isSmooth B S hS (q ≫ P.fst)
    (AlgebraicStacks.isSmooth_comp B S hS q P.fst hq hPfst)
  have := surjective_siteMap_of_isSurjective (q ≫ P.fst)
    (isSurjective_comp B S hS q P.fst hqs hPfsts)
  have := locallyOfFiniteType_siteMap_of_isLocallyOfFiniteType B S hS (q ≫ P.snd)
    (AlgebraicStacks.isLocallyOfFiniteType_comp B S hS q P.snd
      (AlgebraicStacks.isLocallyOfFiniteType_of_isSmooth B S hS q hq) hPsnd)
  exact Scheme.size_le_of_smooth_surjective_of_locallyOfFiniteType
    ((BigFppfOver.toScheme B S hS).map (siteMap B S hS (q ≫ P.fst)))
    ((BigFppfOver.toScheme B S hS).map (siteMap B S hS (q ≫ P.snd)))

/-- **The chart of a well-nigh affine stack followed by an étale 1-morphism representable by
algebraic spaces is locally of finite type** (Stacks 06FM, 06LT). -/
theorem isLocallyOfFiniteType_chart_comp_of_isEtale {𝒳ᵢ 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (K : WellNighAffineChart.{u, w} B S hS 𝒳ᵢ) (g : 𝒳ᵢ ⟶ 𝒳)
    (hrep : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom) (he : IsEtale B S hS g) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS (K.chart ≫ g) := by
  refine AlgebraicStacks.isLocallyOfFiniteType_comp B S hS K.chart g
    K.isLocallyOfFiniteType_chart ?_
  obtain ⟨-, hrel⟩ := isRelativelyEtale_of_isEtale B S hS g hrep he
  exact (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    𝒳ᵢ.property 𝒳.property g.hom).2 <|
    (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      𝒳ᵢ.property 𝒳.property g.hom hrep).2
      fun V y hy G hG e => Space.isLocallyOfFiniteType_of_isEtale' B S hS _ (hrel V y hy G hG e)

/-- **Every cover as in Stacks 0DUE contains a small Keel–Mori cover.** The family is re-indexed
by the points of one smooth surjective chart `U₀` of `𝒳`, each point going to a member through
which its image passes, and the charts of the members are bounded by `2 ^ 2 ^ size U₀`. -/
theorem exists_keelMoriCover_isSmall (𝒳 : AlgebraicStacks.{u, w} B S hS) {ι : Type*}
    (𝒳ᵢ : ι → AlgebraicStacks.{u, w} B S hS) (g : ∀ i, 𝒳ᵢ i ⟶ 𝒳)
    (hcov : ∀ x : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids,
      ∃ (i : ι) (y : points B S hS (𝒳ᵢ i).val.val (𝒳ᵢ i).val.isFiberedInGroupoids),
        pointsMap B S hS (𝒳ᵢ i).val.val (𝒳ᵢ i).val.isFiberedInGroupoids
          𝒳.val.isFiberedInGroupoids (g i).hom.hom y = x)
    (hwna : ∀ i, IsWellNighAffine.{u, w} B S hS (𝒳ᵢ i))
    (hstab : ∀ i, IsStabilizerPreserving B S hS (g i))
    (hrep : ∀ i, IsRepresentableByAlgebraicSpaces B S hS (g i).hom.hom)
    (hsep : ∀ i, AlgebraicStacks.IsSeparated B S hS (g i))
    (het : ∀ i, IsEtale B S hS (g i)) :
    ∃ C : KeelMoriCover B S hS 𝒳, C.IsSmall := by
  classical
  obtain ⟨U₀, a₀, ha₀, ha₀s⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS 𝒳
  let := pointTopology B S hS (schemeFibredCategory B S hS U₀)
  let T₀ := (BigFppfOver.toScheme B S hS).obj U₀
  choose idx pt hpt using fun v : T₀ =>
    hcov (AlgebraicStacks.pointsMap B S hS a₀ ((pointsHomeomorphScheme B S hS U₀).symm v))
  let C : KeelMoriCover B S hS 𝒳 :=
    { ι := T₀
      obj := fun v => 𝒳ᵢ (idx v)
      map := fun v => g (idx v)
      wellNighAffine := fun v => hwna (idx v)
      chart := fun v => (nonempty_wellNighAffineChart B S hS _ (hwna (idx v))).some
      cover := fun x => by
        obtain ⟨w, hw⟩ := ha₀s x
        refine ⟨pointsHomeomorphScheme B S hS U₀ w, pt _, ?_⟩
        rw [hpt, Homeomorph.symm_apply_apply, hw]
      inducesIso := fun v q =>
        inducesIsomorphismAt_of_inertiaPullbackComparison_isEquivalenceOver B S hS _
          (hstab (idx v)) q
      rep := fun v => hrep (idx v)
      separated := fun v => hsep (idx v)
      etale := fun v => het (idx v) }
  have hT₀ : T₀.size < B.cutoff := U₀.left.2
  refine ⟨C, (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ T₀.size,
    T₀.aleph0_le_size.trans ((cantor _).le.trans (cantor _).le),
    B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit hT₀),
    T₀.mk_le_two_pow_size.trans (power_le_power_left two_ne_zero (cantor _).le), fun v => ?_⟩
  let K := C.chart v
  have := K.isAffine_U
  exact size_le_of_isLocallyOfFiniteType_of_smooth_surjective B S hS 𝒳 a₀ ha₀ ha₀s
    (K.chart ≫ g (idx v))
    (isLocallyOfFiniteType_chart_comp_of_isEtale B S hS K (g (idx v)) (hrep (idx v)) (het (idx v)))

/-- **The Keel–Mori theorem from a cover as in Stacks 0DUE** (Stacks 0DUT): for an algebraic
stack with a family of 1-morphisms from well-nigh affine stacks, jointly surjective on points,
stabilizer preserving, representable by algebraic spaces, separated and étale, there is a uniform
categorical moduli space `f : 𝒳 ⟶ M` which is separated, quasi-compact and a universal
homeomorphism, and which has well-nigh affine moduli pieces. -/
theorem exists_keelMoriModuliSpace_of_cover (𝒳 : AlgebraicStacks.{u, w} B S hS) {ι : Type*}
    (𝒳ᵢ : ι → AlgebraicStacks.{u, w} B S hS) (g : ∀ i, 𝒳ᵢ i ⟶ 𝒳)
    (hcov : ∀ x : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids,
      ∃ (i : ι) (y : points B S hS (𝒳ᵢ i).val.val (𝒳ᵢ i).val.isFiberedInGroupoids),
        pointsMap B S hS (𝒳ᵢ i).val.val (𝒳ᵢ i).val.isFiberedInGroupoids
          𝒳.val.isFiberedInGroupoids (g i).hom.hom y = x)
    (hwna : ∀ i, IsWellNighAffine.{u, w} B S hS (𝒳ᵢ i))
    (hstab : ∀ i, IsStabilizerPreserving B S hS (g i))
    (hrep : ∀ i, IsRepresentableByAlgebraicSpaces B S hS (g i).hom.hom)
    (hsep : ∀ i, AlgebraicStacks.IsSeparated B S hS (g i))
    (het : ∀ i, IsEtale B S hS (g i)) :
    ∃ (M : AlgebraicSpaces B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property),
      IsUniformCategoricalModuliSpace B S hS M f.hom ∧ AlgebraicStacks.IsSeparated B S hS f ∧
        IsQuasiCompactMorphism.{u, w} B S hS f ∧ UniversalHomeomorphism B S hS f ∧
          HasWellNighAffineModuliPieces B S hS f := by
  obtain ⟨C, hC⟩ := exists_keelMoriCover_isSmall B S hS 𝒳 𝒳ᵢ g hcov hwna hstab hrep hsep het
  exact KeelMoriCover.exists_keelMoriModuliSpace_of_isSmall hC

end Stack

end AlgebraicGeometry

end
