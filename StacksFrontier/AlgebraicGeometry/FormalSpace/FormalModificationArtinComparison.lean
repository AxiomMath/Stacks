module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ProperSeparatedDiagonal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.AllTestObjects
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautOfRepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothRigSurjectiveClosedImmersionCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveRigEtaleDiagonalCriterion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalModificationBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalModificationBaseChangeAdic
public import StacksFrontier.RingTheory.Rig.JacobianCramerIdealOfDefinition

/-!
# Artin's conditions on a formal modification

Let `S` be a scheme contained in a big fppf site `B`. In [ArtinII, Definition 1.7] a formal
modification is a proper morphism `f : X ⟶ Y` of locally Noetherian formal algebraic spaces
satisfying

1. (i) the Cramer and Jacobian ideal of `f` each contain an ideal of definition of `X`,
2. (ii) the ideal defining the diagonal `Δ_f : X ⟶ X ×_Y X` is annihilated by an ideal of
   definition of `X ×_Y X`, and
3. (iii) any adic morphism `Spf R ⟶ Y` lifts to `Spf R ⟶ X` whenever `R` is a complete
   discrete valuation ring.

**Stacks 0GDL** compares these with the conditions of Definition 0GDK
(`AlgebraicGeometry.FormalSpace.IsFormalModification`): (i) agrees with rig-étaleness of `f`;
for rig-étale `f`, (ii) agrees with rig-surjectivity of `Δ_f`; and once (i) and (ii) hold, (iii)
agrees with rig-surjectivity of `f`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasJacobianCramerIdealOfDefinition`: Artin's condition (i),
  read on the affine étale charts of `f`: on every chart, given by a continuous homomorphism
  `φ : A → C` of Noetherian adic rings, the Jacobian and the Cramer ideal of every completed
  polynomial presentation of `C` over `A` each contain an ideal of definition of `C`.

Artin's condition (ii) is read, as in Stacks 0GD6, as
`AlgebraicGeometry.FormalSpace.HasAnnihilatedKerOnPullbackCharts` for `Δ_f`: on every affine
representable étale chart of `X ×_Y X` the diagonal is given by a surjection of `WAdm^{Noeth}`
whose kernel is annihilated by an ideal of definition of the source. Artin's condition (iii)
is `AlgebraicGeometry.FormalSpace.FactorsAdicCompleteDvrPoints`.

## Main results

* `AlgebraicGeometry.FormalSpace.hasJacobianCramerIdealOfDefinition_iff_isRigEtale`: Ad (i).
* `AlgebraicGeometry.FormalSpace.isRigEtale_diagonal_of_isRigEtale_of_isProper`: the first step
  of Ad (ii), `Δ_f` is rig-étale for `f` proper and rig-étale.
* `AlgebraicGeometry.FormalSpace.hasAnnihilatedKerOnPullbackCharts_diagonal_iff_isRigSurjective`:
  Ad (ii).
* `FormalSpace.factorsAdicCompleteDvrPoints_iff_isRigSurjective_of_artinConditions`: Ad (iii).
* `AlgebraicGeometry.FormalSpace.artinConditions_comparison`: **Stacks 0GDL**, the three
  comparisons together.
* `AlgebraicGeometry.FormalSpace.isFormalModification_iff_artinConditions`: a morphism is a
  formal modification in Artin's sense if and only if it is one in the sense of Definition 0GDK.

## References

* [Stacks Project, Tag 0AJY](https://stacks.math.columbia.edu/tag/0AJY)
* [Stacks Project, Tag 0GD1](https://stacks.math.columbia.edu/tag/0GD1)
* [Stacks Project, Tag 0GD3](https://stacks.math.columbia.edu/tag/0GD3)
* [Stacks Project, Tag 0GD6](https://stacks.math.columbia.edu/tag/0GD6)
* [Stacks Project, Tag 0GDA](https://stacks.math.columbia.edu/tag/0GDA)
* [Stacks Project, Tag 0GDK](https://stacks.math.columbia.edu/tag/0GDK)
* [Stacks Project, Tag 0GDL](https://stacks.math.columbia.edu/tag/0GDL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Ad (i): the Jacobian and the Cramer ideal -/

/-- **Artin's condition (i)** on a morphism `f : X ⟶ Y` of formal algebraic spaces over `S`,
read on its affine étale charts: for every commutative square whose vertical maps are
representable étale maps from affine formal algebraic spaces `U ⟶ X`, `V ⟶ Y`, and every
presentation of the map `U ⟶ V` as the formal spectrum of a continuous homomorphism
`φ : A → C` of Noetherian adic rings, the Jacobian ideal and the Cramer ideal of every completed
polynomial presentation `C = A⟨x₁, …, x_r⟩ / J`, over every ideal of definition of `A` and for
every finite family generating `J`, each contain an ideal of definition of `C`. -/
abbrev HasJacobianCramerIdealOfDefinition {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  HasPropertyOnEveryAffineEtaleDiagram B S hS
    (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
    (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
      [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
      ∀ [IsLinearTopology R₁ R₁] [IsLinearTopology R₂ R₂] [IsNoetherianRing R₁]
        [IsNoetherianRing R₂], RingHom.JacobianCramerContainIdealOfDefinition φ) f

/-- An isomorphism of fppf sheaves is locally of finite type. -/
private theorem isLocallyOfFiniteType_of_isIso {P Q : FppfSheaf B S hS} (e : P ⟶ Q) [IsIso e] :
    IsLocallyOfFiniteType B S hS e :=
  .of_isRepresentableEtale B S hS e (isRepresentableEtale_of_isIso B S hS e)

/-- The chart maps of a morphism locally of finite type are adic and topologically of finite
type, over `WAdm^{Noeth}`. A chart map `t : U ⟶ V` over a morphism `f` locally of finite type is
locally of finite type, hence of finite type between affine formal algebraic spaces, so its
presenting homomorphism is taut and topologically of finite type; tautness out of a Noetherian
adic ring is adicness. -/
private theorem hasPropertyOnEveryAffineEtaleDiagram_isAdic_of_isLocallyOfFiniteType
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hft : IsLocallyOfFiniteType B S hS f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsAdic φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ) f := by
  intro U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hA hRc hwa D E eU eV φ hφ
  have htlft : IsLocallyOfFiniteType B S hS t := by
    refine IsLocallyOfFiniteType.of_comp_of_isAffineFormal B S hS t b hV ?_
    rw [← hsq]
    exact IsLocallyOfFiniteType.comp B S hS a f
      (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS a ha) hft
  have hsrc : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum E) :=
    isAffineFormalAlgebraicSpace_of_iso B S hS eU hU
  have htgt : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D) :=
    isAffineFormalAlgebraicSpace_of_iso B S hS eV hV
  have hmap : IsLocallyOfFiniteType B S hS (formalSpectrumMap hwa φ) := by
    rw [show formalSpectrumMap hwa φ = eU.inv ≫ t ≫ eV.hom by simp [hφ]]
    exact .comp B S hS eU.inv (t ≫ eV.hom) (isLocallyOfFiniteType_of_isIso B S hS _)
      (.comp B S hS t eV.hom htlft (isLocallyOfFiniteType_of_isIso B S hS _))
  obtain ⟨htaut, htft⟩ := isTaut_and_isTopologicallyOfFiniteType_of_isFiniteType_formalSpectrumMap
    B S hS hwa hRc.1.isWeaklyAdmissible D E φ htgt hsrc
    (IsLocallyOfFiniteType.isFiniteType_of_isAffineFormal B S hS _ hsrc htgt hmap)
  have : IsNoetherianRing A := hA.2
  obtain ⟨⟨I, -, hI⟩, -⟩ := hA.1
  let _ : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  have : CompleteSpace R := hRc.1.2.2
  have : T2Space R := hRc.1.2.1
  exact ⟨RingHom.isAdic_of_isTaut φ.toRingHom htaut
    ⟨I, IsNoetherian.noetherian I, hI⟩, htft⟩

/-- **Ad (i) of Stacks 0GDL.** Let `f : X ⟶ Y` be a morphism of formal algebraic spaces over
`S` which is locally of finite type, as Artin's proper morphisms are (local Noetherianity, part
of the setting of 0GDL, is not needed here).
Then Artin's condition (i), that the Jacobian and the Cramer ideal of `f` contain an ideal of
definition of `X`, holds if and only if `f` is rig-étale. Chart by chart this is Stacks 0AJY
(`RingHom.isRigEtale_tfae_jacobianCramer`); local finite typeness makes every chart map adic
and topologically of finite type, which the Jacobian and Cramer ideals presuppose. -/
theorem hasJacobianCramerIdealOfDefinition_iff_isRigEtale {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hft : IsLocallyOfFiniteType B S hS f) :
    HasJacobianCramerIdealOfDefinition B S hS f ↔ IsRigEtale B S hS f := by
  rw [isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram]
  have hloc := hasPropertyOnEveryAffineEtaleDiagram_isAdic_of_isLocallyOfFiniteType B S hS f hft
  constructor
  · intro h U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eV g hg _ _ _ _
    have hfin := ((Rig.adicFiniteType_tfae g.toRingHom hCA.1 hCR.1
      (Rig.exists_idealOfDefinition_fg hCA.1 hCA.2)
      (Rig.exists_idealOfDefinition_fg hCR.1 hCR.2)).out 1 6).mp
      (hloc U V a b t hU hV ha hb hsq A R hCA hCR hA D E eU eV g hg)
    exact ⟨g.continuous, ((RingHom.isRigEtale_tfae_jacobianCramer g.toRingHom g.continuous
      hCA.1 hCR.1 hfin).out 2 1).mp (h U V a b t hU hV ha hb hsq A R hCA hCR hA D E eU eV g hg)⟩
  · intro h U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eV g hg _ _ _ _
    obtain ⟨hcont, hre⟩ := h U V a b t hU hV ha hb hsq A R hCA hCR hA D E eU eV g hg
    exact ((RingHom.isRigEtale_tfae_jacobianCramer g.toRingHom hcont hCA.1 hCR.1
      hre.1).out 1 2).mp hre

/-! ### Ad (ii): the ideal of the diagonal -/

/-- **The first step of Ad (ii) of Stacks 0GDL.** Let `f : X ⟶ Y` be a proper rig-étale
morphism of locally Noetherian formal algebraic spaces over `S`. Then `X ×_Y X` is locally
Noetherian and the relative diagonal `Δ_f : X ⟶ X ×_Y X` is rig-étale: `X` is rig-étale over
`X` via `𝟙 X` (Stacks 0GD3, cancelling `f`) and `X ×_Y X` is rig-étale over `X` via the second
projection (Stacks 0GD1, `f` being adic as it is proper), so `Δ_f` is rig-étale by Stacks 0GD3
applied to `Δ_f ≫ pr₂ = 𝟙 X`. -/
theorem isRigEtale_diagonal_of_isRigEtale_of_isProper {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hproper : IsProper B S hS f) (hf : IsRigEtale B S hS f) :
    IsLocallyNoetherian B S hS (pullback f f) ∧
      IsRigEtale B S hS (pullback.diagonal f) := by
  have hXX := isLocallyNoetherian_pullback_of_isRigEtale B S hS f f hX hY hX hf
    hproper.isRepresentable
  have hsnd := isRigEtale_pullback_snd_of_isLocallyNoetherian B S hS f f hX hY hX hf
    hproper.isRepresentable
  refine ⟨hXX, isRigEtale_of_comp_of_isLocallyNoetherian B S hS (pullback.diagonal f)
    (pullback.snd f f) hX hXX hX ?_ hsnd⟩
  rw [pullback.diagonal_snd]
  exact isRigEtale_of_comp_of_isLocallyNoetherian B S hS (𝟙 X) f hX hX hY
    (by rwa [Category.id_comp]) hf

/-- **Ad (ii) of Stacks 0GDL.** Let `f : X ⟶ Y` be a proper rig-étale morphism of locally
Noetherian formal algebraic spaces over `S`. Then Artin's condition (ii), that on every affine
representable étale chart of `X ×_Y X` the relative diagonal `Δ_f` is given by a surjection of
`WAdm^{Noeth}` whose kernel is annihilated by an ideal of definition of the source, holds if and
only if `Δ_f` is rig-surjective. The diagonal is a closed immersion, `f` being proper hence
separated, and rig-étale, so this is Stacks 0GD6 for `Δ_f`. -/
theorem hasAnnihilatedKerOnPullbackCharts_diagonal_iff_isRigSurjective
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hX : IsLocallyNoetherian B S hS X)
    (hY : IsLocallyNoetherian B S hS Y) (hproper : IsProper B S hS f)
    (hf : IsRigEtale B S hS f) :
    HasAnnihilatedKerOnPullbackCharts B S hS (pullback.diagonal f) ↔
      IsRigSurjective B S hS (pullback.diagonal f) := by
  obtain ⟨hXX, hΔ⟩ := isRigEtale_diagonal_of_isRigEtale_of_isProper B S hS f hX hY hproper hf
  have h0GD6 := isRigSmooth_and_isRigSurjective_tfae_of_isClosedImmersion' B S hS
    (pullback.diagonal f) hX hXX (IsProper.isSeparatedMorphism B S hS hproper)
  refine ⟨fun hker ↦ ?_, fun hsurj ↦ ?_⟩
  · obtain ⟨-, h⟩ := (h0GD6.out 3 2).mp hker
    exact h
  · have h : IsRigEtale B S hS (pullback.diagonal f) ∧
        IsRigSurjective B S hS (pullback.diagonal f) := ⟨hΔ, hsurj⟩
    exact (h0GD6.out 2 3).mp h

/-! ### Ad (iii): lifting adic points over the ring itself -/

/-- **Ad (iii) of Stacks 0GDL.** Let `f : X ⟶ Y` be a proper morphism of locally Noetherian
formal algebraic spaces over `S` satisfying Artin's conditions (i) and (ii). Then Artin's
condition (iii), that every adic morphism `Spf R ⟶ Y` with `R` a complete discrete valuation
ring lifts to `Spf R ⟶ X`, holds if and only if `f` is rig-surjective, which asks for such a
lift only after replacing `R` by an extension. By Ad (i) and Ad (ii) the relative diagonal
`Δ_f` is rig-étale and rig-surjective, so this is Stacks 0GDA. -/
theorem factorsAdicCompleteDvrPoints_iff_isRigSurjective_of_artinConditions
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hX : IsLocallyNoetherian B S hS X)
    (hY : IsLocallyNoetherian B S hS Y) (hproper : IsProper B S hS f)
    (hi : HasJacobianCramerIdealOfDefinition B S hS f)
    (hii : HasAnnihilatedKerOnPullbackCharts B S hS (pullback.diagonal f)) :
    FactorsAdicCompleteDvrPoints B S hS f ↔ IsRigSurjective B S hS f := by
  have hft := IsProper.isLocallyOfFiniteType B S hS hproper
  have hf := (hasJacobianCramerIdealOfDefinition_iff_isRigEtale B S hS f hft).mp hi
  obtain ⟨-, hΔ⟩ := isRigEtale_diagonal_of_isRigEtale_of_isProper B S hS f hX hY hproper hf
  have hΔs := (hasAnnihilatedKerOnPullbackCharts_diagonal_iff_isRigSurjective B S hS f hX hY
    hproper hf).mp hii
  exact (isRigSurjective_iff_factorsAdicCompleteDvrPoints_of_rigEtale_diagonal B S hS f hX hY
    hft hΔ hΔs).symm

/-! ### The remark -/

/-- **Stacks 0GDL.** Let `f : X ⟶ Y` be a proper morphism of locally Noetherian formal
algebraic spaces over `S`, and compare the conditions of Artin's Definition 1.7 of a formal
modification — (i) the Jacobian and the Cramer ideal of `f` each contain an ideal of definition
of `X`, (ii) the ideal of the relative diagonal `Δ_f : X ⟶ X ×_Y X` is annihilated by an ideal
of definition of `X ×_Y X`, (iii) every adic morphism `Spf R ⟶ Y` with `R` a complete discrete
valuation ring lifts to `X` — with those of Definition 0GDK:

* Ad (i): condition (i) holds if and only if `f` is rig-étale;
* Ad (ii): if `f` is rig-étale, then `Δ_f` is rig-étale, and condition (ii) holds if and only
  if `Δ_f` is rig-surjective;
* Ad (iii): if conditions (i) and (ii) hold, condition (iii) holds if and only if `f` is
  rig-surjective.

Conditions (i) and (ii) are read on the affine étale charts of `f` and of `X ×_Y X`, as
`AlgebraicGeometry.FormalSpace.HasJacobianCramerIdealOfDefinition` and
`AlgebraicGeometry.FormalSpace.HasAnnihilatedKerOnPullbackCharts`. -/
@[stacks 0GDL]
theorem artinConditions_comparison {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y)
    (hproper : IsProper B S hS f) :
    (HasJacobianCramerIdealOfDefinition B S hS f ↔ IsRigEtale B S hS f) ∧
      (IsRigEtale B S hS f →
        IsRigEtale B S hS (pullback.diagonal f) ∧
          (HasAnnihilatedKerOnPullbackCharts B S hS (pullback.diagonal f) ↔
            IsRigSurjective B S hS (pullback.diagonal f))) ∧
      (HasJacobianCramerIdealOfDefinition B S hS f →
        HasAnnihilatedKerOnPullbackCharts B S hS (pullback.diagonal f) →
          (FactorsAdicCompleteDvrPoints B S hS f ↔ IsRigSurjective B S hS f)) :=
  ⟨hasJacobianCramerIdealOfDefinition_iff_isRigEtale B S hS f
      (IsProper.isLocallyOfFiniteType B S hS hproper),
    fun hf ↦ ⟨(isRigEtale_diagonal_of_isRigEtale_of_isProper B S hS f hX hY hproper hf).2,
      hasAnnihilatedKerOnPullbackCharts_diagonal_iff_isRigSurjective B S hS f hX hY hproper hf⟩,
    factorsAdicCompleteDvrPoints_iff_isRigSurjective_of_artinConditions B S hS f hX hY hproper⟩

/-- **Artin's formal modifications are those of Definition 0GDK.** A morphism `f : X ⟶ Y` of
locally Noetherian formal algebraic spaces over `S` is a formal modification in the sense of
Artin — proper and satisfying conditions (i), (ii) and (iii) — if and only if it is a formal
modification in the sense of Definition 0GDK. This is the conclusion Stacks 0GDL draws from its
three comparisons. -/
theorem isFormalModification_iff_artinConditions {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsLocallyNoetherian B S hS Y) :
    (IsProper B S hS f ∧ HasJacobianCramerIdealOfDefinition B S hS f ∧
        HasAnnihilatedKerOnPullbackCharts B S hS (pullback.diagonal f) ∧
          FactorsAdicCompleteDvrPoints B S hS f) ↔
      IsFormalModification B S hS f := by
  constructor
  · rintro ⟨hproper, hi, hii, hiii⟩
    obtain ⟨h1, h2, h3⟩ := artinConditions_comparison B S hS f hX hY hproper
    have hf := h1.mp hi
    exact ⟨hX, hY, hproper, hf, (h3 hi hii).mp hiii, (h2 hf).2.mp hii⟩
  · intro h
    obtain ⟨h1, h2, h3⟩ := artinConditions_comparison B S hS f hX hY h.isProper
    have hi := h1.mpr h.isRigEtale
    have hii := (h2 h.isRigEtale).2.mpr h.isRigSurjective_diagonal
    exact ⟨h.isProper, hi, hii, (h3 hi hii).mpr h.isRigSurjective⟩

end AlgebraicGeometry.FormalSpace

end
