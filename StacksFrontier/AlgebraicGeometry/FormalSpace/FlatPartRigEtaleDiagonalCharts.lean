module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicDvrPointThroughPrime
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProductFormalBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletedTensorFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleAdicPointLift
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleStageFormalSpectrumMap
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeNoetherianRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartOverCdvrDescent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleCancellationGeneral
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFormallyEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableFormalSpectrumTaut
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FlatBaseChangeLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleClosedImmersionCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocalCharacterizationCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocallyOfFiniteTypeUnconditional
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjective
public import StacksFrontier.RingTheory.IdempotentIdealOfPointConditions
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FlatBaseChangeLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautOfRepresentableByAlgebraicSpaces

/-!
# Charts of a flat formal algebraic space with rig-étale rig-surjective diagonal

Let `A` be a complete discrete valuation ring and `q : X' ⟶ Spf A` a flat morphism locally of
finite type from a locally Noetherian formal algebraic space whose relative diagonal is rig-étale
and rig-surjective. This file proves, for an affine representable étale chart `U = Spf Bu` of
`X'`, that the kernel of the diagonal `μ : R → Bu` of `U` over `A` is idempotent, `R` being the
chart ring of `U ×_{Spf A} U`. This is the step of the proof of Stacks 0GD9 replacing the source's
appeal to Stacks 0GD6 for `U ×_{X'} U ⟶ U ×_{Spf A} U`, a morphism not known to be a closed
immersion at that point.

The kernel `J` of `μ` satisfies `π ^ N J ⊆ J ^ 2` by rig-étaleness of the diagonal (Stacks 0GD4
on one chart), and every adic point of `Spf R` out of a complete discrete valuation ring which
reduces into the diagonal kills `J` by rig-surjectivity of the diagonal, a formally étale lift
along `U ×_{X'} U ⟶ U` identifying its two components;
`Ideal.isIdempotentElem_of_span_pow_mul_le_sq` concludes.

## Main results

* `AlgebraicGeometry.FormalSpace.isAffine_and_isNoetherian_pullback_charts`: fibre products of
  Noetherian charts over `Spf A` are Noetherian affine.
* `AlgebraicGeometry.FormalSpace.map_eq_zero_of_mem_ker_of_isRigSurjective_diagonal`: adic points
  reducing into the diagonal lie on it.
* `AlgebraicGeometry.FormalSpace.flat_of_isPullback_charts`: their chart rings are flat over `A`.
* `AlgebraicGeometry.FormalSpace.isIdempotentElem_ker_of_isRigEtale_of_isRigSurjective_diagonal`:
  the kernel of the diagonal of a chart is idempotent.
* `AlgebraicGeometry.FormalSpace.isFlat_pullback_snd_of_isLocallyNoetherian_of_isFlat`: flat base
  change (Stacks 0GCE, part (2), flatness) through chart conditions proved here.

## References

* [Stacks Project, Tag 0GD9](https://stacks.math.columbia.edu/tag/0GD9)
* [Stacks Project, Tag 0GD4](https://stacks.math.columbia.edu/tag/0GD4)
* [Stacks Project, Tag 0AQS](https://stacks.math.columbia.edu/tag/0AQS)
* [Stacks Project, Tag 0GCE](https://stacks.math.columbia.edu/tag/0GCE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Base

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [IsNoetherianRing A]

omit [IsNoetherianRing A] in
/-- A Noetherian ring complete for an adic topology defined by an ideal is an adic topological
ring in the sense of `TopologicalRing.IsAdic`. -/
theorem topologicalRingIsAdic_of_isAdic_of_isAdicComplete {I : Ideal A} (hI : _root_.IsAdic I)
    (hc : IsAdicComplete I A) : TopologicalRing.IsAdic A :=
  have hw := TopologicalRing.isWeaklyAdmissible_of_isAdic hI hc
  ⟨⟨I, TopologicalRing.isIdealOfDefinition_of_isAdic hI, hI⟩, hw.2.2, hw.2.1⟩

variable (D : QuotientSystem B S hS A)

omit [IsNoetherianRing A] in
/-- **Fibre products of Noetherian charts over a Noetherian adic base.** Let `q : X' ⟶ Spf A` be
locally of finite type with `X'` locally Noetherian, and let `a : U ⟶ X'`, `b : V ⟶ X'` be
affine representable étale charts. Then `U ×_{Spf A} V` is an affine formal algebraic space
(Stacks 0AN3, clause (1), `Spf A` being separated), locally Noetherian (Stacks 0AQ8) and hence
Noetherian. -/
theorem isAffine_and_isNoetherian_pullback_charts (hA : TopologicalRing.IsAdic A)
    {X' U V : FppfSheaf B S hS} (q : X' ⟶ formalSpectrum D) (hX' : IsLocallyNoetherian B S hS X')
    (hq : IsLocallyOfFiniteType B S hS q) {a : U ⟶ X'} {b : V ⟶ X'}
    (hU : IsAffineFormalAlgebraicSpace B S hS U) (hV : IsAffineFormalAlgebraicSpace B S hS V)
    (ha : IsRepresentableEtale B S hS a) (hb : IsRepresentableEtale B S hS b) :
    IsAffineFormalAlgebraicSpace B S hS (pullback (a ≫ q) (b ≫ q)) ∧
      IsLocallyNoetherian B S hS (pullback (a ≫ q) (b ≫ q)) ∧
        IsNoetherian B S hS (pullback (a ≫ q) (b ≫ q)) := by
  have hSpf := isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic B S hS hA D
    (Iso.refl _)
  have haff := isAffineFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS
    (a ≫ q) (b ≫ q) (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hSpf)
    (IsAffineFormalAlgebraicSpace.isSeparated B S hS hSpf) hU hV
  have hUn := isLocallyNoetherian_of_isAffine_of_isNoetherian B S hS hU
    (isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hX' a hU ha)
  have hbq : IsLocallyOfFiniteType B S hS (b ≫ q) :=
    IsLocallyOfFiniteType.comp B S hS b q
      (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS b hb) hq
  have hloc := isLocallyNoetherian_of_isPullback' B S hS
    (IsPullback.of_hasPullback (a ≫ q) (b ≫ q))
    (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hV)
    (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hSpf) hUn hbq
  exact ⟨haff, hloc, isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hloc
    (𝟙 _) haff (isRepresentableEtale_id B S hS _)⟩

end Base

section Conormal

/-- **The conormal module of a rig-étale surjection is killed by an ideal of definition.** A
surjective rig-étale continuous homomorphism `μ : R → C` of Noetherian adic rings has kernel `J`
with `I J ⊆ J ^ 2` for an ideal of definition `I` of `R`. This is the implication
(1) ⟹ (3) of Stacks 0GD4 read on one chart, through Stacks 0GD0. -/
theorem exists_isIdealOfDefinition_mul_ker_le_sq_of_isRigEtale {R C : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] [IsNoetherianRing R]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    [IsNoetherianRing C] (hR : TopologicalRing.IsAdic R) (hC : TopologicalRing.IsAdic C)
    (μ : R →+* C) (hμ : Continuous μ) (hsurj : Function.Surjective μ)
    (hre : RingHom.IsRigEtale μ) :
    ∃ I : Ideal R, TopologicalRing.IsIdealOfDefinition I ∧
      I * RingHom.ker μ ≤ RingHom.ker μ ^ 2 := by
  obtain ⟨hft, I, hI, hc, hfin, hre'⟩ := hre
  have hsm : Rig.IsRigSmooth (Rig.adicFiniteTypeAlgebra μ hft I hI) := by
    let _ : Algebra R C := μ.toAlgebra
    let _ : Algebra.FiniteType (R ⧸ I) (C ⧸ I.map (algebraMap R C)) := hfin
    have heq : Rig.adicFiniteTypeAlgebra μ hft I hI =
        Rig.AdicFiniteTypeAlgebra.of (I := I) C hc := by
      apply ObjectProperty.FullSubcategory.ext
      rfl
    rw [heq]
    exact Rig.isRigSmooth_of_isRigEtale _ hre'
  obtain ⟨I₀, hI₀def, hI₀adic, hI₀complete⟩ := exists_idealOfDefinition_isAdicComplete hR
  have hsm₀ : Rig.IsRigSmooth (Rig.adicFiniteTypeAlgebra μ hft I₀ hI₀def) :=
    (Rig.isRigSmooth_iff_forall_idealOfDefinition (Rig.weaklyAdmissible_of_isAdicRing hR)
      (Rig.weaklyAdmissible_of_isAdicRing hC) μ hμ hft).mp ⟨I, hI, hsm⟩ I₀ hI₀def
  let _ : IsAdicComplete I₀ R := hI₀complete
  obtain ⟨c, hc⟩ := (Rig.isRigSmooth_iff_exists_pow_mul_ker_le_sq
    (Rig.adicFiniteTypeAlgebra μ hft I₀ hI₀def) hsurj).mp hsm₀
  exact ⟨I₀ ^ (c + 1), isIdealOfDefinition_pow_succ hI₀adic c,
    Ideal.mul_le.mpr fun r hr x hx => hc r (Ideal.pow_le_pow_right (Nat.le_succ c) hr) x hx⟩

end Conormal

section Stage

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C]

/-- **Two formal spectrum maps agree on a stage on which their ring maps agree.** If two
continuous homomorphisms `ψ₁ ψ₂ : A → C` over `S` agree modulo a weak ideal of definition `K` of
`C`, then the two morphisms `Spf ψᵢ` agree on the quotient stage `Spec (C ⧸ K)` of `Spf C`: both
are the composite of the stage map `Spec (C ⧸ K) ⟶ Spec (A ⧸ J)` they induce, for a common weak
ideal of definition `J` of `A` carried into `K`, with the inclusion of that stage. -/
theorem formalSpectrumInclusion_comp_formalSpectrumMap_eq
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    {D : QuotientSystem B S hS A} {E : QuotientSystem B S hS C} (ψ₁ ψ₂ : ContinuousHom D E)
    (K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I })
    (hψ : ∀ x : A, ψ₁.toRingHom x - ψ₂.toRingHom x ∈ K.1) :
    formalSpectrumInclusion E (OrderDual.toDual K) ≫ formalSpectrumMap hA ψ₁ =
      formalSpectrumInclusion E (OrderDual.toDual K) ≫ formalSpectrumMap hA ψ₂ := by
  obtain ⟨J, hJ⟩ := exists_isWeakIdealOfDefinition_le_comap hA.1 ψ₁.toRingHom ψ₁.continuous K
  have hJ₂ : J.1 ≤ Ideal.comap ψ₂.toRingHom K.1 := fun x hx => by
    rw [Ideal.mem_comap, show ψ₂.toRingHom x = ψ₁.toRingHom x - (ψ₁.toRingHom x -
      ψ₂.toRingHom x) by ring]
    exact K.1.sub_mem (Ideal.mem_comap.mp (hJ hx)) (hψ x)
  rw [formalSpectrumMap_spec hA ψ₁ J K hJ, formalSpectrumMap_spec hA ψ₂ J K hJ₂]
  have hq : Ideal.quotientMap K.1 ψ₁.toRingHom hJ = Ideal.quotientMap K.1 ψ₂.toRingHom hJ₂ := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply, Ideal.quotientMap_mk]
    exact Ideal.Quotient.eq.mpr (hψ x)
  have hs : ψ₁.stageMap J K hJ = ψ₂.stageMap J K hJ₂ := by
    unfold ContinuousHom.stageMap
    congr 3
    rw [hq]
  rw [hs]

end Stage

section EtaleUniqueness

variable {W : Type u} [CommRing W] [TopologicalSpace W] [IsTopologicalRing W] {I : Ideal W}

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Lifts of an adic point along a formally étale morphism are unique.** Let `f : X ⟶ Y` be a
formally étale morphism of fppf sheaves over `S` and let `W` carry the `I`-adic topology, with a
quotient system `D`. Two morphisms `Spf W ⟶ X` which agree after composition with `f` and agree
on the closed stage `Spec (W ⧸ I)` are equal: by induction along the tower of square-zero
thickenings `Spec (W ⧸ Iⁿ⁺¹) ⊂ Spec (W ⧸ Iⁿ⁺²)`, both restrictions to each stage are lifts of the
same square, and formal étaleness makes such a lift unique. -/
theorem formalSpectrum_hom_eq_of_formallyEtale {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : Space.FormallyEtale f.hom) (hadic : _root_.IsAdic I) (D : QuotientSystem B S hS W)
    {z₁ z₂ : formalSpectrum D ⟶ X} (h : z₁ ≫ f = z₂ ≫ f)
    (h₀ : formalSpectrumInclusion D (OrderDual.toDual (adicStage hadic 0)) ≫ z₁ =
      formalSpectrumInclusion D (OrderDual.toDual (adicStage hadic 0)) ≫ z₂) :
    z₁ = z₂ := by
  classical
  let Jt := BigFppfOver.topology B S hS
  let ι : ∀ n, (formalSpectrumDiagram D).obj (OrderDual.toDual (adicStage hadic n)) ⟶
      formalSpectrum D := fun n => formalSpectrumInclusion D (OrderDual.toDual (adicStage hadic n))
  let g : ∀ n, OrderDual.toDual (adicStage hadic n) ⟶ OrderDual.toDual (adicStage hadic (n + 1)) :=
    fun n => homOfLE (adicStage_le_succ hadic n)
  have hg : ∀ n, (formalSpectrumDiagram D).map (g n) =
      (Sheaf.sheafifiedYoneda Jt).map (adicTowerMap D hadic n) := fun n => rfl
  have hι : ∀ n, (formalSpectrumDiagram D).map (g n) ≫ ι (n + 1) = ι n := fun n =>
    colimit.w (formalSpectrumDiagram D) (g n)
  have key : ∀ n, ι n ≫ z₁ = ι n ≫ z₂ := by
    intro n
    induction n with
    | zero => exact h₀
    | succ n ih =>
      have hlift : ∀ z : formalSpectrum D ⟶ X,
          Space.IsLift f.hom (adicTowerMap D hadic n) (Sheaf.sectionEquiv Jt (ι n ≫ z))
            (Sheaf.sectionEquiv Jt (ι (n + 1) ≫ z ≫ f))
            (Sheaf.sectionEquiv Jt (ι (n + 1) ≫ z)) := by
        intro z
        refine ⟨?_, ?_⟩
        · exact (Sheaf.sectionEquiv_map_comp Jt (adicTowerMap D hadic n) (ι (n + 1) ≫ z)).symm.trans
            (congrArg (Sheaf.sectionEquiv Jt)
              ((Category.assoc _ _ _).symm.trans (congrArg (fun c => c ≫ z) (hι n))))
        · exact (Sheaf.sectionEquiv_comp Jt (ι (n + 1) ≫ z) f).symm.trans
            (congrArg (Sheaf.sectionEquiv Jt) (Category.assoc _ _ _))
      have hy : f.hom.app _ (Sheaf.sectionEquiv Jt (ι n ≫ z₂)) =
          Y.obj.map (adicTowerMap D hadic n).op (Sheaf.sectionEquiv Jt (ι (n + 1) ≫ z₂ ≫ f)) := by
        refine (Sheaf.sectionEquiv_comp Jt (ι n ≫ z₂) f).symm.trans ?_
        refine Eq.trans ?_ (Sheaf.sectionEquiv_map_comp Jt (adicTowerMap D hadic n)
          (ι (n + 1) ≫ z₂ ≫ f))
        refine congrArg (Sheaf.sectionEquiv Jt) ?_
        refine (Category.assoc _ _ _).trans ?_
        refine Eq.trans ?_ (Category.assoc _ _ _)
        exact congrArg (fun c => c ≫ z₂ ≫ f) (hι n).symm
      have huniq := hf _ _ (isAffine_stageObj D (adicStage hadic n))
        (isAffine_stageObj D (adicStage hadic (n + 1))) (adicTowerMap D hadic n)
        (isSquareZeroClosedImmersion_adicTowerMap D hadic n) _ _ hy
      have h₁ : Space.IsLift f.hom (adicTowerMap D hadic n) (Sheaf.sectionEquiv Jt (ι n ≫ z₂))
          (Sheaf.sectionEquiv Jt (ι (n + 1) ≫ z₂ ≫ f))
          (Sheaf.sectionEquiv Jt (ι (n + 1) ≫ z₁)) := by
        have h' := hlift z₁
        have e1 : Sheaf.sectionEquiv Jt (ι n ≫ z₁) = Sheaf.sectionEquiv Jt (ι n ≫ z₂) :=
          congrArg _ ih
        have e2 : Sheaf.sectionEquiv Jt (ι (n + 1) ≫ z₁ ≫ f) =
            Sheaf.sectionEquiv Jt (ι (n + 1) ≫ z₂ ≫ f) := congrArg (fun c => Sheaf.sectionEquiv Jt
              (ι (n + 1) ≫ c)) h
        exact ⟨h'.1.trans e1, h'.2.trans e2⟩
      exact (Sheaf.sectionEquiv Jt).injective (huniq.unique h₁ (hlift z₂))
  exact formalSpectrum_hom_ext_of_cofinal D (adicStage hadic) (exists_adicStage_le hadic) key

end EtaleUniqueness

section PullbackMap

/-- **The product of two representable étale maps over a base is representable étale.** For
`a : X' ⟶ X` and `b : Y' ⟶ Y` representable étale over `f : X ⟶ Z` and `g : Y ⟶ Z`, the induced
`X' ×_Z Y' ⟶ X ×_Z Y` is representable étale: it is the composite of a base change of `a` and a
base change of `b`. -/
theorem isRepresentableEtale_pullback_map {X Y Z X' Y' : FppfSheaf B S hS} (f : X ⟶ Z)
    (g : Y ⟶ Z) {a : X' ⟶ X} {b : Y' ⟶ Y} (ha : IsRepresentableEtale B S hS a)
    (hb : IsRepresentableEtale B S hS b) :
    IsRepresentableEtale B S hS
      (pullback.map (a ≫ f) (b ≫ g) f g a b (𝟙 Z) (by simp) (by simp)) := by
  let m₁ : pullback (a ≫ f) (b ≫ g) ⟶ pullback f (b ≫ g) :=
    pullback.map (a ≫ f) (b ≫ g) f (b ≫ g) a (𝟙 _) (𝟙 Z) (by simp) (by simp)
  let m₂ : pullback f (b ≫ g) ⟶ pullback f g :=
    pullback.map f (b ≫ g) f g (𝟙 _) b (𝟙 Z) (by simp) (by simp)
  have hm : pullback.map (a ≫ f) (b ≫ g) f g a b (𝟙 Z) (by simp) (by simp) = m₁ ≫ m₂ :=
    pullback.hom_ext (by simp [m₁, m₂]) (by simp [m₁, m₂])
  have hsq₁ : IsPullback m₁ (pullback.fst (a ≫ f) (b ≫ g)) (pullback.fst f (b ≫ g)) a := by
    refine IsPullback.of_right ?_ (by simp [m₁]) (IsPullback.of_hasPullback f (b ≫ g)).flip
    rw [show m₁ ≫ pullback.snd f (b ≫ g) = pullback.snd (a ≫ f) (b ≫ g) by simp [m₁]]
    exact (IsPullback.of_hasPullback (a ≫ f) (b ≫ g)).flip
  have hsq₂ : IsPullback (pullback.snd f (b ≫ g)) m₂ b (pullback.snd f g) := by
    refine (IsPullback.of_right ?_ (by simp [m₂]) (IsPullback.of_hasPullback f g)).flip
    rw [show m₂ ≫ pullback.fst f g = pullback.fst f (b ≫ g) by simp [m₂]]
    exact IsPullback.of_hasPullback f (b ≫ g)
  rw [hm]
  exact IsRepresentableEtale.comp B S hS (isRepresentableEtale_of_isPullback B S hS hsq₁.flip ha)
    (isRepresentableEtale_of_isPullback B S hS hsq₂ hb)

end PullbackMap

section RingMaps

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- Continuous homomorphisms over `S` with the same formal spectrum map are equal (Stacks 0AN0). -/
theorem ContinuousHom.eq_of_formalSpectrumMap_eq (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hC : TopologicalRing.IsWeaklyAdmissible C) {D : QuotientSystem B S hS A}
    {E : QuotientSystem B S hS C} {f g : ContinuousHom D E}
    (h : formalSpectrumMap hA f = formalSpectrumMap hA g) : f = g :=
  (existsUnique_continuousHom_formalSpectrumMap_eq hA hC (formalSpectrumMap hA g)).unique h rfl

end RingMaps

section KernelOfDiagonal

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] (D : QuotientSystem B S hS A)
  {Bu R : Type u} [CommRing Bu] [TopologicalSpace Bu] [IsTopologicalRing Bu]
  [IsLinearTopology Bu Bu] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [IsLinearTopology R R]

/-- A ring map presenting a projection of `U ×_Z U` is split by the diagonal presentation `μ`. -/
private theorem comp_eq_id_of_formalSpectrumMap_diagonal {Z U : FppfSheaf B S hS} (f : U ⟶ Z)
    (hBu : TopologicalRing.IsWeaklyAdmissible Bu) (hR : TopologicalRing.IsWeaklyAdmissible R)
    {EU : QuotientSystem B S hS Bu} {EP : QuotientSystem B S hS R} (eU : U ≅ formalSpectrum EU)
    (eP : pullback f f ≅ formalSpectrum EP) (μ : ContinuousHom EP EU)
    (hμ : formalSpectrumMap hR μ = eU.inv ≫ pullback.diagonal f ≫ eP.hom)
    (ρ : ContinuousHom EU EP) (pr : pullback f f ⟶ U) (hpr : pullback.diagonal f ≫ pr = 𝟙 U)
    (hρ : formalSpectrumMap hBu ρ = eP.inv ≫ pr ≫ eU.hom) :
    μ.toRingHom.comp ρ.toRingHom = RingHom.id Bu := by
  have hcomp : formalSpectrumMap hBu (ContinuousHom.comp hR hBu μ ρ) =
      formalSpectrumMap hBu (ContinuousHom.id EU) := by
    rw [formalSpectrumMap_id hBu (ContinuousHom.id EU) rfl, ← formalSpectrumMap_comp_eq, hμ, hρ]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (pullback.diagonal f), hpr]
    simp
  exact congrArg ContinuousHom.toRingHom
    (ContinuousHom.eq_of_formalSpectrumMap_eq B S hS hBu hBu hcomp)

omit [IsTopologicalRing A] [IsLinearTopology A A] in
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **An adic point of the self-product of a chart which reduces into the diagonal lies on it.**
Let `q : X' ⟶ Spf A` have rig-surjective relative diagonal and let `a : U ⟶ X'` be
representable étale, with `U = Spf Bu` and `U ×_{Spf A} U = Spf R`; let `μ : R → Bu` present the
diagonal and `ρ₁, ρ₂ : Bu → R` the two projections. If an adic point `χ : R → W` out of a complete
discrete valuation ring carries the kernel `J` of `μ` into the maximal ideal of `W`, then `χ`
kills `J`.

Rig-surjectivity of the diagonal gives an extension `W ⊂ W'` over which the two points
`Spf W' ⟶ U` agree in `X'`, so they define a point of `U ×_{X'} U`; it lifts the first of them
along the étale projection `U ×_{X'} U ⟶ U`, as does the composite of the first point with the
diagonal of `a`, and the two lifts agree on the closed stage because `χ` reduces into the
diagonal. By formal étaleness they agree, so the two points agree, and `χ` factors through `μ`. -/
theorem map_eq_zero_of_mem_ker_of_isRigSurjective_diagonal {X' U : FppfSheaf B S hS}
    (q : X' ⟶ formalSpectrum D) (a : U ⟶ X') (ha : IsRepresentableEtale B S hS a)
    (hdiag : IsRigSurjective B S hS (pullback.diagonal q))
    (hBu : TopologicalRing.IsWeaklyAdmissible Bu) (hR : TopologicalRing.IsWeaklyAdmissible R)
    {EU : QuotientSystem B S hS Bu} {EP : QuotientSystem B S hS R}
    (eU : U ≅ formalSpectrum EU) (eP : pullback (a ≫ q) (a ≫ q) ≅ formalSpectrum EP)
    (μ : ContinuousHom EP EU)
    (hμ : formalSpectrumMap hR μ = eU.inv ≫ pullback.diagonal (a ≫ q) ≫ eP.hom)
    (ρ₁ ρ₂ : ContinuousHom EU EP)
    (hρ₁ : formalSpectrumMap hBu ρ₁ = eP.inv ≫ pullback.fst (a ≫ q) (a ≫ q) ≫ eU.hom)
    (hρ₂ : formalSpectrumMap hBu ρ₂ = eP.inv ≫ pullback.snd (a ≫ q) (a ≫ q) ≫ eU.hom)
    (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [TopologicalSpace W]
    [IsTopologicalRing W] [IsLinearTopology W W]
    (hWadic : _root_.IsAdic (IsLocalRing.maximalIdeal W))
    (hWc : IsAdicComplete (IsLocalRing.maximalIdeal W) W)
    (hWw : TopologicalRing.IsWeaklyAdmissible W) (DW : QuotientSystem B S hS W)
    (χ : ContinuousHom EP DW)
    (hχrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (formalSpectrumMap hR χ).hom)
    (hχ : ∀ x ∈ RingHom.ker μ.toRingHom, χ.toRingHom x ∈ IsLocalRing.maximalIdeal W) :
    ∀ x ∈ RingHom.ker μ.toRingHom, χ.toRingHom x = 0 := by
  classical
  -- the chart `U ×_{Spf A} U ⟶ X' ×_{Spf A} X'` and the adic point of `X' ×_{Spf A} X'`
  obtain ⟨bm, hbmdef⟩ : ∃ bm : pullback (a ≫ q) (a ≫ q) ⟶ pullback q q,
      bm = pullback.map (a ≫ q) (a ≫ q) q q a a (𝟙 _) (by simp) (by simp) := ⟨_, rfl⟩
  have hbm : IsRepresentableEtale B S hS bm := by
    rw [hbmdef]; exact isRepresentableEtale_pullback_map B S hS q q ha ha
  have hbm₁ : bm ≫ pullback.fst q q = pullback.fst (a ≫ q) (a ≫ q) ≫ a := by
    rw [hbmdef]; exact pullback.lift_fst _ _ _
  have hbm₂ : bm ≫ pullback.snd q q = pullback.snd (a ≫ q) (a ≫ q) ≫ a := by
    rw [hbmdef]; exact pullback.lift_snd _ _ _
  obtain ⟨pt, hptdef⟩ : ∃ pt : formalSpectrum DW ⟶ pullback (a ≫ q) (a ≫ q),
      pt = formalSpectrumMap hR χ ≫ eP.inv := ⟨_, rfl⟩
  have hptrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (pt ≫ bm).hom := by
    rw [hptdef]
    exact Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ bm.hom
      (Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _ hχrep
        (isAdicMorphism_of_isIso B S hS eP.inv)) hbm.1
  obtain ⟨W', hW'ring, hW'dom, hW'dvr, hW'alg, hW'ext, hW'top, hW'topring, hW'lin, hW'adic,
    hW'c, D', e, x, he, hx⟩ := hdiag W hWadic hWc hWw DW (pt ≫ bm) hptrep
  let : CommRing W' := hW'ring
  let : IsDomain W' := hW'dom
  let : IsDiscreteValuationRing W' := hW'dvr
  let : Algebra W W' := hW'alg
  let : IsDiscreteValuationRing.IsExtension W W' := hW'ext
  let : TopologicalSpace W' := hW'top
  let : IsTopologicalRing W' := hW'topring
  let : IsLinearTopology W' W' := hW'lin
  have hW'w : TopologicalRing.IsWeaklyAdmissible W' :=
    TopologicalRing.isWeaklyAdmissible_of_isAdic hW'adic hW'c
  obtain ⟨E, hEdef⟩ : ∃ E, E = formalSpectrumMap hWw e := ⟨_, rfl⟩
  rw [← hEdef] at hx
  -- the two points of `U` over `W'` agree in `X'`
  obtain ⟨y₁, hy₁def⟩ : ∃ y : formalSpectrum D' ⟶ U,
      y = E ≫ pt ≫ pullback.fst (a ≫ q) (a ≫ q) := ⟨_, rfl⟩
  obtain ⟨y₂, hy₂def⟩ : ∃ y : formalSpectrum D' ⟶ U,
      y = E ≫ pt ≫ pullback.snd (a ≫ q) (a ≫ q) := ⟨_, rfl⟩
  have hy₁ : y₁ ≫ a = x := by
    calc y₁ ≫ a = E ≫ pt ≫ bm ≫ pullback.fst q q := by rw [hy₁def, hbm₁]; simp
      _ = (x ≫ pullback.diagonal q) ≫ pullback.fst q q := by rw [hx]; simp
      _ = x := by simp
  have hy₂ : y₂ ≫ a = x := by
    calc y₂ ≫ a = E ≫ pt ≫ bm ≫ pullback.snd q q := by rw [hy₂def, hbm₂]; simp
      _ = (x ≫ pullback.diagonal q) ≫ pullback.snd q q := by rw [hx]; simp
      _ = x := by simp
  -- the two points are formal spectra of ring maps agreeing modulo the maximal ideal
  have hρ₁' : eP.inv ≫ pullback.fst (a ≫ q) (a ≫ q) = formalSpectrumMap hBu ρ₁ ≫ eU.inv := by
    rw [hρ₁]; simp
  have hρ₂' : eP.inv ≫ pullback.snd (a ≫ q) (a ≫ q) = formalSpectrumMap hBu ρ₂ ≫ eU.inv := by
    rw [hρ₂]; simp
  let ψ₁ : ContinuousHom EU D' := ContinuousHom.comp hWw hBu e (ContinuousHom.comp hR hBu χ ρ₁)
  let ψ₂ : ContinuousHom EU D' := ContinuousHom.comp hWw hBu e (ContinuousHom.comp hR hBu χ ρ₂)
  have hyψ₁ : y₁ = formalSpectrumMap hBu ψ₁ ≫ eU.inv := by
    rw [hy₁def, hEdef, hptdef, Category.assoc, hρ₁', ← Category.assoc (formalSpectrumMap hR χ),
      formalSpectrumMap_comp_eq, ← Category.assoc, formalSpectrumMap_comp_eq]
  have hyψ₂ : y₂ = formalSpectrumMap hBu ψ₂ ≫ eU.inv := by
    rw [hy₂def, hEdef, hptdef, Category.assoc, hρ₂', ← Category.assoc (formalSpectrumMap hR χ),
      formalSpectrumMap_comp_eq, ← Category.assoc, formalSpectrumMap_comp_eq]
  have hμρ₁ := comp_eq_id_of_formalSpectrumMap_diagonal B S hS (a ≫ q) hBu hR eU eP μ hμ ρ₁ _
    (pullback.diagonal_fst _) hρ₁
  have hμρ₂ := comp_eq_id_of_formalSpectrumMap_diagonal B S hS (a ≫ q) hBu hR eU eP μ hμ ρ₂ _
    (pullback.diagonal_snd _) hρ₂
  have hdiff : ∀ b : Bu, ψ₁.toRingHom b - ψ₂.toRingHom b ∈ (adicStage hW'adic 0).1 := by
    intro b
    have hmem : ρ₁.toRingHom b - ρ₂.toRingHom b ∈ RingHom.ker μ.toRingHom := by
      rw [RingHom.mem_ker, map_sub]
      have h1 := congrArg (fun φ => φ b) hμρ₁
      have h2 := congrArg (fun φ => φ b) hμρ₂
      simp only [RingHom.comp_apply, RingHom.id_apply] at h1 h2
      rw [h1, h2, sub_self]
    have hloc : e.toRingHom (χ.toRingHom (ρ₁.toRingHom b - ρ₂.toRingHom b)) ∈
        IsLocalRing.maximalIdeal W' := by
      rw [he]
      exact map_nonunit (algebraMap W W') _ (hχ _ hmem)
    simpa [adicStage, ψ₁, ψ₂, map_sub] using hloc
  -- two lifts of `y₁` along the étale projection `U ×_{X'} U ⟶ U`
  have hfst : IsRepresentableEtale B S hS (pullback.fst a a) :=
    isRepresentableEtale_of_isPullback B S hS (IsPullback.of_hasPullback a a).flip ha
  have e₁ : pullback.lift y₁ y₂ (hy₁.trans hy₂.symm) ≫ pullback.fst a a = y₁ :=
    pullback.lift_fst _ _ _
  have e₂ : pullback.lift y₁ y₂ (hy₁.trans hy₂.symm) ≫ pullback.snd a a = y₂ :=
    pullback.lift_snd _ _ _
  have e₃ : pullback.diagonal a ≫ pullback.fst a a = 𝟙 U := pullback.diagonal_fst a
  have e₄ : pullback.diagonal a ≫ pullback.snd a a = 𝟙 U := pullback.diagonal_snd a
  have h₀ : formalSpectrumInclusion D' (OrderDual.toDual (adicStage hW'adic 0)) ≫
        pullback.lift y₁ y₂ (hy₁.trans hy₂.symm) =
      formalSpectrumInclusion D' (OrderDual.toDual (adicStage hW'adic 0)) ≫
        y₁ ≫ pullback.diagonal a := by
    have hst := formalSpectrumInclusion_comp_formalSpectrumMap_eq B S hS hBu ψ₁ ψ₂
      (adicStage hW'adic 0) hdiff
    have k₁ : (y₁ ≫ pullback.diagonal a) ≫ pullback.fst a a = y₁ :=
      (Category.assoc _ _ _).trans ((congrArg (y₁ ≫ ·) e₃).trans (Category.comp_id _))
    have k₂ : (y₁ ≫ pullback.diagonal a) ≫ pullback.snd a a = y₁ :=
      (Category.assoc _ _ _).trans ((congrArg (y₁ ≫ ·) e₄).trans (Category.comp_id _))
    have hst' : formalSpectrumInclusion D' (OrderDual.toDual (adicStage hW'adic 0)) ≫ y₂ =
        formalSpectrumInclusion D' (OrderDual.toDual (adicStage hW'adic 0)) ≫ y₁ := by
      rw [hyψ₁, hyψ₂]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ eU.inv) hst.symm).trans
        (Category.assoc _ _ _))
    refine pullback.hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (e₁.trans k₁.symm)).trans
        (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₂).trans (hst'.trans
        ((congrArg (_ ≫ ·) k₂.symm).trans (Category.assoc _ _ _).symm)))
  have hz := formalSpectrum_hom_eq_of_formallyEtale B S hS (pullback.fst a a)
    (formallyEtale_hom_of_isRepresentableEtale _ hfst) hW'adic D'
    (e₁.trans ((Category.assoc _ _ _).trans ((congrArg (y₁ ≫ ·) e₃).trans
      (Category.comp_id _))).symm) h₀
  have hy : y₂ = y₁ :=
    e₂.symm.trans ((congrArg (· ≫ pullback.snd a a) hz).trans
      ((Category.assoc _ _ _).trans ((congrArg (y₁ ≫ ·) e₄).trans (Category.comp_id _))))
  -- hence `E ≫ pt` factors through the diagonal, and `χ` through `μ`
  have hfac : E ≫ pt = y₁ ≫ pullback.diagonal (a ≫ q) := by
    have d₁ : pullback.diagonal (a ≫ q) ≫ pullback.fst (a ≫ q) (a ≫ q) = 𝟙 U :=
      pullback.diagonal_fst _
    have d₂ : pullback.diagonal (a ≫ q) ≫ pullback.snd (a ≫ q) (a ≫ q) = 𝟙 U :=
      pullback.diagonal_snd _
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, d₁, Category.comp_id, hy₁def]
    · rw [Category.assoc, Category.assoc, d₂, Category.comp_id, ← hy, hy₂def]
  have hΔ : eU.inv ≫ pullback.diagonal (a ≫ q) = formalSpectrumMap hR μ ≫ eP.inv := by
    rw [hμ]; simp
  have hψ : formalSpectrumMap hR (ContinuousHom.comp hWw hR e χ) =
      formalSpectrumMap hR (ContinuousHom.comp hBu hR ψ₁ μ) := by
    have h1 : E ≫ pt = formalSpectrumMap hR (ContinuousHom.comp hWw hR e χ) ≫ eP.inv := by
      rw [hEdef, hptdef, ← Category.assoc, formalSpectrumMap_comp_eq]
    have h2 : y₁ ≫ pullback.diagonal (a ≫ q) =
        formalSpectrumMap hR (ContinuousHom.comp hBu hR ψ₁ μ) ≫ eP.inv := by
      rw [hyψ₁, Category.assoc, hΔ, ← Category.assoc, formalSpectrumMap_comp_eq]
    have h3 := h1.symm.trans (hfac.trans h2)
    simpa using congrArg (fun k => k ≫ eP.hom) h3
  have hψeq := congrArg ContinuousHom.toRingHom
    (ContinuousHom.eq_of_formalSpectrumMap_eq B S hS hR hW'w hψ)
  intro y hy
  have h3 := congrArg (fun φ => φ y) hψeq
  simp only [ψ₁, ContinuousHom.comp_toRingHom, RingHom.comp_apply, RingHom.mem_ker.mp hy,
    map_zero] at h3
  rw [he] at h3
  exact (FaithfulSMul.algebraMap_injective W W') (by simpa using h3)

end KernelOfDiagonal


section FlatBaseChange

/-- **The chart maps of a flat morphism locally of finite type are flat, adic and topologically of
finite type**, over `WAdm^{Noeth}`. A chart map `t : U ⟶ V` over a morphism `f` locally of finite
type is locally of finite type (Stacks 0AQ4, 0AQ6), hence of finite type between affine formal
algebraic spaces, so its presenting homomorphism is taut and topologically of finite type
(Stacks 0AN5, 0ANV); tautness out of a Noetherian adic ring is adicness. Flatness of the chart
maps is Definition 0GCC. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_isFlatAdicOfFiniteTypeHom_of_isFlat
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hf : IsFlat B S hS f)
    (hft : IsLocallyOfFiniteType B S hS f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsNoetherianAdic
      IsFlatAdicOfFiniteTypeHom f := by
  have hP := (isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f).mp hf
  intro U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hA hRc hwa D E eU eV φ hφ
  refine ⟨hP U V a b t hU hV ha hb hsq A R hA hRc hwa D E eU eV φ hφ, ?_⟩
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
    have hrw : formalSpectrumMap hwa φ = eU.inv ≫ t ≫ eV.hom := by
      rw [hφ]; simp
    rw [hrw]
    exact IsLocallyOfFiniteType.comp B S hS eU.inv (t ≫ eV.hom)
      (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS eU.inv
        (isRepresentableEtale_of_isIso B S hS eU.inv))
      (IsLocallyOfFiniteType.comp B S hS t eV.hom htlft
        (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS eV.hom
          (isRepresentableEtale_of_isIso B S hS eV.hom)))
  obtain ⟨htaut, htft⟩ := isTaut_and_isTopologicallyOfFiniteType_of_isFiniteType_formalSpectrumMap
    B S hS hwa hRc.1.isWeaklyAdmissible D E φ htgt hsrc
    (IsLocallyOfFiniteType.isFiniteType_of_isAffineFormal B S hS _ hsrc htgt hmap)
  have hRw := hRc.1.isWeaklyAdmissible
  have : IsNoetherianRing A := hA.2
  obtain ⟨⟨I, -, hI⟩, -⟩ := hA.1
  let _ : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  have : CompleteSpace R := hRc.1.2.2
  have : T2Space R := hRc.1.2.1
  exact ⟨RingHom.isAdic_of_isTaut φ.toRingHom φ.continuous htaut
    ⟨I, IsNoetherian.noetherian I, hI⟩, htft⟩

/-- **Stacks 0GCE, part (2), flatness, through the chart conditions above.** A base change of a
flat morphism locally of finite type of locally Noetherian formal algebraic spaces is flat. -/
theorem isFlat_pullback_snd_of_isLocallyNoetherian_of_isFlat {X Y Z : FppfSheaf B S hS}
    (f : X ⟶ Y) (g : Z ⟶ Y) (hX : IsLocallyNoetherian B S hS X)
    (hY : IsLocallyNoetherian B S hS Y) (hZ : IsLocallyNoetherian B S hS Z)
    (hf : IsFlat B S hS f) (hft : IsLocallyOfFiniteType B S hS f) :
    IsFlat B S hS (pullback.snd f g) := by
  have h := (conditions_pullback_snd_of_isStableUnderBaseChangeNoetherian B S hS
    IsFlatAdicOfFiniteTypeHom TopologicalRing.flatAdicFiniteType_isStableUnderBaseChange
    isFlatAdicOfFiniteTypeHom_isomorphismInvariant f g hX hY hZ
    (hasPropertyOnEveryAffineEtaleDiagram_isFlatAdicOfFiniteTypeHom_of_isFlat B S hS f hf hft)).1
  refine (isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS _).mpr ?_
  intro U V a b t hU hV ha hb hsq A R _ _ _ _ _ _ _ _ hA hR hwa D E eU eV φ hφ
  exact (h U V a b t hU hV ha hb hsq A R hA hR hwa D E eU eV φ hφ).1

end FlatBaseChange

section FlatCharts

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [IsNoetherianRing A] (D : QuotientSystem B S hS A)

/-- **The ring of a fibre product of charts of a flat space is flat over the base.** Let
`q : X' ⟶ Spf A` be flat and locally of finite type with `X'` locally Noetherian, and let
`a : U ⟶ X'`, `b : V ⟶ X'` be affine representable étale charts. If `U ×_{Spf A} V` is
presented as `Spf R` with `R` Noetherian adic, then the homomorphism `A → R` presenting its
structure morphism is flat: the structure morphism is the composite of the base change of the
flat morphism `U ⟶ Spf A` (Stacks 0GCE) with the flat morphism `V ⟶ Spf A` (Stacks 0GCF). -/
theorem flat_of_isPullback_charts (hA : TopologicalRing.IsAdic A) {X' U V : FppfSheaf B S hS}
    (q : X' ⟶ formalSpectrum D) (hX' : IsLocallyNoetherian B S hS X')
    (hq : IsLocallyOfFiniteType B S hS q) (hqflat : IsFlat B S hS q) {a : U ⟶ X'}
    {b : V ⟶ X'} (hU : IsAffineFormalAlgebraicSpace B S hS U)
    (hV : IsAffineFormalAlgebraicSpace B S hS V) (ha : IsRepresentableEtale B S hS a)
    (hb : IsRepresentableEtale B S hS b) {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] [IsNoetherianRing R]
    (hR : TopologicalRing.IsAdic R) (EP : QuotientSystem B S hS R)
    (eP : pullback (a ≫ q) (b ≫ q) ≅ formalSpectrum EP) (c : ContinuousHom D EP)
    (hc : formalSpectrumMap hA.isWeaklyAdmissible c =
      eP.inv ≫ pullback.snd (a ≫ q) (b ≫ q) ≫ b ≫ q) :
    c.toRingHom.Flat := by
  obtain ⟨-, hPloc, -⟩ := isAffine_and_isNoetherian_pullback_charts B S hS D hA q hX' hq hU hV
    ha hb
  have hSpf := isLocallyNoetherian_formalSpectrum B S hS hA D
  have hUl := isLocallyNoetherian_of_isAffine_of_isNoetherian B S hS hU
    (isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hX' a hU ha)
  have hVl := isLocallyNoetherian_of_isAffine_of_isNoetherian B S hS hV
    (isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS hX' b hV hb)
  have haq : IsFlat B S hS (a ≫ q) := isFlat_comp_of_isRepresentableEtale B S hS ha hqflat
  have hbq : IsFlat B S hS (b ≫ q) := isFlat_comp_of_isRepresentableEtale B S hS hb hqflat
  have haql : IsLocallyOfFiniteType B S hS (a ≫ q) := IsLocallyOfFiniteType.comp B S hS a q
    (IsLocallyOfFiniteType.of_isRepresentableEtale B S hS a ha) hq
  have hsnd := isFlat_pullback_snd_of_isLocallyNoetherian_of_isFlat B S hS (a ≫ q) (b ≫ q) hUl
    hSpf hVl haq haql
  have hf := isFlat_comp_of_isLocallyNoetherian _ _ hPloc hVl hSpf hsnd hbq
  have hEPaff := isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic B S hS hR EP
    (Iso.refl _)
  have hDaff := isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic B S hS hA D
    (Iso.refl _)
  obtain ⟨hrep, het⟩ := isRepresentableEtale_of_isIso B S hS eP.inv
  obtain ⟨hrep', het'⟩ := isRepresentableEtale_id B S hS (formalSpectrum D)
  exact hf (formalSpectrum EP) (formalSpectrum D) hEPaff hDaff eP.inv (𝟙 _)
    (eP.inv ≫ pullback.snd (a ≫ q) (b ≫ q) ≫ b ≫ q) hrep hrep' het het' (by simp) A R hA hR
    hA.isWeaklyAdmissible D EP (Iso.refl _) (Iso.refl _) c (by simp [hc])

end FlatCharts

section IdempotentKernel

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsLinearTopology A A] (D : QuotientSystem B S hS A)

/-- **The diagonal of a chart of a flat space with rig-étale rig-surjective diagonal is open and
closed.** Let `A` be a discrete valuation ring with its maximal-adic topology, complete, and let
`q : X' ⟶ Spf A` be flat and locally of finite type, with `X'` locally Noetherian and relative
diagonal rig-étale and rig-surjective. Let `a : U ⟶ X'` be an affine representable étale chart
with `U = Spf Bu` and `U ×_{Spf A} U = Spf R`, and let `μ : R → Bu` present the diagonal of
`U` over `A`, with `ρ₁, ρ₂ : Bu → R` presenting the two projections. Then the kernel `J` of `μ`
is idempotent.

The ring `R` is Noetherian and flat over `A`, so a uniformizer `π` of `A` is a nonzerodivisor of
`R` and avoids its minimal primes. The diagonal of `U` is a base change of the diagonal of `X'`
along a chart, so it is rig-étale: `π ^ N J ⊆ J ^ 2` by Stacks 0GD4 on one chart. And for primes
`𝔮 ⊆ 𝔪` of `R` with `π ∉ 𝔮` and `J ⊆ 𝔪` maximal, an adic point of `Spf R` out of a complete
discrete valuation ring with kernel `𝔮` and closed point `𝔪` reduces into the diagonal, so it
kills `J` by rig-surjectivity of the diagonal of `X'`, whence `J ⊆ 𝔮`. These are the two
hypotheses of `Ideal.isIdempotentElem_of_span_pow_mul_le_sq`. -/
theorem isIdempotentElem_ker_of_isRigEtale_of_isRigSurjective_diagonal
    (hAadic : _root_.IsAdic (IsLocalRing.maximalIdeal A))
    (hAc : IsAdicComplete (IsLocalRing.maximalIdeal A) A) {X' U : FppfSheaf B S hS}
    (q : X' ⟶ formalSpectrum D) (hX' : IsLocallyNoetherian B S hS X')
    (hq : IsLocallyOfFiniteType B S hS q) (hqflat : IsFlat B S hS q)
    (hdiagE : IsRigEtale B S hS (pullback.diagonal q))
    (hdiagS : IsRigSurjective B S hS (pullback.diagonal q)) (a : U ⟶ X')
    (hU : IsAffineFormalAlgebraicSpace B S hS U) (ha : IsRepresentableEtale B S hS a)
    {Bu R : Type u} [CommRing Bu] [TopologicalSpace Bu] [IsTopologicalRing Bu]
    [IsLinearTopology Bu Bu] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R] (hBu : TopologicalRing.IsNoetherianAdic Bu)
    (hR : TopologicalRing.IsNoetherianAdic R)
    {EU : QuotientSystem B S hS Bu} {EP : QuotientSystem B S hS R}
    (eU : U ≅ formalSpectrum EU) (eP : pullback (a ≫ q) (a ≫ q) ≅ formalSpectrum EP)
    (μ : ContinuousHom EP EU)
    (hμ : formalSpectrumMap hR.1.isWeaklyAdmissible μ =
      eU.inv ≫ pullback.diagonal (a ≫ q) ≫ eP.hom)
    (ρ₁ ρ₂ : ContinuousHom EU EP)
    (hρ₁ : formalSpectrumMap hBu.1.isWeaklyAdmissible ρ₁ =
      eP.inv ≫ pullback.fst (a ≫ q) (a ≫ q) ≫ eU.hom)
    (hρ₂ : formalSpectrumMap hBu.1.isWeaklyAdmissible ρ₂ =
      eP.inv ≫ pullback.snd (a ≫ q) (a ≫ q) ≫ eU.hom) :
    IsIdempotentElem (RingHom.ker μ.toRingHom) := by
  classical
  have _ : IsNoetherianRing R := hR.2
  have _ : IsNoetherianRing Bu := hBu.2
  have hAN : TopologicalRing.IsAdic A :=
    topologicalRingIsAdic_of_isAdic_of_isAdicComplete hAadic hAc
  have hAw := hAN.isWeaklyAdmissible
  have hRw := hR.1.isWeaklyAdmissible
  have hBuw := hBu.1.isWeaklyAdmissible
  -- the structure homomorphism `A → R`, which is flat
  obtain ⟨c, hc, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hAw hRw
    (eP.inv ≫ pullback.snd (a ≫ q) (a ≫ q) ≫ a ≫ q)
  have hcflat := flat_of_isPullback_charts B S hS D hAN q hX' hq hqflat hU hU ha ha hR.1 EP eP c
    hc
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  set π : R := c.toRingHom ϖ with hπdef
  have hπreg : π ∈ nonZeroDivisors R := by
    let _ : Algebra A R := c.toRingHom.toAlgebra
    have _ : Module.Flat A R := hcflat
    have hreg : IsSMulRegular R ϖ :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
    refine mem_nonZeroDivisors_iff_right.mpr fun x hx => hreg ?_
    show ϖ • x = ϖ • 0
    rw [smul_zero, Algebra.smul_def]
    exact (mul_comm _ _).trans hx
  -- powers of `π` enter every open ideal of `R`
  have hπpow : ∀ I : Ideal R, IsOpen (I : Set R) → ∃ N, π ^ N ∈ I := by
    intro I hI
    have hopen : IsOpen (c.toRingHom ⁻¹' (I : Set R)) := hI.preimage c.continuous
    obtain ⟨N, hN⟩ := (isAdic_iff.mp hAadic).2 _ (hopen.mem_nhds (by simp))
    refine ⟨N, ?_⟩
    have hmem : ϖ ^ N ∈ IsLocalRing.maximalIdeal A ^ N :=
      Ideal.pow_mem_pow ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ ▸
        Ideal.mem_span_singleton_self ϖ) N
    simpa [hπdef, map_pow] using hN hmem
  -- the chart square of the diagonal
  obtain ⟨bm, hbmdef⟩ : ∃ bm : pullback (a ≫ q) (a ≫ q) ⟶ pullback q q,
      bm = pullback.map (a ≫ q) (a ≫ q) q q a a (𝟙 _) (by simp) (by simp) := ⟨_, rfl⟩
  have hbm : IsRepresentableEtale B S hS bm := by
    rw [hbmdef]; exact isRepresentableEtale_pullback_map B S hS q q ha ha
  have hsq : a ≫ pullback.diagonal q = pullback.diagonal (a ≫ q) ≫ bm := by
    rw [hbmdef]
    refine pullback.hom_ext ?_ ?_ <;> simp
  obtain ⟨hPaff, -, -⟩ := isAffine_and_isNoetherian_pullback_charts B S hS D hAN q hX' hq hU hU
    ha ha
  have hre := hdiagE U (pullback (a ≫ q) (a ≫ q)) hU hPaff a bm (pullback.diagonal (a ≫ q))
    ha.1 hbm.1 ha.2 hbm.2 hsq R Bu hR.1 hBu.1 hRw EP EU eU eP μ (by rw [hμ]; simp)
  -- `μ` is split by `ρ₁`, hence surjective
  have hμρ₁ := comp_eq_id_of_formalSpectrumMap_diagonal B S hS (a ≫ q) hBuw hRw eU eP μ hμ ρ₁ _
    (pullback.diagonal_fst _) hρ₁
  have hsurj : Function.Surjective μ.toRingHom := fun b =>
    ⟨ρ₁.toRingHom b, by simpa using congrArg (fun φ => φ b) hμρ₁⟩
  obtain ⟨I, hI, hIJ⟩ := exists_isIdealOfDefinition_mul_ker_le_sq_of_isRigEtale hR.1 hBu.1
    μ.toRingHom μ.continuous hsurj hre
  obtain ⟨N, hN⟩ := hπpow I hI.1
  have hNJ : Ideal.span {π ^ N} * RingHom.ker μ.toRingHom ≤ RingHom.ker μ.toRingHom ^ 2 :=
    (Ideal.mul_mono_left ((Ideal.span_singleton_le_iff_mem I).mpr hN)).trans hIJ
  refine Ideal.isIdempotentElem_of_span_pow_mul_le_sq hπreg hNJ ?_
  intro q' m hq' hm hq'm hJm hπq'
  obtain ⟨I₀, hI₀def, -, hI₀c⟩ := exists_idealOfDefinition_isAdicComplete hR.1
  have _ : IsAdicComplete I₀ R := hI₀c
  have hI₀m : I₀ ≤ m := (IsAdicComplete.le_jacobson_bot I₀).trans
    (sInf_le ⟨bot_le, hm⟩)
  have hq'I₀ : ¬ I₀ ≤ q' := fun hle => by
    obtain ⟨N₀, hN₀⟩ := hπpow I₀ hI₀def.1
    exact hπq' (hq'.mem_of_pow_mem N₀ (hle hN₀))
  have _ : m.IsPrime := hm.isPrime
  obtain ⟨W, _, _, _, _, _, _, hWadic, hWc, hWw, DW, χ, hker, hcomap, hrep⟩ :=
    exists_adic_completeDvr_point_of_le_isPrime B S hS hR.1 EP hq'm hI₀def hI₀m hq'I₀
  have hχ0 := map_eq_zero_of_mem_ker_of_isRigSurjective_diagonal B S hS D q a ha hdiagS hBuw hRw
    eU eP μ hμ ρ₁ ρ₂ hρ₁ hρ₂ W hWadic hWc hWw DW χ hrep fun x hx =>
      show x ∈ (IsLocalRing.maximalIdeal W).comap χ.toRingHom from hcomap ▸ hJm hx
  rw [← hker]
  exact fun x hx => hχ0 x hx

end IdempotentKernel

end AlgebraicGeometry.FormalSpace

end
