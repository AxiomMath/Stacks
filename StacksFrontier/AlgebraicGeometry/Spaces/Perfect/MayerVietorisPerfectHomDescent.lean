module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictedPerfectHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelMayerVietoris
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.StageHomSystemLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectBiprod

/-!
# The Mayer–Vietoris step for the descent of morphisms of perfect objects

In the proof of Stacks 09RI the full faithfulness of the pullback to the limit on perfect objects
is carried through the induction principle of Stacks 08GP over the quasi-compact quasi-separated
algebraic spaces `W₀` over the chosen stage `X₀`. The induction step is an elementary
distinguished square `(U ⊆ W₀, f : V₀ ⟶ W₀)` with intersection `P₀ = U ×_{W₀} V₀`: if morphisms of
perfect objects descend in the restrictions of the situation to `U`, `V₀` and `P₀`, they descend
in its restriction to `W₀`.

At a stage `i`, the square base changes to an elementary distinguished square of `Wᵢ` (Stacks
08GN), whose Mayer–Vietoris triangle (Stacks 08GV) on the models of the spaces-étale sites is
`j_{P!}Lj_P^*E ⟶ j_{U!}Lj_U^*E ⊞ j_{V!}Lj_V^*E ⟶ E ⟶`. The groups of morphisms out of the
extensions by zero along the later stages are those of the restrictions to the pieces
(`AlgebraicGeometry.Space.DescentSituation.stageHomSystem_isColimitAt_lowerShriek`), hence filtered
colimits; so are those out of their biproducts and shifts, and the five lemma on directed colimits
(`Stacks.StageHomSystem.IsColimitAt.of_distTriang`) gives the filtered colimit statement for `E`.

## Main results

In the namespace `AlgebraicGeometry.Space.DescentSituation`:

* `perfectHomsDescend_restrictTo_of_isElementaryDistinguishedSquare`: for an elementary
  distinguished square `(U ⊆ W₀, f : V₀ ⟶ W₀)`, if morphisms of perfect objects descend in the
  restrictions to `U`, `V₀` and `U ×_{W₀} V₀`, they descend in the restriction to `W₀`.

## References

* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi

universe u

namespace AlgebraicGeometry.Space.DescentSituation

attribute [local instance high] HasDerivedCategory.standard
attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : DescentSituation B S hS hZ I)

/-- **The Mayer–Vietoris step of the descent of morphisms of perfect objects** (proof of Stacks
09RI, induction of Stacks 08GP). For an elementary distinguished square `(U ⊆ W₀, f : V₀ ⟶ W₀)`
of quasi-compact quasi-separated algebraic spaces over the chosen stage, if morphisms of perfect
objects descend in the restrictions of `D` to `U`, `V₀` and `U ×_{W₀} V₀`, they descend in its
restriction to `W₀`. -/
theorem perfectHomsDescend_restrictTo_of_isElementaryDistinguishedSquare
    {W₀ V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW₀ : IsAlgebraicSpace B S hS W₀)
    (hW₀qc : IsQuasiCompactSpace B S hS W₀) (hW₀qs : IsAbsolutelyQuasiSeparated B S hS hZ W₀)
    (w : W₀ ⟶ D.system.obj (op D.base)) (U : Subfunctor W₀) (f : V₀ ⟶ W₀)
    (hsq : IsElementaryDistinguishedSquare B S hS hW₀ U f)
    (hU : IsAlgebraicSpace B S hS U.toFunctor) (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.toFunctor)
    (hVqc : IsQuasiCompactSpace B S hS V₀) (hVqs : IsAbsolutelyQuasiSeparated B S hS hZ V₀)
    (hP : IsAlgebraicSpace B S hS (pullback U.ι f))
    (hPqc : IsQuasiCompactSpace B S hS (pullback U.ι f))
    (hPqs : IsAbsolutelyQuasiSeparated B S hS hZ (pullback U.ι f))
    (hFFU : (D.restrictTo hU hUqc hUqs (U.ι ≫ w)).PerfectHomsDescend)
    (hFFV : (D.restrictTo hsq.isAlgebraicSpace hVqc hVqs (f ≫ w)).PerfectHomsDescend)
    (hFFP : (D.restrictTo hP hPqc hPqs (pullback.fst U.ι f ≫ U.ι ≫ w)).PerfectHomsDescend) :
    (D.restrictTo hW₀ hW₀qc hW₀qs w).PerfectHomsDescend := by
  refine perfectHomsDescend_of_isStagesColimit _ fun i _ E K hE hK => ?_
  refine (stageHomSystem_isColimitAt_iff _ E K).1 ?_
  have := isDirected_laterStages D
  have : IsDirected {k // i ≤ k} (· ≤ ·) := ⟨fun a b => by
    obtain ⟨c, h₁, h₂⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨c, a.2.trans h₁⟩, h₁, h₂⟩⟩
  have : ∀ k, ((D.restrictTo hW₀ hW₀qc hW₀qs w).stagePullbackFunctor i k).IsTriangulated :=
    fun k => isTriangulated_derivedPullback _ (isMorphismOfSites_spacesEtaleModelHom B S hS _)
  have : ((D.restrictTo hW₀ hW₀qc hW₀qs w).limitPullbackFunctor i).IsTriangulated :=
    isTriangulated_derivedPullback _ (isMorphismOfSites_spacesEtaleModelHom B S hS _)
  let p : (D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op i) ⟶ W₀ :=
    pullback.snd (D.system.map (homOfLE i.2).op) w
  have hsqi := isElementaryDistinguishedSquare_preimage B S hS hW₀
    ((D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace i) U f hsq p
  have hWsq : IsElementaryDistinguishedSquare B S hS
      (⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op i),
        (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace i⟩ : AlgebraicSpaces B S hS).2
      (U.preimage p) (pullback.snd f p) := hsqi
  have hW₀sq : IsElementaryDistinguishedSquare B S hS
      (⟨W₀, hW₀⟩ : AlgebraicSpaces B S hS).2 U f := hsq
  obtain ⟨m₁, m₂, m₃, hT⟩ := exists_mem_distTriang_spacesEtaleModelMayerVietoris B S hS hWsq E
  have hUe := isEtale_edsOpenHom B S hS (W := ⟨W₀, hW₀⟩) hW₀sq
  have hPe := isEtale_edsInterHom B S hS (W := ⟨W₀, hW₀⟩) hW₀sq
  -- the three pieces
  have hGU := D.stageHomSystem_isColimitAt_lowerShriek hW₀ hW₀qc hW₀qs w hU hUqc hUqs U.ι i
    (edsOpenHom B S hS hWsq) (U.fromPreimage p) (Subfunctor.isPullback_preimage p U).flip hFFU
    hUe (isEtale_edsOpenHom B S hS hWsq)
  have hGV := D.stageHomSystem_isColimitAt_lowerShriek hW₀ hW₀qc hW₀qs w hsq.isAlgebraicSpace hVqc
    hVqs f i (edsEtaleHom B S hS hWsq) (pullback.fst f p) (IsPullback.of_hasPullback f p).flip hFFV
    hsq.isEtale (isEtale_edsEtaleHom B S hS hWsq)
  have hGP := D.stageHomSystem_isColimitAt_lowerShriek hW₀ hW₀qc hW₀qs w hP hPqc hPqs
    (pullback.fst U.ι f ≫ U.ι) i (edsInterHom B S hS hWsq) _
    (isPullback_preimage_inter B S hS U f p) hFFP hPe (isEtale_edsInterHom B S hS hWsq)
  have hpb : ∀ {Y : AlgebraicSpaces B S hS}
      (g : Y ⟶ ⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op i),
        (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace i⟩),
      (spacesEtaleModelRingedSite B S hS Y).IsPerfect
        ((derivedPullback (spacesEtaleModelHom B S hS g)).obj E) :=
    fun g => isPerfect_derivedPullback_spacesEtaleModelHom g E hE
  have hsh : ∀ {Y : AlgebraicSpaces B S hS}
      (g : Y ⟶ ⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op i),
        (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace i⟩),
      (spacesEtaleModelRingedSite B S hS Y).IsPerfect
        (((derivedPullback (spacesEtaleModelHom B S hS g)).obj E)⟦(1 : ℤ)⟧) :=
    fun g => RingedSite.isPerfect_shift_general_of_hasDerivedCategory _ _ (hpb g) 1
  -- the shift of an extension by zero is the extension by zero of the shift
  have eSh : ∀ {Y : AlgebraicSpaces B S hS}
      (g : Y ⟶ ⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op i),
        (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace i⟩) (hg : IsEtale B S hS g.hom)
      (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleModelRingedTopos B S hS Y).O))),
      (spacesEtaleModelDerivedLowerShriek B S hS g hg).obj (A⟦(1 : ℤ)⟧) ≅
        ((spacesEtaleModelDerivedLowerShriek B S hS g hg).obj A)⟦(1 : ℤ)⟧ := fun g hg A => by
    let := (spacesEtaleModelDerivedLowerShriekAdjunction B S hS g hg).leftAdjointCommShift ℤ
    exact ((spacesEtaleModelDerivedLowerShriek B S hS g hg).commShiftIso (1 : ℤ)).app A
  have := preservesBinaryBiproducts_of_preservesBiproducts
    (shiftFunctor (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (spacesEtaleModelRingedTopos B S hS ⟨(D.restrictTo hW₀ hW₀qc hW₀qs w).system.obj (op i),
        (D.restrictTo hW₀ hW₀qc hW₀qs w).algebraicSpace i⟩).O))) (1 : ℤ))
  exact Stacks.StageHomSystem.IsColimitAt.of_distTriang _ (Triangle.mk m₁ m₂ m₃) hT K
    (Stacks.StageHomSystem.IsColimitAt.biprod _ (hGU _ (hpb _) K hK) (hGV _ (hpb _) K hK))
    (Stacks.StageHomSystem.IsColimitAt.of_iso _ (eSh _ _ _) (hGP _ (hsh _) K hK))
    (Stacks.StageHomSystem.IsColimitAt.of_iso _
      (biprod.mapIso (eSh _ _ _) (eSh _ _ _) ≪≫ ((shiftFunctor _ (1 : ℤ)).mapBiprod _ _).symm)
      (Stacks.StageHomSystem.IsColimitAt.biprod _ (hGU _ (hsh _) K hK) (hGV _ (hsh _) K hK)))
    (hGP _ (hpb _) K hK)

end AlgebraicGeometry.Space.DescentSituation
