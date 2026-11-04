module

public import StacksFrontier.AlgebraicGeometry.Blowup.PerfectHomomorphism
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingPerfectPullback
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.IntegralPerfectComplex
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FinitePresentationDegreeMinusOne
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension

/-!
# Stacks tag 0ESV through the Fitting blowup of the cokernel

Let `X` be a scheme and `φ : ℱ ⟶ 𝒢` a homomorphism of perfect `𝒪_X`-modules of Tor dimension at
most one which vanish on a scheme-theoretically dense open `U ⊆ X`. Stacks tag 0ESV: there is a
`U`-admissible blowup `b : X' ⟶ X` after which the kernel, the image and the cokernel of `b^*φ`
are again perfect `𝒪_{X'}`-modules of Tor dimension at most one.

The cone `E` of `φ[0]` is concentrated in degrees `-1` and `0` and has `Coker(φ)` for its `H^0`,
so the blowup needed is the one tag 0ESN supplies for the single module `Coker(φ)`. That module
is finitely presented, because `E` is perfect hence pseudo-coherent and has no cohomology above
degree `0` (tag 08DN (2)), and it vanishes over `U`. Tag 0ESS keeps `b^*ℱ` and `b^*𝒢` perfect of
Tor dimension at most one, and the image and the kernel follow from the two short exact sequences
`0 ⟶ Im(b^*φ) ⟶ b^*𝒢 ⟶ Coker(b^*φ) ⟶ 0` and `0 ⟶ Ker(b^*φ) ⟶ b^*ℱ ⟶ Im(b^*φ) ⟶ 0` by tag 08CR
and tag 08CJ.

## Main results

* `AlgebraicGeometry.exists_admissibleBlowup_isPerfectTorLEOne_ker_im_coker` is Stacks tag 0ESV.
* `AlgebraicGeometry.isPerfectTorLEOne_abelianImage_of_cokernel` and
  `AlgebraicGeometry.isPerfectTorLEOne_kernel`: the image of a homomorphism is perfect of Tor
  dimension at most one once its target and its cokernel are, and then the kernel is once the
  source and the image are.
* `AlgebraicGeometry.isZero_homology_derTensor_single_single`: the derived tensor product of two
  modules placed in degree zero has no cohomology in positive degrees.

## References

* [Stacks Project, Tag 0ESV](https://stacks.math.columbia.edu/tag/0ESV)
* [Stacks Project, Tag 0ESN](https://stacks.math.columbia.edu/tag/0ESN)
* [Stacks Project, Tag 0ESS](https://stacks.math.columbia.edu/tag/0ESS)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
* [Stacks Project, Tag 08DN](https://stacks.math.columbia.edu/tag/08DN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open StrictlyPerfect RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-! ### The image and the kernel -/

/-- **The derived tensor product of two modules placed in degree zero has no cohomology in
positive degrees.** Both factors lie in `D^{≤ 0}` and the derived tensor product of two objects
of `D^{≤ 0}` lies in `D^{≤ 0}`.

For a module placed in degree zero the upper end of the Tor-amplitude condition is therefore
automatic, and only the vanishing below the lower end has to be proved. -/
theorem isZero_homology_derTensor_single_single {Y : RingedSpace.{u, u}}
    (M N : OXMod.{u, u} Y) (i : ℤ) (hi : 0 < i) :
    IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) i).obj
      (((Stacks.Cohomology.TorAmplitude.derTensor Y).tensor.obj
          ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj M)).obj
        ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj N))) := by
  have hM : ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj M).IsLE 0 :=
    (DerivedCategory.isLE_iff _ 0).2 fun j hj =>
      RingedSpace.isZero_homology_singleFunctor_zero_of_ne_zero M j (by omega)
  have hN : ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj N).IsLE 0 :=
    (DerivedCategory.isLE_iff _ 0).2 fun j hj =>
      RingedSpace.isZero_homology_singleFunctor_zero_of_ne_zero N j (by omega)
  have key : ∀ K' L' : Stacks.DerivedTensor.RingedSite.DerivedModules Y.sheaf,
      K'.IsLE 0 → L'.IsLE 0 →
      (((Stacks.Cohomology.TorAmplitude.derTensor Y).tensor.obj K').obj L').IsLE (0 + 0) := by
    intro K' L' h1 h2
    let := h1
    let := h2
    exact Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct Y.sheaf _ K' L' 0 0
  have h := key _ _ hM hN
  rw [zero_add] at h
  exact (DerivedCategory.isLE_iff _ 0).1 h i hi

/-- The kernel of an epimorphism of `𝒪_Y`-modules is perfect of Tor dimension at most one as soon
as its source and target are. -/
private theorem isPerfectTorLEOne_kernel_of_epi {Y : Scheme.{u}}
    {B C : OXMod.{u, u} Y.toRingedSpace} (f : B ⟶ C) [Epi f] (hB : IsPerfectTorLEOne Y B)
    (hC : IsPerfectTorLEOne Y C) : IsPerfectTorLEOne Y (kernel f) := by
  have hT : (ShortComplex.kernelSequence f).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact f
      epi_g := by dsimp only [ShortComplex.kernelSequence]; infer_instance }
  refine ⟨Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₁_of_distinguished
    hT.singleTriangle hT.singleTriangle_distinguished hB.1 hC.1, ?_⟩
  intro N i hi
  -- `- ⊗^L 𝒩[0]`, named at the spelling in which the triangle lives.
  let A : DerivedCategory (OXMod.{u, u} Y.toRingedSpace) ⥤
      DerivedCategory (OXMod.{u, u} Y.toRingedSpace) :=
    (Stacks.Cohomology.TorAmplitude.derTensor Y.toRingedSpace).tensor.flip.obj
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y.toRingedSpace) 0).obj N)
  let hcs : A.CommShift ℤ :=
    (Stacks.Cohomology.TorAmplitude.derTensor Y.toRingedSpace).commShift_left _
  let hit : A.IsTriangulated :=
    (Stacks.Cohomology.TorAmplitude.derTensor Y.toRingedSpace).exact_left _
  by_cases hn : i < -1
  · have hd : A.mapTriangle.obj hT.singleTriangle ∈ distinguishedTriangles :=
      A.map_distinguished _ hT.singleTriangle_distinguished
    refine (DerivedCategory.HomologySequence.exact₁ _ hd (i - 1) i (by omega)).isZero_X₂ ?_ ?_
    · exact (hC.2 N (i - 1) (by simp only [Set.mem_Icc]; omega)).eq_of_src _ _
    · exact (hB.2 N i (by simp only [Set.mem_Icc]; omega)).eq_of_tgt _ _
  · have hp : 0 < i := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hi
      omega
    exact isZero_homology_derTensor_single_single _ N i hp

/-- **The last sentence of the proof of Stacks tag 0ESV.** The image of a homomorphism
`φ : ℱ ⟶ 𝒢` of `𝒪_Y`-modules is perfect of Tor dimension at most one as soon as `𝒢` and the
cokernel of `φ` are.

This is Stacks tag 08CR and the Tor amplitude of the short exact sequence
`0 ⟶ Im(φ) ⟶ 𝒢 ⟶ Coker(φ) ⟶ 0`, the image being the kernel of the cokernel. -/
theorem isPerfectTorLEOne_abelianImage_of_cokernel {Y : Scheme.{u}}
    {F G : OXMod.{u, u} Y.toRingedSpace}
    (φ : F ⟶ G) (hG : IsPerfectTorLEOne Y G) (hC : IsPerfectTorLEOne Y (cokernel φ)) :
    IsPerfectTorLEOne Y (Abelian.image φ) :=
  isPerfectTorLEOne_kernel_of_epi (cokernel.π φ) hG hC

/-- **The kernel.** The kernel of a homomorphism `φ : ℱ ⟶ 𝒢` of `𝒪_Y`-modules is perfect of Tor
dimension at most one as soon as `ℱ` and the image of `φ` are.

This is Stacks tag 08CR and the Tor amplitude of the short exact sequence
`0 ⟶ Ker(φ) ⟶ ℱ ⟶ Im(φ) ⟶ 0`. -/
theorem isPerfectTorLEOne_kernel {Y : Scheme.{u}} {F G : OXMod.{u, u} Y.toRingedSpace}
    (φ : F ⟶ G) (hF : IsPerfectTorLEOne Y F) (hI : IsPerfectTorLEOne Y (Abelian.image φ)) :
    IsPerfectTorLEOne Y (kernel φ) :=
  (isPerfectTorLEOne_kernel_of_epi (Abelian.factorThruImage φ) hF hI).of_iso
    ((kernelCompMono (Abelian.factorThruImage φ) (Abelian.image.ι φ)).symm ≪≫
      kernel.mapIso _ φ (Iso.refl _) (Iso.refl _) (by simp))

/-! ### Stacks tag 0ESV -/

/-- **Stacks Project, Tag 0ESV.** Let `X` be a scheme and `φ : ℱ ⟶ 𝒢` a homomorphism of perfect
`𝒪_X`-modules of Tor dimension at most one. Let `U ⊆ X` be a scheme-theoretically dense open with
`ℱ|_U = 0` and `𝒢|_U = 0`. Then there is a `U`-admissible blowup `b : X' ⟶ X` such that the
kernel, the image and the cokernel of `b^*φ` are perfect `𝒪_{X'}`-modules of Tor dimension at
most one.

The blowup is the blowup of `X` in the zeroth Fitting ideal of `Coker(φ)`. That cokernel is
finitely presented: it is the `H^0` of the cone `E` of `φ[0]` — the source's object `(ℱ ⟶ 𝒢)` of
`D(𝒪_X)`, which is perfect by tag 08CR and hence pseudo-coherent — and `E` has no cohomology in
positive degrees, so tag 08DN (2) applies. It vanishes over `U` because `ℱ` and `𝒢` do and
pullback is right exact, hence is finite locally free of rank `0` there. Tag 0ESN (1) therefore
makes the blowup `U`-admissible and tag 0ESN (4) makes `b^*Coker(φ)` perfect of Tor dimension at
most one; right exactness of pullback identifies that module with the cokernel of `b^*φ`. The
pullbacks `b^*ℱ` and `b^*𝒢` are perfect of Tor dimension at most one by tag 0ESS, after which the
image — the source's "kernel of the cokernel" — and then the kernel are
`AlgebraicGeometry.isPerfectTorLEOne_abelianImage_of_cokernel` and
`AlgebraicGeometry.isPerfectTorLEOne_kernel`. -/
@[stacks 0ESV "the U-admissible blowup after which the kernel, image and cokernel of the \
pullback of φ are perfect of Tor dimension ≤ 1"]
theorem exists_admissibleBlowup_isPerfectTorLEOne_ker_im_coker {X : Scheme.{u}}
    (F G : OXMod.{u, u} X.toRingedSpace) (φ : F ⟶ G)
    (hF : IsPerfectTorLEOne X F) (hG : IsPerfectTorLEOne X G)
    (U : X.Opens) (hU : Scheme.Opens.IsSchemeTheoreticallyDense U)
    (_hFU : IsZero ((modulePullback U.ι.toLRSHom.toShHom).obj F))
    (hGU : IsZero ((modulePullback U.ι.toLRSHom.toShHom).obj G)) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X), Stacks.Blowup.IsAdmissibleBlowup U b ∧
      IsPerfectTorLEOne X' (kernel ((modulePullback b.toLRSHom.toShHom).map φ)) ∧
      IsPerfectTorLEOne X' (Abelian.image ((modulePullback b.toLRSHom.toShHom).map φ)) ∧
      IsPerfectTorLEOne X' (cokernel ((modulePullback b.toLRSHom.toShHom).map φ)) := by
  -- The source's object `(ℱ ⟶ 𝒢)` of `D(𝒪_X)`: the cone of `φ[0]`.
  obtain ⟨E, g₀, h₀, hT⟩ := distinguished_cocone_triangle
    ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).map φ)
  let T := Triangle.mk
    ((DerivedCategory.singleFunctor (OXMod.{u, u} X.toRingedSpace) 0).map φ) g₀ h₀
  -- It is perfect by tag 08CR.
  have hEperfect : Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, u + 1} E :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished T hT hF.1 hG.1
  -- It has no cohomology in positive degrees.
  have hvanE : ∀ i : ℤ, 0 < i →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) i).obj E) := by
    intro i hi
    refine (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1) (by omega)).isZero_X₂ ?_ ?_
    · exact (RingedSpace.isZero_homology_singleFunctor_zero_of_ne_zero G i
        (by omega)).eq_zero_of_src _
    · exact (RingedSpace.isZero_homology_singleFunctor_zero_of_ne_zero F (i + 1)
        (by omega)).eq_zero_of_tgt _
  -- Its `H^0` is the cokernel of `φ`.
  let e₁ := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (OXMod.{u, u} X.toRingedSpace) 0).app F
  let e₂ := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (OXMod.{u, u} X.toRingedSpace) 0).app G
  have comm : (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) 0).map T.mor₁ ≫
      e₂.hom = e₁.hom ≫ φ :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (OXMod.{u, u} X.toRingedSpace) 0).hom.naturality φ
  have hz₁ : IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) 1).obj
      T.obj₁) :=
    RingedSpace.isZero_homology_singleFunctor_zero_of_ne_zero F 1 (by omega)
  let eC : (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) 0).obj E ≅
      cokernel φ := homologyCokernelIso T hT hz₁ φ e₁ e₂ comm
  -- Hence the cokernel is finitely presented, by tag 08DN (2).
  obtain ⟨K, hK, eK⟩ := Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect E hEperfect
  have hfpH := RingedSpace.isFinitePresentation_homology_of_isPseudoCoherentFrom E (-1)
    ⟨K, hK (-1), eK⟩ (fun i hi => hvanE i (by omega))
  have hz0 : ((-1 : ℤ) + 1) = 0 := by norm_num
  rw [hz0] at hfpH
  have hfpC : SheafOfModules.IsFinitePresentation
      (R := structureSheafOfRings X.toRingedSpace) (cokernel φ) := hfpH.of_iso eC
  have hfpC' : ((cokernel φ : X.Modules)).IsFinitePresentation := hfpC
  -- The cokernel vanishes over `U`, because `𝒢` does and pullback is right exact.
  have hpc₀ : PreservesFiniteColimits (modulePullback U.ι.toLRSHom.toShHom) :=
    RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback _
  have hCU : IsZero ((modulePullback U.ι.toLRSHom.toShHom).obj (cokernel φ)) := by
    refine IsZero.of_iso ?_ (PreservesCokernel.iso (modulePullback U.ι.toLRSHom.toShHom) φ)
    rw [IsZero.iff_id_eq_zero,
      ← cancel_epi (cokernel.π ((modulePullback U.ι.toLRSHom.toShHom).map φ)), comp_zero,
      Category.comp_id]
    exact hGU.eq_zero_of_src _
  have hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj (cokernel φ)) 0 :=
    isFiniteLocallyFreeOfRank_zero_of_isZero hCU
  -- The blowup of `X` in the zeroth Fitting ideal of the cokernel.
  set I : X.IdealSheafData := fittingIdeal (cokernel φ) ((0 : ℕ) : ℤ) with hIdef
  have hadm : Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) :=
    isAdmissibleBlowup_fittingIdeal (cokernel φ) U 0 hrank
  -- Tag 0ESN (4): the pullback of the cokernel is perfect of Tor dimension at most one.
  have hCpull : IsPerfectTorLEOne (blowUp I)
      ((Scheme.Modules.pullback (blowUpToBase I)).obj (cokernel φ)) :=
    isPerfect_and_hasTorAmplitude_modulePullback_fittingBlowUp (cokernel φ) U 0 hU hrank
  have hpc₁ : PreservesFiniteColimits (modulePullback (blowUpToBase I).toLRSHom.toShHom) :=
    RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback _
  have hcok : IsPerfectTorLEOne (blowUp I)
      (cokernel ((modulePullback (blowUpToBase I).toLRSHom.toShHom).map φ)) :=
    IsPerfectTorLEOne.of_iso
      (PreservesCokernel.iso (modulePullback (blowUpToBase I).toLRSHom.toShHom) φ) hCpull
  -- Tag 0ESS: the pullbacks of `ℱ` and `𝒢` stay perfect of Tor dimension at most one.
  have hA : IsPerfectTorLEOne (blowUp I)
      ((modulePullback (blowUpToBase I).toLRSHom.toShHom).obj F) :=
    ⟨isPerfect_modulePullback_blowUpToBase I F hF.1 hF.2,
      hasTorAmplitude_modulePullback_blowUpToBase I F hF.2⟩
  have hB : IsPerfectTorLEOne (blowUp I)
      ((modulePullback (blowUpToBase I).toLRSHom.toShHom).obj G) :=
    ⟨isPerfect_modulePullback_blowUpToBase I G hG.1 hG.2,
      hasTorAmplitude_modulePullback_blowUpToBase I G hG.2⟩
  -- The image is the kernel of the cokernel, and then the kernel is the kernel of the image.
  have him : IsPerfectTorLEOne (blowUp I)
      (Abelian.image ((modulePullback (blowUpToBase I).toLRSHom.toShHom).map φ)) :=
    isPerfectTorLEOne_abelianImage_of_cokernel _ hB hcok
  exact ⟨blowUp I, blowUpToBase I, hadm, isPerfectTorLEOne_kernel _ hA him, him, hcok⟩

end AlgebraicGeometry

end
