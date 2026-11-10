module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.FixingZeroDimensional
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.Twist
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.ZeroDimensionalAgreement
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.RingTheory.LocalCohomology.ArtinianOverLocalRing
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.ReducedProjective
public import StacksFrontier.AlgebraicGeometry.HProjective.AmpleBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.ProjectiveOverAmpleBase
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Part B of Orlov's theorem: a functor fixing the zero-dimensional sheaves is a twist

Let `k` be a field and `X` a proper regular scheme over `k`. A `k`-linear exact endofunctor `F` of
`D_perf(𝒪_X)` with `F(𝓕) ≅ 𝓕` for every coherent `𝓕` with zero-dimensional support is fully
faithful ([Stacks, Tag 0G26]) and, applying [Stacks, Tag 0GX0] to the pair `(F, 𝟭)`, essentially
surjective. So `exists_areSiblingsPerfect_of_fullyFaithful_of_essSurj` applies to it, which is
[Stacks, Tag 0G27]. Over an algebraically closed field and for `X` smooth, the automorphism it
produces is the identity and `F` is object-wise `E ↦ E ⊗^𝐋 L` with `L` invertible: this is
`AlgebraicGeometry.TwistOfFixingZeroDimensional`, part B of the reduction of [Stacks, Tag 0G0Y] to
object-wise statements.

The file then deduces [Stacks, Tag 0G06]: a fully faithful `F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)`, `Y`
proper over `k`, agreeing on the zero-dimensional sheaves with a Fourier-Mukai functor `G` of a
perfect kernel is a sibling of a Fourier-Mukai functor of a perfect kernel. Apply
[Stacks, Tag 0G27] to `H = R ∘ G`, `R` the right adjoint of `F` ([Stacks, Tag 0FYN]), and absorb
the quasi-inverse `M ↦ L(f⁻¹)^*(M ⊗^𝐋 ℒ^∨)` of the resulting twist into the kernel.

Finally, for `X` and `Y` smooth proper over `k`, [Stacks, Tag 0G0B]: a `k`-linear exact fully
faithful `F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` is a sibling of a Fourier-Mukai functor `Φ_K` with
perfect kernel `K` on `X ×_k Y`. The construction of [Stacks, Section 0G07]
(`AlgebraicGeometry.fourierMukaiAgreesOnZeroDimensional`) gives a perfect kernel `P` whose
Fourier-Mukai functor agrees with `F` on the zero-dimensional coherent modules, and
[Stacks, Tag 0G06] applied to `F` and `Φ_P` gives the sibling. If `F` is moreover an equivalence,
so is `Φ_K`, by [Stacks, Tag 0FZV] (`AlgebraicGeometry.AreSiblingsPerfect.isEquivalence`): this is
[Stacks, Tag 0G0D].

## Main results

* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.essSurj_of_fixes_zeroDimensional`:
  a fully faithful `F` fixing the zero-dimensional sheaves is essentially surjective.
* `Orlov.exists_areSiblingsPerfect_of_fixes_zeroDimensional`:
  [Stacks, Tag 0G27].
* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.twistOfFixingZeroDimensional`:
  `AlgebraicGeometry.TwistOfFixingZeroDimensional k` over an algebraically closed field.
* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.perfectInverseTwistCompIso`: the quasi-inverse
  of `M ↦ Lf^*M ⊗^𝐋 ℒ`.
* `Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.perfectFourierMukaiOverInverseTwistIso`: its
  composite with a Fourier-Mukai functor is the Fourier-Mukai functor of the twisted kernel.
* `Orlov.exists_areSiblingsPerfectRegularSource_perfectFourierMukaiOver`:
  [Stacks, Tag 0G06].
* `AlgebraicGeometry.exists_perfectFourierMukaiOver_agrees_zeroDimensional`: the functor `G` of
  [Stacks, Section 0G07], read in `D_perf(𝒪_Y)`.
* `AlgebraicGeometry.exists_fourierMukai_areSiblingsPerfect`: [Stacks, Tag 0G0B].
* `AlgebraicGeometry.exists_fourierMukai_isEquivalence_areSiblingsPerfect`: [Stacks, Tag 0G0D].
* `AlgebraicGeometry.nonempty_iso_of_areSiblings_coherentToModulesDerivedBounded`: siblings out
  of `D^b_Coh` of a reduced scheme proper over a field with an ample invertible module, the first
  fully faithful, are isomorphic.
* `AlgebraicGeometry.nonempty_iso_of_areSiblingsPerfect`: the same for siblings out of `D_perf`.
* `AlgebraicGeometry.exists_iso_perfectFourierMukaiOver`: Orlov's theorem for `X` smooth proper
  over `k` with an ample invertible module: `F` is isomorphic to the Fourier-Mukai functor of a
  perfect kernel.
* `AlgebraicGeometry.IsProjective.isProper_and_exists_isAmple_of_isAffine`: a projective morphism
  to an affine scheme is proper and its source has an ample invertible module.
* `AlgebraicGeometry.nonempty_iso_of_areSiblings_of_isProjective`:
  the first sentence of [Stacks, Tag 0G01], for `X` reduced and projective over `k`.
* `AlgebraicGeometry.exists_iso_perfectFourierMukaiOver_of_isProjective`: [Stacks, Tag 0G0C]
  (Orlov), for `X` and `Y` smooth proper over `k` and `X` projective over `k`.

## References

* [Stacks Project, Tag 0G26](https://stacks.math.columbia.edu/tag/0G26)
* [Stacks Project, Tag 0GX0](https://stacks.math.columbia.edu/tag/0GX0)
* [Stacks Project, Tag 0G27](https://stacks.math.columbia.edu/tag/0G27)
* [Stacks Project, Tag 0G05](https://stacks.math.columbia.edu/tag/0G05)
* [Stacks Project, Tag 0G06](https://stacks.math.columbia.edu/tag/0G06)
* [Stacks Project, Tag 0FYN](https://stacks.math.columbia.edu/tag/0FYN)
* [Stacks Project, Section 0G07](https://stacks.math.columbia.edu/tag/0G07)
* [Stacks Project, Tag 0G0B](https://stacks.math.columbia.edu/tag/0G0B)
* [Stacks Project, Tag 0G0D](https://stacks.math.columbia.edu/tag/0G0D)
* [Stacks Project, Tag 0G0C](https://stacks.math.columbia.edu/tag/0G0C)
* [Stacks Project, Tag 0G01](https://stacks.math.columbia.edu/tag/0G01)
* [Stacks Project, Tag 0FZV](https://stacks.math.columbia.edu/tag/0FZV)
* [Stacks Project, Tag 0FZZ](https://stacks.math.columbia.edu/tag/0FZZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.PerfectComplexes
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.CoherentModuleFunctors (coherentToModules)

universe u

namespace Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

attribute [local instance 100000] HasDerivedCategory.standard

-- Two abelian structures on `Coh(𝒪_X)` are in scope; `D^b_Coh` and the sibling relation are
-- stated with the one of `AlgebraicGeometry.CoherentAbelian`, so it is the one selected here.
attribute [local instance 100000] CoherentAbelian.coherentModulesAbelian

section Field

variable {k : Type u} [Field k] {X : Over (Spec (CommRingCat.of k))} [IsProper X.hom]

/-- **A fully faithful functor fixing the zero-dimensional sheaves is essentially surjective**:
[Stacks, Tag 0GX0] for the pair `(F, 𝟭)`. -/
theorem essSurj_of_fixes_zeroDimensional (hX : IsRegular X.left)
    (F : PerfectDerivedCategory X.left ⥤ PerfectDerivedCategory X.left) [F.CommShift ℤ]
    [F.IsTriangulated]
    (hlin : letI : Linear k X.left.Modules := modulesLinear k X; F.Linear k)
    (hfix : ∀ (𝓕 : X.left.Modules), 𝓕.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp 𝓕) = 0 →
      ∀ h𝓕 : IsPerfect (X := X.left.toRingedSpace)
          ((DerivedCategory.singleFunctor X.left.Modules 0).obj 𝓕),
        Nonempty ((F.obj ⟨_, h𝓕⟩).obj ≅ (DerivedCategory.singleFunctor X.left.Modules 0).obj 𝓕))
    (hFF : Nonempty F.FullyFaithful) : F.EssSurj := by
  let : Linear k X.left.Modules := modulesLinear k X
  have : F.Linear k := hlin
  refine ⟨fun E => essImage_of_agree_on_zeroDimensional X X hX F (𝟭 _)
    (fun M hM hdim hpM => ?_) hFF E⟩
  obtain ⟨φ⟩ := hfix M hM hdim hpM
  exact ⟨((ObjectProperty.fullyFaithfulι _).preimageIso φ :
    F.obj ⟨_, hpM⟩ ≅ ⟨_, hpM⟩)⟩

/-- **[Stacks, Tag 0G27].** Let `k` be a field, let `X` be a proper scheme over `k` which is
regular, and let `F : D_perf(𝒪_X) ⥤ D_perf(𝒪_X)` be a `k`-linear exact functor. Assume that for
every coherent `𝒪_X`-module `𝓕` with `dim Supp(𝓕) = 0` there is an isomorphism `𝓕 ≅ F(𝓕)`. Then
there exist an automorphism `f : X ⟶ X` over `k` which induces the identity on the underlying
topological space and an invertible `𝒪_X`-module `ℒ` such that `F` and
`F'(M) = Lf^*M ⊗^𝐋_{𝒪_X} ℒ` are siblings.

Here `F'` is `perfectPullbackDerivedTensor f.hom ℒ` and "siblings" is
`AlgebraicGeometry.AreSiblingsPerfect` ([Stacks, Tag 0FZZ]: siblings as functors on
`D_perf = D^b_Coh`, `X` being regular). `F` is fully faithful by [Stacks, Tag 0G26] and essentially
surjective by [Stacks, Tag 0GX0], and the rest of the source's proof is
`exists_areSiblingsPerfect_of_fullyFaithful_of_essSurj`. -/
@[stacks 0G27]
theorem exists_areSiblingsPerfect_of_fixes_zeroDimensional (hX : IsRegular X.left)
    (F : PerfectDerivedCategory X.left ⥤ PerfectDerivedCategory X.left) [F.CommShift ℤ]
    [F.IsTriangulated]
    (hlin : letI : Linear k X.left.Modules := modulesLinear k X; F.Linear k)
    (hfix : ∀ (𝓕 : X.left.Modules), 𝓕.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp 𝓕) = 0 →
      ∀ h𝓕 : IsPerfect (X := X.left.toRingedSpace)
          ((DerivedCategory.singleFunctor X.left.Modules 0).obj 𝓕),
        Nonempty ((F.obj ⟨_, h𝓕⟩).obj ≅ (DerivedCategory.singleFunctor X.left.Modules 0).obj 𝓕)) :
    haveI : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
    ∃ (f : X.left ≅ X.left) (L : X.left.Modules)
      (hL : Stacks.SheafOfModules.IsInvertible X.left.presheaf X.left.ringCatSheaf.2 L),
      f.hom ≫ X.hom = X.hom ∧ (∀ x : X.left, f.hom x = x) ∧
      @AreSiblingsPerfect X.left X.left hX hX _ _ F
        (perfectPullbackDerivedTensor f.hom L (isPerfect_single_of_isInvertible hX L hL))
        ‹_› ‹_›
        (show (perfectPullbackDerivedTensor f.hom L
          (isPerfect_single_of_isInvertible hX L hL)).CommShift ℤ from inferInstance)
        (show (perfectPullbackDerivedTensor f.hom L
          (isPerfect_single_of_isInvertible hX L hL)).IsTriangulated from inferInstance) := by
  have hFF := fullyFaithful_of_fixes_zeroDimensional hX F hlin hfix
  have := essSurj_of_fixes_zeroDimensional hX F hlin hfix hFF
  exact exists_areSiblingsPerfect_of_fullyFaithful_of_essSurj hX F hlin hfix hFF

end Field

/-- **`AlgebraicGeometry.TwistOfFixingZeroDimensional` over an algebraically closed field**: a
`K`-linear exact endofunctor `H` of `D_perf(𝒪_X)`, `X` smooth and proper over `K`, fixing every
coherent module with zero-dimensional support is fully faithful ([Stacks, Tag 0G26]), essentially
surjective ([Stacks, Tag 0GX0]), hence object-wise a twist by an invertible module
([Stacks, Tag 0G27] and [Stacks, Tag 0G05], `exists_twist_of_fullyFaithful_of_essSurj`). -/
theorem twistOfFixingZeroDimensional (K : Type u) [Field K] [IsAlgClosed K] :
    TwistOfFixingZeroDimensional K := by
  intro A hs hp
  let : Linear K A.left.Modules := modulesLinear K A
  intro H hlin hcs htri hfix
  let := hcs
  have := htri
  have := hs
  have := hp
  have hX : IsRegular A.left := isRegular_of_smooth_over_field A.hom
  have hFF := fullyFaithful_of_fixes_zeroDimensional (X := A) hX H hlin hfix
  have := essSurj_of_fixes_zeroDimensional hX H hlin hfix hFF
  exact exists_twist_of_fullyFaithful_of_essSurj H hlin hfix hFF

/-! ### The quasi-inverse of a twisted pullback -/

section QuasiInverse

variable {X : Scheme.{u}} (hX : IsRegular X) [IsNoetherian X] (f : X ≅ X) (L : X.Modules)
  (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L)

/-- **The functor `M ↦ L(f⁻¹)^*(M ⊗^𝐋 ℒ^∨)` on perfect complexes**, for an automorphism `f` and an
invertible module `ℒ` with dual `ℒ^∨`: a quasi-inverse of `M ↦ Lf^*M ⊗^𝐋 ℒ`
(`perfectInverseTwistCompIso`). -/
def perfectInverseTwist : PerfectDerivedCategory X ⥤ PerfectDerivedCategory X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙
      dtenR X ((DerivedCategory.singleFunctor X.Modules 0).obj
        (Stacks.SheafOfModules.dualSheaf X.presheaf X.ringCatSheaf.2 L)) ⋙ dpull f.inv)
    fun E => by
      have := hL
      exact RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ _
        (isPerfect_dtenR _ _ E.property (isPerfect_single_of_isInvertible hX _
          (Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf X.presheaf
            X.ringCatSheaf.2 L)))

/-- **`M ↦ L(f⁻¹)^*(M ⊗^𝐋 ℒ^∨)` is a right inverse of `M ↦ Lf^*M ⊗^𝐋 ℒ`**:
`Lf^* L(f⁻¹)^* ≅ 𝟭` ([Stacks, Tag 0D5S]), and `(M ⊗^𝐋 ℒ^∨) ⊗^𝐋 ℒ ≅ M ⊗^𝐋 (ℒ^∨ ⊗ ℒ) ≅ M`, the
evaluation `ℒ^∨ ⊗ ℒ ⟶ 𝒪_X` being an isomorphism for `ℒ` invertible. -/
def perfectInverseTwistCompIso :
    perfectInverseTwist hX f L hL ⋙
        perfectPullbackDerivedTensor f.hom L (isPerfect_single_of_isInvertible hX L hL) ≅
      𝟭 _ :=
  haveI := hL
  letI := Scheme.Modules.canonicalDerivedMonoidal X
  let L' := Stacks.SheafOfModules.dualSheaf X.presheaf X.ringCatSheaf.2 L
  have hev := Stacks.SheafOfModules.Invertible.isIso_evaluation X.presheaf X.ringCatSheaf.2 L
  let e : (DerivedCategory.singleFunctor X.Modules 0).obj L' ⊗
      (DerivedCategory.singleFunctor X.Modules 0).obj L ≅ 𝟙_ _ :=
    (singleDerivedTensorIso X L (isFlat_of_isInvertible L hL)).app L' ≪≫
      (DerivedCategory.singleFunctor X.Modules 0).mapIso
        (@asIso _ _ _ _ (Stacks.SheafOfModules.evaluation X.presheaf X.ringCatSheaf.2 L) hev)
  let ρ : MonoidalCategory.tensorRight (𝟙_ (DerivedCategory X.Modules)) ≅ 𝟭 _ :=
    NatIso.ofComponents (fun M => ρ_ M) (fun φ => by simp)
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (ObjectProperty.ι _)
      (Functor.isoWhiskerLeft (dtenR X ((DerivedCategory.singleFunctor X.Modules 0).obj L'))
          ((Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight (dpullCompIsoIdOfCompEqId f.hom f.inv f.hom_inv_id) _ ≪≫
            Functor.leftUnitor _) ≪≫
        (tensorRightTensor _ _).symm ≪≫ (tensoringRight _).mapIso e ≪≫ ρ) ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

include hL in
/-- **`𝓕 ↦ (f⁻¹)^*(𝓕 ⊗ ℒ^∨)` preserves coherence**: tensoring with an invertible module does, and
so does the inverse image along an isomorphism (quasi-coherence and finite type are preserved,
and on a Noetherian scheme that is coherence, [Stacks, Tag 01XZ]). -/
theorem isCoherent_pullback_tensor_dualSheaf (M : X.Modules) (hM : M.IsCoherent) :
    ((Scheme.Modules.pullback f.inv).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj
        (Stacks.SheafOfModules.dualSheaf X.presheaf X.ringCatSheaf.2 L)).obj M)).IsCoherent := by
  have := hL
  have := hM
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.SheafOfModules.dualSheaf X.presheaf X.ringCatSheaf.2 L) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
      (Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf X.presheaf X.ringCatSheaf.2 L)
  have h₁ := AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X M
    (Stacks.SheafOfModules.dualSheaf X.presheaf X.ringCatSheaf.2 L)
  obtain ⟨hq, hft⟩ :=
    (CoherentOfFiniteType.isCoherent_iff_isQuasicoherent_and_isFiniteType _).1 h₁
  refine (CoherentOfFiniteType.isCoherent_iff_isQuasicoherent_and_isFiniteType _).2
    ⟨Stacks.Modules.isQuasicoherent_pullback f.inv _ hq, ?_⟩
  exact @SheafOfModules.pullback_isFiniteType _ _ f.inv.toLRSHom.toShHom _ hft

/-- The functor `𝓕 ↦ (f⁻¹)^*(𝓕 ⊗ ℒ^∨)` on coherent modules. -/
def coherentInverseTwist :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf ⥤
      AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
  ObjectProperty.lift _ (coherentToModules X ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj
        (Stacks.SheafOfModules.dualSheaf X.presheaf X.ringCatSheaf.2 L) ⋙
      Scheme.Modules.pullback f.inv)
    fun M => isCoherent_pullback_tensor_dualSheaf f L hL M.obj M.property

/-- **On coherent modules `M ↦ L(f⁻¹)^*(M ⊗^𝐋 ℒ^∨)` is `𝓕 ↦ (f⁻¹)^*(𝓕 ⊗ ℒ^∨)`**, naturally: `ℒ^∨`
is flat and `f⁻¹` an isomorphism, so neither the tensor product nor the pullback needs deriving. -/
def perfectCoherentSingleFunctorCompPerfectInverseTwistIso :
    perfectCoherentSingleFunctor hX ⋙ perfectInverseTwist hX f L hL ≅
      coherentInverseTwist f L hL ⋙ perfectCoherentSingleFunctor hX :=
  haveI := hL
  let L' := Stacks.SheafOfModules.dualSheaf X.presheaf X.ringCatSheaf.2 L
  have hL' : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L' :=
    Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf X.presheaf X.ringCatSheaf.2 L
  let e₁ : DerivedCategory.singleFunctor X.Modules 0 ⋙ dpull f.inv ≅
      Scheme.Modules.pullback f.inv ⋙ DerivedCategory.singleFunctor X.Modules 0 :=
    Functor.isoWhiskerLeft (DerivedCategory.singleFunctor X.Modules 0)
        (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIsoMapDerivedCategoryOfIsIso
          f.inv.toLRSHom.toShHom) ≪≫
      (RingedSpaceModuleAdjunction.modulePullback
        f.inv.toLRSHom.toShHom).mapDerivedCategorySingleFunctor 0
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.isoWhiskerRight (boundedCoherentSingleFunctorCompιIso X)
        (dtenR X ((DerivedCategory.singleFunctor X.Modules 0).obj L') ⋙ dpull f.inv) ≪≫
      Functor.isoWhiskerLeft (coherentInModules X).ι
        ((Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (singleDerivedTensorIso X L' (isFlat_of_isInvertible L' hL'))
            (dpull f.inv) ≪≫
          Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _ e₁) ≪≫
      Functor.isoWhiskerLeft (coherentInverseTwist f L hL)
        (boundedCoherentSingleFunctorCompιIso X).symm)

end QuasiInverse

/-! ### Fully faithful functors agreeing with Fourier-Mukai functors on zero-dimensional sheaves -/

section FourierMukai

variable {k : Type u} [Field k] {X Y : Over (Spec (CommRingCat.of k))} [IsProper X.hom]
  [IsProper Y.hom]

/-- **The categorical core of [Stacks, Tag 0G06].** Let `H ⋙ F ≅ G`, let `T` be a right inverse
of `H'` with `Φ' ≅ T ⋙ G`, and let `H` and `H'` agree object by object and, naturally, along
`j : C₀ ⥤ C`, where `T` restricts along `j` to `t`. Then `F` and `Φ'` agree naturally along `j`
and object by object: `Φ' ≅ T ⋙ G ≅ T ⋙ H ⋙ F`, which along `j` is `t ⋙ j ⋙ H ⋙ F ≅
t ⋙ j ⋙ H' ⋙ F ≅ j ⋙ T ⋙ H' ⋙ F ≅ j ⋙ F`. -/
theorem nonempty_iso_and_forall_nonempty_iso_of_rightInverse {C₀ C D : Type*} [Category* C₀]
    [Category* C] [Category* D] (j : C₀ ⥤ C) (t : C₀ ⥤ C₀) (F G Φ' : C ⥤ D) (H H' T : C ⥤ C)
    (γ : H ⋙ F ≅ G) (β : Φ' ≅ T ⋙ G) (ε : T ⋙ H' ≅ 𝟭 C) (τ : j ⋙ T ≅ t ⋙ j)
    (σ : j ⋙ H ≅ j ⋙ H') (hobj : ∀ K, Nonempty (H.obj K ≅ H'.obj K)) :
    Nonempty (j ⋙ F ≅ j ⋙ Φ') ∧ ∀ K, Nonempty (F.obj K ≅ Φ'.obj K) := by
  refine ⟨⟨?_⟩, fun K => ⟨?_⟩⟩
  · exact (Functor.isoWhiskerLeft j (β ≪≫ Functor.isoWhiskerLeft T γ.symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight τ (H ⋙ F) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft t ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight σ F ≪≫ Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight τ.symm (H' ⋙ F) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft j ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ε F ≪≫ Functor.leftUnitor F)).symm
  · exact (β.app K ≪≫ γ.symm.app (T.obj K) ≪≫ F.mapIso (hobj (T.obj K)).some ≪≫
      F.mapIso (ε.app K)).symm

section Kernel

variable (Y) (f : X.left ≅ X.left) (hf : f.hom ≫ X.hom = X.hom) (L : X.left.Modules)
  (P : DerivedCategory (pullback X.hom Y.hom).Modules)

/-- **The twisted kernel** `L pr_1^*ℒ^∨ ⊗^𝐋 L(f × 𝟙)^* P` on `X ×_k Y`, whose Fourier-Mukai functor
is `M ↦ Φ_P(L(f⁻¹)^*(M ⊗^𝐋 ℒ^∨))` (`perfectFourierMukaiOverInverseTwistIso`). -/
def inverseTwistKernel : DerivedCategory (pullback X.hom Y.hom).Modules :=
  (dtenR _ ((dpull (pullbackMapIsoOfIso Y.hom f hf).hom).obj P)).obj
    ((fourierMukaiPullback X.hom Y.hom).obj ((DerivedCategory.singleFunctor X.left.Modules 0).obj
      (Stacks.SheafOfModules.dualSheaf X.left.presheaf X.left.ringCatSheaf.2 L)))

variable {Y} {L} (hL : Stacks.SheafOfModules.IsInvertible X.left.presheaf X.left.ringCatSheaf.2 L)
  {P} (hP : IsPerfect (X := (pullback X.hom Y.hom).toRingedSpace) P) (hX : IsRegular X.left)
  [IsNoetherian X.left] [IsNoetherian Y.left]

omit [IsProper X.hom] [IsProper Y.hom] [AlgebraicGeometry.IsNoetherian Y.left] in
include hL hP hX in
/-- The twisted kernel of a perfect kernel is perfect ([Stacks, Tag 09J5]). -/
theorem isPerfect_inverseTwistKernel :
    IsPerfect (X := (pullback X.hom Y.hom).toRingedSpace) (inverseTwistKernel Y f hf L P) := by
  have := hL
  exact isPerfect_dtenR _ _ (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback.{u} _ _
      (isPerfect_single_of_isInvertible hX _
        (Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf X.left.presheaf
          X.left.ringCatSheaf.2 L)))
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ P hP)

/-- **Precomposing a Fourier-Mukai functor with `M ↦ L(f⁻¹)^*(M ⊗^𝐋 ℒ^∨)` twists its kernel**:
`Φ_{P'} ≅ Φ_P ∘ T` for the twisted kernel `P'`, by `fourierMukaiDpullIso` and
`fourierMukaiTwistNatIso`. -/
def perfectFourierMukaiOverInverseTwistIso :
    perfectFourierMukaiOver k X Y (isPerfect_inverseTwistKernel f hf hL hP hX) ≅
      perfectInverseTwist hX f L hL ⋙ perfectFourierMukaiOver k X Y hP :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (ObjectProperty.ι _)
      ((fourierMukaiTwistNatIso X.hom Y.hom _ _).symm ≪≫
        Functor.isoWhiskerLeft _ (fourierMukaiDpullIso Y.hom f hf P).symm))

end Kernel

/-- **[Stacks, Tag 0G06].** Let `k` be a field, let `X`, `Y` be proper schemes over `k` with `X`
regular, and let `F, G : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` be `k`-linear exact functors such that
(1) `F(𝓕) ≅ G(𝓕)` for every coherent `𝒪_X`-module `𝓕` with `dim Supp(𝓕) = 0`, (2) `F` is fully
faithful, and (3) `G` is a Fourier-Mukai functor whose kernel is in `D_perf(𝒪_{X × Y})`. Then
there is a Fourier-Mukai functor `F' : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` whose kernel is in
`D_perf(𝒪_{X × Y})` such that `F` and `F'` are siblings.

Here (3) reads: `G` is naturally isomorphic to `Φ_P = perfectFourierMukaiOver k X Y hP` for a
perfect `P` on `X ×_k Y`; the conclusion gives `F' = Φ_{P'}` itself, and "siblings" is
`AlgebraicGeometry.AreSiblingsPerfectRegularSource` ([Stacks, Tag 0FZZ] for a regular `X` and an
arbitrary `Y` of finite type over `k`).

The proof is the source's. By [Stacks, Tag 0GX0] the essential image of `G` lies in that of `F`.
Let `R` be the exact right adjoint of `F` ([Stacks, Tag 0FYN]); `F` being fully faithful,
`H = R ∘ G` satisfies `F ∘ H ≅ G` and fixes the zero-dimensional sheaves, so by
[Stacks, Tag 0G27] it is a sibling of `H'(M) = Lf^*M ⊗^𝐋 ℒ` for an automorphism `f` of `X` over
`k` and an invertible `ℒ`. With `T(M) = L(f⁻¹)^*(M ⊗^𝐋 ℒ^∨)`, `H' ∘ T ≅ 𝟭`, `T` preserves
coherent modules, and `G ∘ T` is the Fourier-Mukai functor of the twisted kernel
`P' = L pr_1^*ℒ^∨ ⊗^𝐋 L(f × 𝟙)^* P`. Then `F ≅ F ∘ H' ∘ T` is a sibling of
`F ∘ H ∘ T ≅ G ∘ T ≅ Φ_{P'}`. -/
@[stacks 0G06]
theorem exists_areSiblingsPerfectRegularSource_perfectFourierMukaiOver (hX : IsRegular X.left)
    (F G : PerfectDerivedCategory X.left ⥤ PerfectDerivedCategory Y.left)
    [F.CommShift ℤ] [F.IsTriangulated] [G.CommShift ℤ] [G.IsTriangulated]
    (hFlin : letI : Linear k X.left.Modules := modulesLinear k X
      letI : Linear k Y.left.Modules := modulesLinear k Y
      F.Linear k)
    (hGlin : letI : Linear k X.left.Modules := modulesLinear k X
      letI : Linear k Y.left.Modules := modulesLinear k Y
      G.Linear k)
    (hagree : ∀ (M : X.left.Modules), M.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp M) = 0 →
      ∀ (hM : IsPerfect (X := X.left.toRingedSpace)
          ((DerivedCategory.singleFunctor X.left.Modules 0).obj M)),
        Nonempty (F.obj (⟨_, hM⟩ : PerfectDerivedCategory X.left) ≅
          G.obj (⟨_, hM⟩ : PerfectDerivedCategory X.left)))
    (hFF : Nonempty F.FullyFaithful)
    (hG : haveI : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
      ∃ (P : DerivedCategory (pullback X.hom Y.hom).Modules)
        (hP : IsPerfect (X := (pullback X.hom Y.hom).toRingedSpace) P),
        Nonempty (G ≅ perfectFourierMukaiOver k X Y hP)) :
    haveI : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
    haveI : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
    ∃ (P' : DerivedCategory (pullback X.hom Y.hom).Modules)
      (hP' : IsPerfect (X := (pullback X.hom Y.hom).toRingedSpace) P'),
      @AreSiblingsPerfectRegularSource X.left Y.left hX _ _ F (perfectFourierMukaiOver k X Y hP')
        ‹_› ‹_›
        (@commShift_fourierMukaiOn _ _ _ X.hom Y.hom _ _ _
          (isTriangulated_perfectInModules X.left) (isTriangulated_perfectInModules Y.left) _)
        (@isTriangulated_fourierMukaiOn _ _ _ X.hom Y.hom _ _ _
          (isTriangulated_perfectInModules X.left) (isTriangulated_perfectInModules Y.left) _) := by
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  have : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
  let : Linear k X.left.Modules := modulesLinear k X
  let : Linear k Y.left.Modules := modulesLinear k Y
  have : F.Linear k := hFlin
  have : G.Linear k := hGlin
  obtain ⟨P, hP, ⟨eG⟩⟩ := hG
  have : F.Full := hFF.some.full
  have : F.Faithful := hFF.some.faithful
  -- the exact right adjoint of `F`, and `H = R ∘ G`
  obtain ⟨R, ⟨adj⟩, hRc, hRt⟩ := exists_exact_rightAdjoint X Y hX F
  let := hRc
  have : R.Linear k := Stacks.LocalCohomology.rightAdjoint_linear adj
  let H := G ⋙ R
  have hfix : ∀ (𝓕 : X.left.Modules), 𝓕.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp 𝓕) = 0 →
      ∀ h𝓕 : IsPerfect (X := X.left.toRingedSpace)
          ((DerivedCategory.singleFunctor X.left.Modules 0).obj 𝓕),
        Nonempty ((H.obj ⟨_, h𝓕⟩).obj ≅
          (DerivedCategory.singleFunctor X.left.Modules 0).obj 𝓕) := by
    intro 𝓕 hc hd h𝓕
    obtain ⟨φ⟩ := hagree 𝓕 hc hd h𝓕
    exact ⟨(ObjectProperty.ι _).mapIso (R.mapIso φ.symm ≪≫ (asIso (adj.unit.app _)).symm)⟩
  obtain ⟨f, L, hL, hfX, -, hsib⟩ :=
    exists_areSiblingsPerfect_of_fixes_zeroDimensional hX H (inferInstance : H.Linear k) hfix
  -- `F ∘ H ≅ G`, the counit being invertible on the essential image of `F` ([Stacks, Tag 0GX0])
  have : IsIso (Functor.whiskerLeft G adj.counit) := by
    have : ∀ E, IsIso ((Functor.whiskerLeft G adj.counit).app E) := fun E =>
      (adj.isIso_counit_app_iff_mem_essImage).2
        (essImage_of_agree_on_zeroDimensional X Y hX F G hagree hFF E)
    exact NatIso.isIso_of_isIso_app _
  let γ : H ⋙ F ≅ G := asIso (Functor.whiskerLeft G adj.counit) ≪≫ Functor.rightUnitor G
  -- the quasi-inverse `T` of `H'`, and the twisted kernel
  let H' := perfectPullbackDerivedTensor f.hom L (isPerfect_single_of_isInvertible hX L hL)
  refine ⟨_, isPerfect_inverseTwistKernel f hfX hL hP hX, ?_⟩
  obtain ⟨⟨σ⟩, hobj⟩ := (@areSiblingsPerfectRegularSource_iff X.left X.left hX _ _ H H'
    (show H.CommShift ℤ from inferInstance) (show H.IsTriangulated from inferInstance)
    (show H'.CommShift ℤ from inferInstance) (show H'.IsTriangulated from inferInstance) _).1 hsib
  have key := nonempty_iso_and_forall_nonempty_iso_of_rightInverse
    (perfectCoherentSingleFunctor hX) (coherentInverseTwist f L hL) F G
    (perfectFourierMukaiOver k X Y (isPerfect_inverseTwistKernel f hfX hL hP hX)) H H'
    (perfectInverseTwist hX f L hL) γ
    (perfectFourierMukaiOverInverseTwistIso f hfX hL hP hX ≪≫ Functor.isoWhiskerLeft _ eG.symm)
    (perfectInverseTwistCompIso hX f L hL)
    (perfectCoherentSingleFunctorCompPerfectInverseTwistIso hX f L hL) σ hobj
  have h1 := (@areSiblingsPerfectRegularSource_iff X.left Y.left hX _ _ F
    (perfectFourierMukaiOver k X Y (isPerfect_inverseTwistKernel f hfX hL hP hX)) ‹_› ‹_›
    (@commShift_fourierMukaiOn _ _ _ X.hom Y.hom _ _ _
      (isTriangulated_perfectInModules X.left) (isTriangulated_perfectInModules Y.left) _)
    (@isTriangulated_fourierMukaiOn _ _ _ X.hom Y.hom _ _ _
      (isTriangulated_perfectInModules X.left) (isTriangulated_perfectInModules Y.left) _) _).2 key
  exact h1

end FourierMukai

section FullyFaithfulSibling

/-! ### A fully faithful functor has a Fourier-Mukai sibling ([Stacks, Tag 0G0B]) -/

variable (k : Type u) [Field k] (X Y : Over (Spec (.of k))) [Smooth X.hom] [IsProper X.hom]
  [Smooth Y.hom] [IsProper Y.hom]

/-- **The functor `G` of [Stacks, Section 0G07], in `D_perf`.** For smooth proper `k`-schemes `X`,
`Y` and a `k`-linear exact fully faithful `F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` there is a perfect
kernel `P` on `X ×_k Y` with `F(𝓕) ≅ Φ_P(𝓕)` in `D_perf(𝒪_Y)` for every coherent `𝒪_X`-module
`𝓕` with zero-dimensional support: `AlgebraicGeometry.fourierMukaiAgreesOnZeroDimensional`, read
in the perfect derived category. -/
theorem _root_.AlgebraicGeometry.exists_perfectFourierMukaiOver_agrees_zeroDimensional
    (F : PerfectDerivedCategory X.left ⥤ PerfectDerivedCategory Y.left)
    [F.CommShift ℤ] [F.IsTriangulated]
    (hlin : letI : Linear k X.left.Modules := modulesLinear k X
      letI : Linear k Y.left.Modules := modulesLinear k Y
      F.Linear k)
    (hF : Nonempty F.FullyFaithful) :
    haveI : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
    ∃ (P : DerivedCategory (pullback X.hom Y.hom).Modules)
      (hP : IsPerfect (X := (pullback X.hom Y.hom).toRingedSpace) P),
      ∀ (𝓕 : X.left.Modules), 𝓕.IsCoherent → topologicalKrullDim (SheafOfModules.supp 𝓕) = 0 →
        ∀ h𝓕 : IsPerfect (X := X.left.toRingedSpace)
            ((DerivedCategory.singleFunctor X.left.Modules 0).obj 𝓕),
          Nonempty (F.obj ⟨_, h𝓕⟩ ≅ (perfectFourierMukaiOver k X Y hP).obj ⟨_, h𝓕⟩) := by
  have : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
  obtain ⟨P, hP, hPF⟩ := fourierMukaiAgreesOnZeroDimensional k X Y inferInstance inferInstance
    inferInstance inferInstance F hlin ‹_› ‹_› hF
  exact ⟨P, hP, fun 𝓕 hcoh hdim h𝓕 => ⟨perfectIsoMk (hPF 𝓕 hcoh hdim h𝓕).some.symm⟩⟩

/-- **Stacks Project, Tag 0G0B.** Let `k` be a field and `X`, `Y` smooth proper `k`-schemes.
Every `k`-linear exact fully faithful functor `F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` has a sibling
([Stacks, Tag 0FZZ]) which is a Fourier-Mukai functor `Φ_K : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` whose
kernel `K` is a perfect object of `D(𝒪_{X ×_k Y})`.

The proof is the source's: [Stacks, Tag 0G06] applied to `F` and the Fourier-Mukai functor `G`
of [Stacks, Section 0G07]
(`AlgebraicGeometry.exists_perfectFourierMukaiOver_agrees_zeroDimensional`), which agrees with
`F` on the coherent modules with zero-dimensional support. -/
@[stacks 0G0B]
theorem _root_.AlgebraicGeometry.exists_fourierMukai_areSiblingsPerfect
    (F : PerfectDerivedCategory X.left ⥤ PerfectDerivedCategory Y.left)
    [hFs : F.CommShift ℤ] [hFt : F.IsTriangulated]
    (hlin : letI : Linear k X.left.Modules := modulesLinear k X
      letI : Linear k Y.left.Modules := modulesLinear k Y
      F.Linear k)
    (hF : Nonempty F.FullyFaithful) :
    haveI : CompactSpace X.left := (quasiCompact_iff_compactSpace X.hom).mp inferInstance
    haveI : CompactSpace Y.left := (quasiCompact_iff_compactSpace Y.hom).mp inferInstance
    haveI : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
    ∃ (K : DerivedCategory (pullback X.hom Y.hom).Modules)
      (hK : IsPerfect (X := (pullback X.hom Y.hom).toRingedSpace) K),
      @AreSiblingsPerfect X.left Y.left (isRegular_of_smooth_over_field X.hom)
        (isRegular_of_smooth_over_field Y.hom) _ _ F (perfectFourierMukaiOver k X Y hK) hFs hFt
        (commShift_fourierMukaiOn _ _ _ _ _ _) (isTriangulated_fourierMukaiOn _ _ _ _ _ _) := by
  have : CompactSpace X.left := (quasiCompact_iff_compactSpace X.hom).mp inferInstance
  have : CompactSpace Y.left := (quasiCompact_iff_compactSpace Y.hom).mp inferInstance
  have : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
  obtain ⟨P, hP, hPF⟩ := exists_perfectFourierMukaiOver_agrees_zeroDimensional k X Y F hlin hF
  obtain ⟨K, hK, h⟩ := exists_areSiblingsPerfectRegularSource_perfectFourierMukaiOver
    (isRegular_of_smooth_over_field X.hom) F (perfectFourierMukaiOver k X Y hP) hlin
    (perfectFourierMukaiOver_linear k X Y hP) hPF hF ⟨P, hP, ⟨Iso.refl _⟩⟩
  exact ⟨K, hK, h⟩

/-- **Stacks Project, Tag 0G0D.** Let `k` be a field and `X`, `Y` smooth proper `k`-schemes. If
`F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` is a `k`-linear exact equivalence, then there is a Fourier-Mukai
functor `F' = Φ_K : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` with kernel `K ∈ D_perf(𝒪_{X ×_k Y})` which is
an equivalence and a sibling of `F`. The functor of [Stacks, Tag 0G0B] is a sibling of `F`, and a
sibling of an equivalence is an equivalence by [Stacks, Tag 0FZV]
(`AlgebraicGeometry.AreSiblingsPerfect.isEquivalence`). -/
@[stacks 0G0D]
theorem _root_.AlgebraicGeometry.exists_fourierMukai_isEquivalence_areSiblingsPerfect
    (F : PerfectDerivedCategory X.left ⥤ PerfectDerivedCategory Y.left)
    [hFs : F.CommShift ℤ] [hFt : F.IsTriangulated]
    (hlin : letI : Linear k X.left.Modules := modulesLinear k X
      letI : Linear k Y.left.Modules := modulesLinear k Y
      F.Linear k)
    [F.IsEquivalence] :
    haveI : CompactSpace X.left := (quasiCompact_iff_compactSpace X.hom).mp inferInstance
    haveI : CompactSpace Y.left := (quasiCompact_iff_compactSpace Y.hom).mp inferInstance
    haveI : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
    ∃ (K : DerivedCategory (pullback X.hom Y.hom).Modules)
      (hK : IsPerfect (X := (pullback X.hom Y.hom).toRingedSpace) K),
      (perfectFourierMukaiOver k X Y hK).IsEquivalence ∧
        @AreSiblingsPerfect X.left Y.left (isRegular_of_smooth_over_field X.hom)
          (isRegular_of_smooth_over_field Y.hom) _ _ F (perfectFourierMukaiOver k X Y hK) hFs hFt
          (commShift_fourierMukaiOn _ _ _ _ _ _) (isTriangulated_fourierMukaiOn _ _ _ _ _ _) := by
  have : IsNoetherian X.left := isNoetherian_of_locallyOfFiniteType X.hom
  have : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
  obtain ⟨K, hK, hsib⟩ := exists_fourierMukai_areSiblingsPerfect k X Y F hlin
    ⟨Functor.FullyFaithful.ofFullyFaithful F⟩
  exact ⟨K, hK, hsib.isEquivalence (hF := ‹_›), hsib⟩

end FullyFaithfulSibling

section ReducedProjective

/-! ### Siblings out of `D^b_Coh` of a reduced projective scheme ([Stacks, Tag 0G01]) -/

/-- Functors out of the target of an equivalence `e` are isomorphic if their composites with
`e.functor` are. -/
private theorem nonempty_iso_of_equivalence_comp_iso {C D E : Type*} [Category* C]
    [Category* D] [Category* E] (e : C ≌ D) (F F' : D ⥤ E) (θ : e.functor ⋙ F ≅ e.functor ⋙ F') :
    Nonempty (F ≅ F') :=
  ⟨(e.invFunIdAssoc F).symm ≪≫ Functor.isoWhiskerLeft e.inverse θ ≪≫ e.invFunIdAssoc F'⟩

/-- **Siblings out of `D^b_Coh` of a reduced scheme with an ample invertible module are
isomorphic.** Let `k` be a field and `X` a reduced scheme proper over `k` with an ample invertible
module `ℒ`. If `F, F' : D^b_Coh(𝒪_X) ⥤ 𝒟` are siblings and `F` is fully faithful, then `F ≅ F'`.
A scheme projective over `k` is such a scheme
(`AlgebraicGeometry.IsProjective.isProper_and_exists_isAmple_of_isAffine`), so this contains the
first sentence of [Stacks, Tag 0G01], which is registered on its projective form
`AlgebraicGeometry.nonempty_iso_of_areSiblings_of_isProjective`. Here `𝒟` is an arbitrary
triangulated category and "siblings" is the relation of
[Stacks, Tag 0FZT] for `Coh(𝒪_X)`, read through the identification
`D^b(Coh(𝒪_X)) = D^b_Coh(𝒪_X)` of [Stacks, Tag 0FDB], as `AlgebraicGeometry.AreSiblingsCoherent`
does for `𝒟 = D^b_Coh(𝒪_Y)`.

The source proves this "via the argument given in the proof of [Stacks, Tag 0G0C]", which is
`AlgebraicGeometry.nonempty_iso_of_areSiblings_of_isReduced_of_isAmple`; the comparison functor
of [Stacks, Tag 0FDB] being an equivalence, the isomorphism on `D^b(Coh(𝒪_X))` descends to
`D^b_Coh(𝒪_X)`. The remaining sentences of the remark (that siblings are not known to be
isomorphic in general, the case of [Stacks, Tag 0G00], the reference to Noah's work and the
invitation to email) are commentary, with no mathematical content to formalize. -/
theorem _root_.AlgebraicGeometry.nonempty_iso_of_areSiblings_coherentToModulesDerivedBounded
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsReduced X]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    (F F' : (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).FullSubcategory ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (h : AreSiblings (coherentToModulesDerivedBounded X ⋙ F)
      (coherentToModulesDerivedBounded X ⋙ F'))
    (hF : Nonempty F.FullyFaithful) : Nonempty (F ≅ F') := by
  have : IsNoetherian X := isNoetherian_of_isProper_spec f
  obtain ⟨hF⟩ := hF
  have hEF : Nonempty (coherentToModulesDerivedBounded X ⋙ F).FullyFaithful :=
    ⟨(Functor.FullyFaithful.ofFullyFaithful (coherentToModulesDerivedBounded X)).comp hF⟩
  obtain ⟨θ⟩ := nonempty_iso_of_areSiblings_of_isReduced_of_isAmple f L hL
    (coherentToModulesDerivedBounded X ⋙ F) (coherentToModulesDerivedBounded X ⋙ F') h hEF
  exact nonempty_iso_of_equivalence_comp_iso (coherentToModulesDerivedBounded X).asEquivalence
    F F' θ

/-- **Siblings out of `D_perf(𝒪_X)` are isomorphic** when `X` is regular, reduced and projective
over a field and the first sibling is fully faithful: on a regular scheme `D_perf = D^b_Coh`
([Stacks, Tag 0FDC]), and siblings of exact functors `D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` are siblings
out of `D^b_Coh(𝒪_X)` ([Stacks, Tag 0FZZ]), to which
`AlgebraicGeometry.nonempty_iso_of_areSiblings_coherentToModulesDerivedBounded` applies. This is
the step of the proof of [Stacks, Tag 0G0C] which upgrades a sibling to an isomorphism. -/
theorem _root_.AlgebraicGeometry.nonempty_iso_of_areSiblingsPerfect
    {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsReduced X]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    (hX : IsRegular X) (hY : IsRegular Y) [CompactSpace X] [CompactSpace Y]
    (F F' : (perfectInModules X).FullSubcategory ⥤ (perfectInModules Y).FullSubcategory)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (h : AreSiblingsPerfect hX hY F F') (hF : Nonempty F.FullyFaithful) : Nonempty (F ≅ F') := by
  let A := ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).ge
  let B := ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded Y hY).le
  obtain ⟨hF⟩ := hF
  have hF₁ : Nonempty (A ⋙ F ⋙ B).FullyFaithful :=
    ⟨(ObjectProperty.fullyFaithfulιOfLE _).comp
      (hF.comp (ObjectProperty.fullyFaithfulιOfLE _))⟩
  obtain ⟨θ⟩ := nonempty_iso_of_areSiblings_coherentToModulesDerivedBounded f L hL
    (A ⋙ F ⋙ B) (A ⋙ F' ⋙ B) h hF₁
  have : A.EssSurj := ⟨fun P => ⟨⟨P.obj, (perfectInModules_eq_derivedCategoryBBounded X hX).le _
    P.property⟩, ⟨Iso.refl _⟩⟩⟩
  have : A.IsEquivalence := { }
  obtain ⟨θ'⟩ := nonempty_iso_of_equivalence_comp_iso A.asEquivalence (F ⋙ B) (F' ⋙ B) θ
  exact ⟨((ObjectProperty.fullyFaithfulιOfLE _).whiskeringRight _).preimageIso θ'⟩

end ReducedProjective

section Orlov

/-! ### Orlov's theorem ([Stacks, Tag 0G0C]) -/

variable (k : Type u) [Field k] (X Y : Over (Spec (.of k))) [Smooth X.hom] [IsProper X.hom]
  [Smooth Y.hom] [IsProper Y.hom]

/-- **Orlov's theorem, for `X` with an ample invertible module.** Let `k` be a field and `X`, `Y`
smooth proper schemes over `k`, with an ample invertible module `ℒ` on `X`. A scheme projective
over `k` has one (`AlgebraicGeometry.IsProjective.isProper_and_exists_isAmple_of_isAffine`), so
this contains [Stacks, Tag 0G0C], which is registered on its projective form
`AlgebraicGeometry.exists_iso_perfectFourierMukaiOver_of_isProjective`. Every `k`-linear exact
fully faithful functor
`F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` is a Fourier-Mukai functor: there is a perfect object `K` of
`D(𝒪_{X ×_k Y})` with `F ≅ Φ_K` as functors.

The proof is the source's. [Stacks, Tag 0G0B]
(`AlgebraicGeometry.exists_fourierMukai_areSiblingsPerfect`) gives a Fourier-Mukai sibling `Φ_K`
of `F`, and siblings are isomorphic by [Stacks, Tag 0FZW] once `X` is decomposed into its
positive-dimensional part, where the coherent modules have enough negative objects (the twists by
negative powers of `ℒ`), and its isolated points, where they form a semisimple category:
`AlgebraicGeometry.nonempty_iso_of_areSiblingsPerfect`, `X` being reduced as it is smooth over
a field. -/
theorem _root_.AlgebraicGeometry.exists_iso_perfectFourierMukaiOver
    (L : X.left.Modules) [Stacks.Ample.IsInvertibleModule X.left L]
    (hL : Stacks.Ample.IsAmple X.left L)
    (F : PerfectDerivedCategory X.left ⥤ PerfectDerivedCategory Y.left)
    [hFs : F.CommShift ℤ] [hFt : F.IsTriangulated]
    (hlin : letI : Linear k X.left.Modules := modulesLinear k X
      letI : Linear k Y.left.Modules := modulesLinear k Y
      F.Linear k)
    (hF : Nonempty F.FullyFaithful) :
    haveI : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
    ∃ (K : DerivedCategory (pullback X.hom Y.hom).Modules)
      (hK : IsPerfect (X := (pullback X.hom Y.hom).toRingedSpace) K),
      Nonempty (F ≅ perfectFourierMukaiOver k X Y hK) := by
  have : CompactSpace X.left := (quasiCompact_iff_compactSpace X.hom).mp inferInstance
  have : CompactSpace Y.left := (quasiCompact_iff_compactSpace Y.hom).mp inferInstance
  have : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
  obtain ⟨K, hK, hsib⟩ := exists_fourierMukai_areSiblingsPerfect k X Y F hlin hF
  have : IsReduced X.left := isReduced_of_smooth X.hom
  exact ⟨K, hK, @nonempty_iso_of_areSiblingsPerfect k _ X.left Y.left X.hom _ _ L _ hL
    (isRegular_of_smooth_over_field X.hom) (isRegular_of_smooth_over_field Y.hom) _ _
    F (perfectFourierMukaiOver k X Y hK) hFs hFt
    (commShift_fourierMukaiOn _ _ _ _ _ _) (isTriangulated_fourierMukaiOn _ _ _ _ _ _) hsib hF⟩

end Orlov

section Projective

/-! ### [Stacks, Tag 0G01] and [Stacks, Tag 0G0C] with `X` projective over `k`

The source's hypothesis "`X` projective over `k`" is the first condition of [Stacks, Tag 01W8],
`AlgebraicGeometry.IsProjective` of the structure morphism: a closed immersion over `k` into the
projective bundle `𝐏(ℰ)` of a finite-type quasi-coherent module `ℰ` on `Spec k`. By
[Stacks, Tag 0B45], (1) ⟹ (5), over the affine base `Spec k`, whose structure sheaf is ample
([Stacks, Tag 01QE]), such an `X` is proper over `k` and carries an ample invertible module, which
is what the forms above consume. -/

/-- **A projective morphism to an affine scheme is proper, and its source carries an ample
invertible module.** This is conditions (1) ⟹ (5) of [Stacks, Tag 0B45]
(`AlgebraicGeometry.isProjective_tfae_seven_of_exists_isAmple`) at an affine base, whose structure
sheaf is ample by [Stacks, Tag 01QE] (`Stacks.HProjective.exists_isAmple_of_isAffine`). -/
@[ega "III 7.7.9", sga "6 VII 3.3" "special case", sga "6 VIII 3.1" "special case"]
theorem _root_.AlgebraicGeometry.IsProjective.isProper_and_exists_isAmple_of_isAffine
    {X S : Scheme.{u}} [IsAffine S] {f : X ⟶ S} (hf : AlgebraicGeometry.IsProjective f) :
    IsProper f ∧
      ∃ (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L),
        letI : Stacks.Ample.IsInvertibleModule X L := hL
        Stacks.Ample.IsAmple X L :=
  ((isProjective_tfae_seven_of_exists_isAmple f
    (Stacks.HProjective.exists_isAmple_of_isAffine S)).out 1 5).mp hf

/-- **Stacks Project, Tag 0G01**, its first sentence. Let `k` be a field and `X` a reduced scheme
which is projective over `k` (`AlgebraicGeometry.IsProjective` of `f : X ⟶ Spec k`, the first
condition of [Stacks, Tag 01W8]). If `F, F' : D^b_Coh(𝒪_X) ⥤ 𝒟` are siblings and `F` is fully
faithful, then `F ≅ F'`. Here `𝒟` is an arbitrary triangulated category and "siblings" is the
relation of [Stacks, Tag 0FZT] for `Coh(𝒪_X)`, read through the identification
`D^b(Coh(𝒪_X)) = D^b_Coh(𝒪_X)` of [Stacks, Tag 0FDB].

A projective `k`-scheme is proper over `k` with an ample invertible module
(`AlgebraicGeometry.IsProjective.isProper_and_exists_isAmple_of_isAffine`), and for those this is
`AlgebraicGeometry.nonempty_iso_of_areSiblings_coherentToModulesDerivedBounded`, the source's
argument "via the proof of [Stacks, Tag 0G0C]". The remaining sentences of the remark (that
siblings are not known to be isomorphic in general, the case of [Stacks, Tag 0G00], the reference
to Noah's work and the invitation to email) are commentary, with no mathematical content to
formalize. -/
@[stacks 0G01 "first sentence: siblings out of D^b_Coh of a reduced projective scheme over a \
field, the first fully faithful, are isomorphic; the remaining sentences are commentary"]
theorem _root_.AlgebraicGeometry.nonempty_iso_of_areSiblings_of_isProjective
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (hf : AlgebraicGeometry.IsProjective f) [IsReduced X]
    {D : Type*} [Category* D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    (F F' : (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).FullSubcategory ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    (h : AreSiblings (coherentToModulesDerivedBounded X ⋙ F)
      (coherentToModulesDerivedBounded X ⋙ F'))
    (hF : Nonempty F.FullyFaithful) : Nonempty (F ≅ F') := by
  obtain ⟨hp, L, hL, hample⟩ := hf.isProper_and_exists_isAmple_of_isAffine
  have := hp
  let := hL
  exact nonempty_iso_of_areSiblings_coherentToModulesDerivedBounded f L hample F F' h hF

variable (k : Type u) [Field k] (X Y : Over (Spec (.of k))) [Smooth X.hom] [IsProper X.hom]
  [Smooth Y.hom] [IsProper Y.hom]

/-- **Stacks Project, Tag 0G0C** (Orlov). Let `k` be a field and `X`, `Y` smooth proper schemes
over `k` with `X` projective over `k` (`AlgebraicGeometry.IsProjective X.hom`, the first condition
of [Stacks, Tag 01W8]). Every `k`-linear exact fully faithful functor
`F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` is a Fourier-Mukai functor: there is a perfect object `K` of
`D(𝒪_{X ×_k Y})` with `F ≅ Φ_K` as functors.

A projective `k`-scheme carries an ample invertible module
(`AlgebraicGeometry.IsProjective.isProper_and_exists_isAmple_of_isAffine`), and for those this is
`AlgebraicGeometry.exists_iso_perfectFourierMukaiOver`, whose proof is the source's: a
Fourier-Mukai sibling from [Stacks, Tag 0G0B], made isomorphic to `F` by [Stacks, Tag 0FZW]. -/
@[stacks 0G0C]
theorem _root_.AlgebraicGeometry.exists_iso_perfectFourierMukaiOver_of_isProjective
    (hX : AlgebraicGeometry.IsProjective X.hom)
    (F : PerfectDerivedCategory X.left ⥤ PerfectDerivedCategory Y.left)
    [hFs : F.CommShift ℤ] [hFt : F.IsTriangulated]
    (hlin : letI : Linear k X.left.Modules := modulesLinear k X
      letI : Linear k Y.left.Modules := modulesLinear k Y
      F.Linear k)
    (hF : Nonempty F.FullyFaithful) :
    haveI : IsNoetherian Y.left := isNoetherian_of_locallyOfFiniteType Y.hom
    ∃ (K : DerivedCategory (pullback X.hom Y.hom).Modules)
      (hK : IsPerfect (X := (pullback X.hom Y.hom).toRingedSpace) K),
      Nonempty (F ≅ perfectFourierMukaiOver k X Y hK) := by
  obtain ⟨-, L, hL, hample⟩ := hX.isProper_and_exists_isAmple_of_isAffine
  let := hL
  exact exists_iso_perfectFourierMukaiOver k X Y L hample F hlin hF

end Projective

end Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

end
