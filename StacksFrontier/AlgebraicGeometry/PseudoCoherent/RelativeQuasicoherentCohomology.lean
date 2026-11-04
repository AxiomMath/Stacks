module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentReflection
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherence of the cohomology of a relatively pseudo-coherent complex

Let `f : X ⟶ S` be a morphism of schemes locally of finite type and let `E` be an object of
`D(𝒪_X)` which is `m`-pseudo-coherent relative to `S`. Then the cohomology sheaf `H^i(E)` is a
quasi-coherent `𝒪_X`-module for every `i > m`. If `E` is pseudo-coherent relative to `S`, then
`E` is an object of `D_QCoh(𝒪_X)`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isQuasicoherent_pushforward`: a sheaf of
  modules on the source of a closed immersion is quasi-coherent as soon as its direct image is.
* `AlgebraicGeometry.Scheme.Hom.isQuasicoherent_homology_of_isPseudoCoherentFrom`: **Stacks 0CSU,
  first clause.** `H^i(E)` is quasi-coherent for `i > m`.
* `AlgebraicGeometry.Scheme.Hom.isQuasicoherentDerived_of_isPseudoCoherent`: **Stacks 0CSU,
  second clause.** A relatively pseudo-coherent object lies in `D_QCoh(𝒪_X)`.

## Implementation notes

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; this is the model in which relative pseudo-coherence is stated,
and there is no global instance, so a user of these results makes the same declaration.

## References

* [The Stacks Project, Lemma 37.59.3 (0CSU)](https://stacks.math.columbia.edu/tag/0CSU)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.10.1 (08E5)](https://stacks.math.columbia.edu/tag/08E5)
* [The Stacks Project, Lemma 29.4.1 (01QY)](https://stacks.math.columbia.edu/tag/01QY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Scheme.Modules

/-- **Quasi-coherence is reflected by the direct image along a closed immersion.** If
`i : Z ⟶ X` is a closed immersion of schemes and `i_*ℱ` is a quasi-coherent `𝒪_X`-module, then
`ℱ` is a quasi-coherent `𝒪_Z`-module. -/
public theorem isQuasicoherent_of_isQuasicoherent_pushforward {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (F : Z.Modules)
    (hF : ((pushforward i).obj F).IsQuasicoherent) : F.IsQuasicoherent := by
  have := Stacks.ClosedImmersion.full_pushforward i
  have := Stacks.ClosedImmersion.faithful_pushforward i
  have hpull : ((pullback i).obj ((pushforward i).obj F)).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ i.toLRSHom.toShHom _ hF
  have hiso : IsIso ((pullbackPushforwardAdjunction i).counit.app F) := inferInstance
  exact (_root_.SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso
    (@asIso _ _ _ _ _ hiso) hpull

end Scheme.Modules

/-- If `F` is an exact functor between categories of modules and `Hⁱ(F(E))` is quasi-coherent,
then so is `F(Hⁱ(E))`. -/
private theorem isQuasicoherent_obj_homology_of_isQuasicoherent_homology_mapDerivedCategory
    {X Y : Scheme.{u}} (F : X.Modules ⥤ Y.Modules) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (E : DerivedCategory X.Modules) (i : ℤ)
    (h : ((DerivedCategory.homologyFunctor Y.Modules i).obj
      (F.mapDerivedCategory.obj E)).IsQuasicoherent) :
    (F.obj ((DerivedCategory.homologyFunctor X.Modules i).obj E)).IsQuasicoherent :=
  (_root_.SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((F.mapDerivedCategoryHomologyIso i).app E) h

/-- If the direct image of `E` along a closed immersion `e : Z ⟶ Y` is `m`-pseudo-coherent, then
`H^i(E)` is quasi-coherent for `i > m`. -/
private theorem isQuasicoherent_homology_of_isPseudoCoherentFromAfterPushforward
    {Z Y : Scheme.{u}} (e : Z ⟶ Y) [IsClosedImmersion e] (E : DerivedCategory Z.Modules)
    (m i : ℤ) (hi : m < i)
    (hE : Scheme.Modules.IsPseudoCoherentFromAfterPushforward e E m) :
    ((DerivedCategory.homologyFunctor Z.Modules i).obj E).IsQuasicoherent := by
  have hY := isQuasicoherent_homology_of_isPseudoCoherentFrom Y
    ((Scheme.Modules.pushforward e).mapDerivedCategory.obj E) m i
    ((Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff e E m).mp hE) hi
  exact Scheme.Modules.isQuasicoherent_of_isQuasicoherent_pushforward e _
    (isQuasicoherent_obj_homology_of_isQuasicoherent_homology_mapDerivedCategory _ E i hY)

namespace Scheme.Hom

/-- Let `f : X ⟶ S` be a morphism of schemes locally of finite type and let `E` be an object of
`D(𝒪_X)` which is `m`-pseudo-coherent relative to `S`. Then the cohomology sheaf `H^i(E)` is a
quasi-coherent `𝒪_X`-module for every `i > m`. -/
@[stacks 0CSU "quasi-coherence of the cohomology sheaves above the bound"]
public theorem isQuasicoherent_homology_of_isPseudoCoherentFrom {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (E : DerivedCategory X.Modules) (m i : ℤ)
    (hE : f.IsPseudoCoherentFrom E m) (hi : m < i) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent := by
  classical
  obtain ⟨ι, V, hVcov, hV⟩ := hE
  choose κ U hUcov hU using hV
  refine Stacks.Modules.isQuasicoherent_of_restrict _
    (fun q : Σ a, κ a => ((U q.1 q.2).1 : X.Opens)) ?_ fun q => ?_
  · refine SetLike.ext fun x => ⟨fun _ => trivial, fun _ => ?_⟩
    have hxS : f.base x ∈ (⨆ a, ((V a).1 : S.Opens)) := hVcov ▸ Opens.mem_top _
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp hxS
    have hxX : x ∈ (⨆ j, ((U a j).1 : X.Opens)) := (hUcov a) ▸ ha
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxX
    exact Opens.mem_iSup.mpr ⟨⟨a, j⟩, hj⟩
  · obtain ⟨hle, n, e, hce, hcomm, hAfter⟩ := hU q.1 q.2
    have := hce
    have hloc := isQuasicoherent_homology_of_isPseudoCoherentFromAfterPushforward e
      ((Scheme.Modules.restrictFunctor (U q.1 q.2).1.ι).mapDerivedCategory.obj E) m i hi hAfter
    exact isQuasicoherent_obj_homology_of_isQuasicoherent_homology_mapDerivedCategory _ E i hloc

/-- Let `f : X ⟶ S` be a morphism of schemes locally of finite type and let `E` be an object of
`D(𝒪_X)` which is pseudo-coherent relative to `S`. Then `E` is an object of `D_QCoh(𝒪_X)`, that
is, `H^i(E)` is quasi-coherent for every `i`. -/
@[stacks 0CSU "membership in the quasi-coherent derived category"]
public theorem isQuasicoherentDerived_of_isPseudoCoherent {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (E : DerivedCategory X.Modules) (hE : f.IsPseudoCoherent E) :
    DerivedCategoryB.derivedCategoryB
      (_root_.SheafOfModules.isQuasicoherent X.ringCatSheaf) E := by
  show ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent
  intro i
  exact isQuasicoherent_homology_of_isPseudoCoherentFrom f E (i - 1) i (hE (i - 1)) (by omega)

end Scheme.Hom

end AlgebraicGeometry

end
