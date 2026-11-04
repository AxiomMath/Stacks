module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.PushforwardInjective

/-!
# Injective quasi-coherent modules and the direct image along a flat morphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, whose direct image and inverse image both preserve quasi-coherence and which induces a flat
morphism of small étale ringed topoi.  Then the direct image carries injective objects of
`QCoh(𝒪_X)` to injective objects of `QCoh(𝒪_Y)`.

## Main definitions

* `AlgebraicGeometry.Space.PushforwardPreservesQuasicoherence`: the direct image `f_*` carries
  quasi-coherent `𝒪_X`-modules to quasi-coherent `𝒪_Y`-modules.
* `AlgebraicGeometry.Space.quasicoherentPushforward`: the direct image
  `f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` on the categories of quasi-coherent modules, for a morphism
  whose direct image preserves quasi-coherence.
* `AlgebraicGeometry.Space.quasicoherentPullbackAdjunction`: the adjunction `f^* ⊣ f_*`
  restricted to the quasi-coherent modules.

## Main results

* `AlgebraicGeometry.Space.quasicoherentPushforwardCompιIso`: composing the restricted direct
  image with the inclusion of the quasi-coherent modules gives the inclusion followed by `f_*`.
* `AlgebraicGeometry.Space.preservesFiniteLimits_modulePullback_of_isFlat` and
  `AlgebraicGeometry.Space.preservesMonomorphisms_modulePullback_of_isFlat`: if `f` induces a
  flat morphism of small étale ringed topoi, the inverse image `f^* : Mod(𝒪_Y) ⥤ Mod(𝒪_X)` is
  left exact, and in particular transforms injections into injections.
* `AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_algebraicSpace`:
  quasi-coherence of modules on the small étale site of an algebraic space is closed under
  kernels.
* `AlgebraicGeometry.Space.preservesMonomorphisms_quasicoherentPullback_of_isFlat`: the same for
  the restriction of `f^*` to the quasi-coherent modules.
* `AlgebraicGeometry.Space.injective_quasicoherentPushforward_obj`: the direct image of an
  injective object of `QCoh(𝒪_X)` is an injective object of `QCoh(𝒪_Y)`.

## References

* [Stacks Project, Tag 09TK](https://stacks.math.columbia.edu/tag/09TK)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The direct image on the quasi-coherent modules -/

/-- The direct image `f_*` along `f : X ⟶ Y` carries quasi-coherent `𝒪_X`-modules to
quasi-coherent `𝒪_Y`-modules. -/
def PushforwardPreservesQuasicoherence (f : X ⟶ Y) : Prop :=
  ∀ F : Modules.{u, u} B S hS X.1 X.2, F.IsQuasicoherentOnSite →
    ((modulePushforward B S hS f).obj F).IsQuasicoherentOnSite

/-- A quasi-compact, quasi-separated morphism of algebraic spaces has a direct image preserving
quasi-coherence, granted `haffine`: the same conclusion for the base change of `f` along every
affine étale scheme chart of `Y`. -/
theorem pushforwardPreservesQuasicoherence_of_forall_affine (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (haffine : ∀ F : Modules.{u, u} B S hS X.1 X.2, F.IsQuasicoherentOnSite →
      ∀ V : SmallEtale B S hS Y.1,
        IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) →
        IsQuasiCompact B S hS (chartBaseChangeProjection B S hS f V).hom →
        IsQuasiSeparated B S hS (chartBaseChangeProjection B S hS f V).hom →
        ((chartLocalizedModulePushforward B S hS f V).obj
          ((moduleChartBaseChangeRestriction B S hS f V).obj F)).IsQuasicoherentOnSite) :
    PushforwardPreservesQuasicoherence B S hS f := fun F hF =>
  pushforward_isQuasicoherentOnSite_of_forall_affine B S hS f hfqc hfqs F (haffine F hF)

/-- The direct image `f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` on the categories of quasi-coherent
modules, the corestriction of `AlgebraicGeometry.Space.modulePushforward`, for a morphism whose
direct image preserves quasi-coherence. -/
noncomputable def quasicoherentPushforward (f : X ⟶ Y)
    (hf : PushforwardPreservesQuasicoherence B S hS f) :
    QuasicoherentSheaves.{u, u} B S hS X.1 X.2 ⥤ QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2 :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ modulePushforward B S hS f)
    fun F => hf F.obj F.property

/-- The direct image on quasi-coherent modules followed by the inclusion into all modules is the
inclusion followed by the direct image `f_*`. -/
noncomputable def quasicoherentPushforwardCompιIso (f : X ⟶ Y)
    (hf : PushforwardPreservesQuasicoherence B S hS f) :
    quasicoherentPushforward B S hS f hf ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ modulePushforward B S hS f :=
  ObjectProperty.liftCompιIso _ _ _

/-- The adjunction `f^* ⊣ f_*` on the quasi-coherent modules: the restriction of the adjunction
between the inverse image and the direct image of all `𝒪`-modules along the two fully faithful
inclusions of the quasi-coherent modules. -/
noncomputable def quasicoherentPullbackAdjunction (f : X ⟶ Y)
    (hpull : HasLocalInverseImagePresentations B S hS f)
    (hpush : PushforwardPreservesQuasicoherence B S hS f) :
    quasicoherentPullback B S hS f hpull ⊣ quasicoherentPushforward B S hS f hpush :=
  (modulePullbackAdjunction B S hS f).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm

/-! ### Flatness and monomorphisms -/

/-- If the morphism of small étale ringed topoi induced by `f : X ⟶ Y` is flat, that is if the
inverse-image form `f⁻¹𝒪_Y ⟶ 𝒪_X` of its structure map is a flat morphism of sheaves of rings,
then the inverse image `f^* : Mod(𝒪_Y) ⥤ Mod(𝒪_X)` is left exact. -/
theorem preservesFiniteLimits_modulePullback_of_isFlat (f : X ⟶ Y)
    (hflat : (smallEtaleRingedToposHom B S hS f).IsFlat) :
    PreservesFiniteLimits (modulePullback B S hS f) :=
  ((exactFunctor_iff _).mp (Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap
    (smallEtaleRingedToposHom B S hS f) hflat)).1

/-- The inverse image of `𝒪`-modules along a morphism of algebraic spaces inducing a flat
morphism of small étale ringed topoi transforms injections into injections. -/
theorem preservesMonomorphisms_modulePullback_of_isFlat (f : X ⟶ Y)
    (hflat : (smallEtaleRingedToposHom B S hS f).IsFlat) :
    (modulePullback B S hS f).PreservesMonomorphisms :=
  have := preservesFiniteLimits_modulePullback_of_isFlat B S hS f hflat
  ⟨fun g _ => preserves_mono_of_preservesLimit _ g⟩

/-! ### Quasi-coherence is closed under kernels -/

/-- Quasi-coherence of `𝒪_Z`-modules on the small étale site of an algebraic space `Z` is closed
under kernels. -/
instance isClosedUnderKernels_quasicoherentSheaves_algebraicSpace (Z : AlgebraicSpaces B S hS) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS Z.1 Z.2).O))).IsClosedUnderKernels :=
  isClosedUnderKernels_quasicoherentSheaves B S hS Z.1 Z.2
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS Z.1 Z.2)

/-- A monomorphism of quasi-coherent `𝒪_Z`-modules is a monomorphism of all `𝒪_Z`-modules. -/
theorem mono_hom_of_mono_quasicoherentSheaves (Z : AlgebraicSpaces B S hS)
    {A C : QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2} (a : A ⟶ C) [Mono a] : Mono a.hom := by
  have hK := ObjectProperty.prop_kernel (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O))) a.hom
    A.property C.property
  have hzero : (ObjectProperty.homMk (kernel.ι a.hom) :
      (⟨kernel a.hom, hK⟩ : QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2) ⟶ A) = 0 :=
    zero_of_comp_mono a (ObjectProperty.hom_ext _ (by
      rw [ObjectProperty.zero_hom]
      exact kernel.condition a.hom))
  have hι : (ObjectProperty.homMk (kernel.ι a.hom) :
      (⟨kernel a.hom, hK⟩ : QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2) ⟶ A).hom = 0 := by
    rw [hzero, ObjectProperty.zero_hom]
  exact Preadditive.mono_of_kernel_zero hι

/-- The inverse image on quasi-coherent modules along a morphism of algebraic spaces inducing a
flat morphism of small étale ringed topoi transforms injections into injections. -/
theorem preservesMonomorphisms_quasicoherentPullback_of_isFlat (f : X ⟶ Y)
    (hpull : HasLocalInverseImagePresentations B S hS f)
    (hflat : (smallEtaleRingedToposHom B S hS f).IsFlat) :
    (quasicoherentPullback B S hS f hpull).PreservesMonomorphisms := by
  have := preservesMonomorphisms_modulePullback_of_isFlat B S hS f hflat
  refine ⟨fun {A C} a _ => ?_⟩
  have : Mono a.hom := mono_hom_of_mono_quasicoherentSheaves B S hS Y a
  exact (ObjectProperty.ι _).mono_of_mono_map
    (inferInstanceAs (Mono ((modulePullback B S hS f).map a.hom)))

/-! ### Injectivity of the direct image -/

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` inducing a flat morphism of small
étale ringed topoi, whose inverse image and direct image both preserve quasi-coherence.  If `J` is
an injective object of `QCoh(𝒪_X)` then `f_*J` is an injective object of `QCoh(𝒪_Y)`. -/
theorem injective_quasicoherentPushforward_obj (f : X ⟶ Y)
    (hflat : (smallEtaleRingedToposHom B S hS f).IsFlat)
    (hpull : HasLocalInverseImagePresentations B S hS f)
    (hpush : PushforwardPreservesQuasicoherence B S hS f)
    (J : QuasicoherentSheaves.{u, u} B S hS X.1 X.2) [Injective J] :
    Injective ((quasicoherentPushforward B S hS f hpush).obj J) :=
  have := preservesMonomorphisms_quasicoherentPullback_of_isFlat B S hS f hpull hflat
  have := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (quasicoherentPullbackAdjunction B S hS f hpull hpush)
  Functor.injective_obj _ _

end AlgebraicGeometry.Space

end
