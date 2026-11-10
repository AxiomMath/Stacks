module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubquotientNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Coherence of the higher direct images along a proper morphism of algebraic spaces

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over a scheme `S` with `Y` locally
Noetherian and let `𝓕` be a coherent `𝒪_X`-module.  Stacks 08AR asserts that `R^i f_*𝓕` is a
coherent `𝒪_Y`-module in every degree.  It is obtained here from the dévissage of coherent
modules on `X`, Stacks 08AN, applied to the property that all higher direct images of a module
are coherent: the two-out-of-three condition and the finite-sum condition of that dévissage are
proved for this property, granted quasi-coherence of the higher direct images, which is
Stacks 0720.

## Main definitions

* `AlgebraicGeometry.Space.HasCoherentHigherDirectImages` is the property `𝓟` of an
  `𝒪_X`-module that all of its higher direct images along `f` are coherent.
* `AlgebraicGeometry.Space.QuasicoherentHigherDirectImages` is the hypothesis `h0720`:
  every higher direct image of a coherent `𝒪_X`-module along `f` is quasi-coherent.
* `AlgebraicGeometry.Space.CoherentDevissage` is the dévissage principle of Stacks 08AN,
  stated for one property, with its three conditions as premises.
* `AlgebraicGeometry.Space.CoherentDevissageIntegralWitness` is the third of those
  conditions: at every reduced closed subspace with irreducible point set, a coherent module
  with full support whose direct image has the property.

## Main results

* `AlgebraicGeometry.Space.isCoherent_X₂_of_exact_of_isQuasicoherentOnSite`: the middle term
  of an exact sequence of `𝒪_F`-modules whose outer terms are coherent and whose middle term
  is quasi-coherent is coherent, on a locally Noetherian algebraic space.
* `AlgebraicGeometry.Space.hasCoherentHigherDirectImages_twoOutOfThree`: **the
  two-out-of-three condition of Stacks 08AN** for the property above, granted `h0720`.
* `AlgebraicGeometry.Space.hasCoherentHigherDirectImages_finiteSum`: **the finite-sum
  condition of Stacks 08AN** for the property above, granted `h0720`.
* `AlgebraicGeometry.Space.isCoherent_rightDerived_modulePushforward_of_isProper`:
  **Stacks 08AR**, with Stacks 0720, Stacks 08AN and the integral-subspace condition of the
  source's proof carried as explicit hypotheses.

## Implementation notes

**What is carried and what is proved.**  Three hypotheses are carried by the last result and
each is a cited result other than Stacks 08AR itself.

* `h0720` is quasi-coherence of the higher direct images, Stacks 0720.  This development does
  not prove it:
  `StacksFrontier/AlgebraicGeometry/Spaces/HigherPushforwardQuasicoherentReduction.lean` carries out
  the reduction to an affine base and records which of the three inputs of the remaining step are
  missing.
* `h08AN` is the dévissage of Stacks 08AN for the property at hand, with the local
  Noetherianity of `X` in place of the source's Noetherianity: the source reaches a Noetherian
  `X` by first localizing étale on `Y`, and the étale-local test for coherence of a higher
  direct image is not available here, there being no transfer of coherence along the chart
  equivalence of Stacks 04M0 in either direction.  Local Noetherianity of `X` *is* discharged,
  from properness and Stacks 04ZK.
* `hwitness` is the third condition of the source's proof: at a reduced closed subspace with
  irreducible point set, a coherent module with full support whose direct image to `X` has the
  property.  The source produces it from Chow's lemma for spaces, Stacks 089J, the eventual
  vanishing of Stacks 08AQ and the projective case Stacks 02O4; a finite surjective scheme
  cover, Stacks 09YC, serves the same purpose.

The two remaining conditions of the dévissage are proved.  The two-out-of-three condition comes
from the long exact sequence of right derived functors in the object variable,
`Stacks.Cohomology.RightDerivedDelta.exists_delta_exact_composableArrows₅`, together with
Stacks 07UC for an extension and Stacks 07UD for a quasi-coherent submodule; it is exactly
there that `h0720` is consumed, since Stacks 07UD asks for quasi-coherence of the subobject.
The finite-sum condition is the same Stacks 07UD applied to the split monomorphism which a
finite sum of copies of a module provides.

**The module universe** is the universe `u` of the schemes and not a free one, because
`AlgebraicGeometry.Space.modulePushforward` exists only there.

**The two local priority raises** are the ones
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteDirectImageCoherence.lean` documents: with the
module-universe-`max u v r w` instances of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/CohomologyOfModules.lean` in the import
closure, search for `Abelian` and `EnoughInjectives` on the modules at module universe `u`
commits to them and then fails on the universe constraint.

## References

* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 07UC](https://stacks.math.columbia.edu/tag/07UC)
* [Stacks Project, Tag 07UD](https://stacks.math.columbia.edu/tag/07UD)
* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 09YC](https://stacks.math.columbia.edu/tag/09YC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The middle term of an exact sequence -/

/-- **The middle term of an exact sequence of `𝒪_F`-modules with coherent outer terms is
coherent as soon as it is quasi-coherent**, on a locally Noetherian algebraic space.

The image of the first map is a quotient of the coherent first term and the coimage of the
second is a submodule of the coherent third term, so both are coherent by Stacks 07UD; the
middle term is an extension of the second by the first, hence coherent by Stacks 07UC. -/
theorem isCoherent_X₂_of_exact_of_isQuasicoherentOnSite
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))]
    {T : ShortComplex (Modules.{u, u} B S hS F hF)} (hT : T.Exact)
    (h₁ : IsCoherent B S hS F hF T.X₁) (h₃ : IsCoherent B S hS F hF T.X₃)
    (h₂ : T.X₂.IsQuasicoherentOnSite) : IsCoherent B S hS F hF T.X₂ := by
  have : T.X₁.IsQuasicoherentOnSite := h₁.toIsQuasicoherentOnSite
  have : T.X₃.IsQuasicoherentOnSite := h₃.toIsQuasicoherentOnSite
  have : (cokernel T.f).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_cokernel_unconditional B S hS F hF T.f
  have : (Abelian.image T.f).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_kernel_of_quasicoherent B S hS F hF (cokernel.π T.f)
  have : (kernel T.g).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_kernel_of_quasicoherent B S hS F hF T.g
  have : (Abelian.coimage T.g).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_cokernel_unconditional B S hS F hF (kernel.ι T.g)
  have himage : IsCoherent B S hS F hF (Abelian.image T.f) :=
    isCoherent_of_epi_of_isQuasicoherentOnSite B S hS F hF (Abelian.factorThruImage T.f)
      inferInstance h₁
  have hcoimage : IsCoherent B S hS F hF (Abelian.coimage T.g) :=
    isCoherent_of_mono_of_isQuasicoherentOnSite B S hS F hF (Abelian.factorThruCoimage T.g)
      inferInstance h₃
  let T' := ShortComplex.mk (Abelian.image.ι T.f) T.g (Abelian.image_ι_comp_eq_zero T.zero)
  exact isCoherent_X₂_of_shortExact B S hS F hF
    (T := ShortComplex.mk T'.f (Abelian.coimage.π T'.g) (Abelian.comp_coimage_π_eq_zero T'.zero))
    ⟨T'.exact_iff_exact_coimage_π.1 (T.exact_iff_exact_image_ι.1 hT)⟩ himage hcoimage

variable {X Y : AlgebraicSpaces B S hS}

/-! ### The property and the quasi-coherence hypothesis -/

/-- The property `𝓟` of the dévissage: all higher direct images of an `𝒪_X`-module along
`f : X ⟶ Y` are coherent `𝒪_Y`-modules. -/
def HasCoherentHigherDirectImages (f : X ⟶ Y) (G : Modules.{u, u} B S hS X.1 X.2) : Prop :=
  ∀ n : ℕ,
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsCoherent B S hS Y.1 Y.2 (((modulePushforward B S hS f).rightDerived n).obj G)

/-- The hypothesis `h0720`: every higher direct image of a coherent `𝒪_X`-module along
`f : X ⟶ Y` is quasi-coherent.

For a quasi-compact and quasi-separated `f` this is Stacks 0720, whose reduction to an affine
base is carried out in
`StacksFrontier/AlgebraicGeometry/Spaces/HigherPushforwardQuasicoherentReduction.lean`. -/
def QuasicoherentHigherDirectImages (f : X ⟶ Y) : Prop :=
  ∀ G : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 G → ∀ n : ℕ,
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    (((modulePushforward B S hS f).rightDerived n).obj G).IsQuasicoherentOnSite

/-! ### The conditions of the dévissage

The first condition is `AlgebraicGeometry.Space.TwoOutOfThreeCoherent`, stated in
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentDevissage.lean`; the second and third are stated
here. -/

/-- The second condition of Stacks 08AN: if the property holds for a direct sum of `r ≥ 1`
copies of a coherent `𝒪_X`-module then it holds for that module.  The sum is presented as a
colimit of a fan of `r` copies of the module, so that no choice of coproduct is fixed. -/
def CoherentDevissageFiniteSum (X : AlgebraicSpaces B S hS)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop) : Prop :=
  ∀ (G C : Modules.{u, u} B S hS X.1 X.2) (r : ℕ), IsCoherent B S hS X.1 X.2 G → 0 < r →
    ∀ ι : ∀ _ : Fin r, G ⟶ C, Nonempty (IsColimit (Cofan.mk C ι)) → P C → P G

/-- The third condition of Stacks 08AN: for every closed subspace `Z` of `X` which is reduced
and whose point set is irreducible there is a coherent `𝒪_Z`-module with full support whose
direct image along the closed immersion `Z ⟶ X` has the property.

This renders the source's "a coherent module on `X` whose scheme theoretic support is `Z`": for
a reduced `Z` a coherent `𝒪_Z`-module with support all of `|Z|` is exactly such a module. -/
def CoherentDevissageIntegralWitness (X : AlgebraicSpaces B S hS)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop) : Prop :=
  ∀ (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z),
    HasEtaleLocalProperty B S hS Z.toFunctor (fun V : Scheme.{u} ↦ IsReduced V) →
    @IrreducibleSpace (points B S hS Z.toFunctor) (pointTopology B S hS Z.toFunctor) →
    ∃ H : Modules.{u, u} B S hS Z.toFunctor hZ.1,
      IsCoherent B S hS Z.toFunctor hZ.1 H ∧
      supportOfSheaf B S hS Z.toFunctor ((SheafOfModules.toSheaf _).obj H) = Set.univ ∧
      P ((modulePushforward B S hS
        (ObjectProperty.homMk Z.ι :
          (⟨Z.toFunctor, hZ.1⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj H)

/-- **The dévissage of coherent modules, Stacks 08AN**, for one property `P` of `𝒪_X`-modules:
over its three conditions, `P` holds for every coherent `𝒪_X`-module.

The source assumes `X` Noetherian; here the premise is local Noetherianity of `X`, which is
what properness over a locally Noetherian base supplies. -/
def CoherentDevissage (X : AlgebraicSpaces B S hS)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop) : Prop :=
  HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V) →
  TwoOutOfThreeCoherent B S hS X P →
  CoherentDevissageFiniteSum B S hS X P →
  CoherentDevissageIntegralWitness B S hS X P →
  ∀ G : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 G → P G

/-! ### The two conditions that are proved -/

/-- **The two-out-of-three condition of Stacks 08AN for the higher direct images**, granted
quasi-coherence of those direct images.

The long exact sequence of the right derived functors of `f_*` in the object variable puts each
of the three terms' degree-`n` direct image between direct images of the other two, in degree
`n` or `n + 1`; `AlgebraicGeometry.Space.isCoherent_X₂_of_exact_of_isQuasicoherentOnSite`
closes each case, and in degree zero the sequence begins with a monomorphism, where Stacks 07UD
applies directly. -/
theorem hasCoherentHigherDirectImages_twoOutOfThree (f : X ⟶ Y)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (h0720 : QuasicoherentHigherDirectImages B S hS f) :
    TwoOutOfThreeCoherent B S hS X (HasCoherentHigherDirectImages B S hS f) := by
  have : Fact (HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :=
    ⟨hY⟩
  have : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X.1 X.2) :=
    isGrothendieckAbelian_modules B S hS X.1 X.2
  have : EnoughInjectives (Modules.{u, u} B S hS X.1 X.2) := inferInstance
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  intro E hE h₁ h₂ h₃
  obtain ⟨delta, hmono, hwin⟩ :=
    Stacks.Cohomology.RightDerivedDelta.exists_delta_exact_composableArrows₅ hE
      (modulePushforward B S hS f)
  refine ⟨fun H₁ H₃ n ↦ ?_, fun H₂ H₃ n ↦ ?_, fun H₁ H₂ n ↦ ?_⟩
  · exact isCoherent_X₂_of_exact_of_isQuasicoherentOnSite B S hS Y.1 Y.2
      ((hwin n).exact 0) (H₁ n) (H₃ n) (h0720 E.X₂ h₂ n)
  · cases n with
    | zero =>
      have := hmono
      exact isCoherent_of_mono_of_isQuasicoherentOnSite B S hS Y.1 Y.2
        (((modulePushforward B S hS f).rightDerived 0).map E.f) (h0720 E.X₁ h₁ 0) (H₂ 0)
    | succ n =>
      exact isCoherent_X₂_of_exact_of_isQuasicoherentOnSite B S hS Y.1 Y.2
        ((hwin n).exact 2) (H₃ n) (H₂ (n + 1)) (h0720 E.X₁ h₁ (n + 1))
  · exact isCoherent_X₂_of_exact_of_isQuasicoherentOnSite B S hS Y.1 Y.2
      ((hwin n).exact 1) (H₂ n) (H₁ (n + 1)) (h0720 E.X₃ h₃ n)

/-- **The finite-sum condition of Stacks 08AN for the higher direct images**, granted
quasi-coherence of those direct images.

A fan of `r ≥ 1` copies of `G` with colimit `C` makes `G` a retract of `C`, so each
`R^n f_*G ⟶ R^n f_*C` is a split monomorphism and Stacks 07UD applies. -/
theorem hasCoherentHigherDirectImages_finiteSum (f : X ⟶ Y)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (h0720 : QuasicoherentHigherDirectImages B S hS f) :
    CoherentDevissageFiniteSum B S hS X (HasCoherentHigherDirectImages B S hS f) := by
  have : Fact (HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :=
    ⟨hY⟩
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  intro G C r hG hr ι hc hC n
  obtain ⟨hc⟩ := hc
  set H := (modulePushforward B S hS f).rightDerived n
  have hfac : ι ⟨0, hr⟩ ≫ Cofan.IsColimit.desc hc (fun _ ↦ 𝟙 G) = 𝟙 G :=
    Cofan.IsColimit.fac hc (fun _ ↦ 𝟙 G) ⟨0, hr⟩
  have : Mono (H.map (ι ⟨0, hr⟩)) :=
    mono_of_mono_fac (show H.map (ι ⟨0, hr⟩) ≫ H.map (Cofan.IsColimit.desc hc fun _ ↦ 𝟙 G)
      = 𝟙 (H.obj G) by rw [← H.map_comp, hfac, H.map_id])
  exact isCoherent_of_mono_of_isQuasicoherentOnSite B S hS Y.1 Y.2 (H.map (ι ⟨0, hr⟩))
    (h0720 G hG n) (hC n)

/-! ### Stacks 08AR -/

/-- **Stacks 08AR**, with the three cited inputs of the source's proof carried as hypotheses.
Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` with `Y` locally Noetherian
and let `𝓕` be a coherent `𝒪_X`-module.  Then `R^i f_*𝓕` is a coherent `𝒪_Y`-module for every
`i`.

The dévissage `h08AN` of Stacks 08AN is applied to the property that all higher direct images
are coherent.  Its local Noetherianity premise is discharged from properness by Stacks 04ZK;
its two-out-of-three and finite-sum conditions are
`AlgebraicGeometry.Space.hasCoherentHigherDirectImages_twoOutOfThree` and
`AlgebraicGeometry.Space.hasCoherentHigherDirectImages_finiteSum`, proved above from the long
exact sequence of the higher direct images together with Stacks 07UC and Stacks 07UD and
consuming the quasi-coherence hypothesis `h0720` of Stacks 0720; its integral-subspace
condition is `hwitness` and is not proved. -/
@[stacks 08AR "conditional on three cited results carried as explicit hypotheses: Stacks 0720 \
as h0720 (quasi-coherence of the higher direct images), Stacks 08AN as h08AN (the devissage of \
coherent modules, with its Noetherian hypothesis on X relaxed to the local Noetherianity that \
properness supplies) and the third condition of the source's devissage as hwitness (a coherent \
module with full support on each reduced closed subspace with irreducible point set, whose \
direct image has coherent higher direct images -- the source gets it from Stacks 089J, 08AQ \
and 02O4, and Stacks 09YC serves as well). The other two conditions of Stacks 08AN are PROVED \
here for this property, and so is the local Noetherianity of X"]
theorem isCoherent_rightDerived_modulePushforward_of_isProper (f : X ⟶ Y)
    (hf : IsProper B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (h0720 : QuasicoherentHigherDirectImages B S hS f)
    (h08AN : CoherentDevissage B S hS X (HasCoherentHigherDirectImages B S hS f))
    (hwitness :
      CoherentDevissageIntegralWitness B S hS X (HasCoherentHigherDirectImages B S hS f))
    (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsCoherent B S hS Y.1 Y.2 (((modulePushforward B S hS f).rightDerived i).obj F) :=
  h08AN (isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2 Y.2 f.hom hf.2.1.1 hY)
    (hasCoherentHigherDirectImages_twoOutOfThree B S hS f hY h0720)
    (hasCoherentHigherDirectImages_finiteSum B S hS f hY h0720) hwitness F hF i

end AlgebraicGeometry.Space

end
