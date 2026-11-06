module

public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairStructureSheaf
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedSectionsUnbounded
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The per-pair comparison for an arbitrary derived object on an affine pair

For `f : X ⟶ S` locally of finite type and a compatible pair of affine opens `U ⊆ f ⁻¹ᵁ V`, the
local condition of Stacks 09UI for an object `E` of `D(𝒪_X)` at that pair asks for a closed
immersion `i : U ⟶ 𝔸ⁿ_V` over `V` through which `f|_U` factors and along whose derived pushforward
`E|_U` becomes `m`-pseudo-coherent. This file identifies that condition with relative
`m`-pseudo-coherence of a complex of `Γ(X, U)`-modules, for an arbitrary `E` presented on `U` as
the sheaf associated to an object `K` of `D(Γ(X, U))`.

## Main definitions

* `AlgebraicGeometry.pushforwardTildeMapDerivedCategoryIso`: for `φ : R ⟶ S` with `Spec φ` a
  closed immersion, the two composites `D(S) ⟶ D(𝒪_{Spec S}) ⟶ D(𝒪_{Spec R})` and
  `D(S) ⟶ D(R) ⟶ D(𝒪_{Spec R})` are isomorphic.

## Main results

* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_mapDerivedCategory_tilde_iff`: an object of
  `D(R)` is `m`-pseudo-coherent exactly when the object of `D(𝒪_{Spec R})` it determines is.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_specMap_derivedTilde_iff`:
  for a closed immersion `Spec φ : Spec S ⟶ Spec R`, the local condition of Stacks 09UI at
  `Spec φ` for the sheaf associated to `K : D(S)` holds exactly when `K`, with scalars restricted
  along `φ`, is `m`-pseudo-coherent over `R`.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_derivedTilde_iff`:
  the same statement at one closed immersion `U ⟶ 𝔸ⁿ_V` of an affine open into an affine space
  over an affine open of the base.
* `AlgebraicGeometry.exists_algHom_isPseudoCoherentFromAfterPushforward_derivedTilde_iff`:
  the previous result with the presenting ring map packaged as a surjective morphism of
  `Γ(S, V)`-algebras.
* `AlgebraicGeometry.affinePairDerivedTildeComparison`: the local condition of Stacks 09UI for `E`
  at the pair holds if and only if `K` is `m`-pseudo-coherent relative to `Γ(S, V)`.
* `AlgebraicGeometry.isPseudoCoherentFromOnAffinePair_iff_derivedSectionsPseudoCoherentOn'`:
  the same statement with the right-hand side read on the derived sections `RΓ(U, E)`, which is
  the per-pair condition `AlgebraicGeometry.Scheme.Hom.DerivedSectionsPseudoCoherentOn'`.

## References

* [The Stacks Project, Lemma 36.61.6 (09VF)](https://stacks.math.columbia.edu/tag/09VF)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.17.1 (08E7)](https://stacks.math.columbia.edu/tag/08E7)
* [The Stacks Project, Lemma 26.7.3 (01I9)](https://stacks.math.columbia.edu/tag/01I9)
* [The Stacks Project, Lemma 15.82.3 (065H)](https://stacks.math.columbia.edu/tag/065H)
* [The Stacks Project, Definition 15.82.4 (065I)](https://stacks.math.columbia.edu/tag/065I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **Pushforward along `Spec φ` commutes with `M ↦ M̃` on derived categories.** Let `φ : R ⟶ S` be
a morphism of commutative rings whose spectrum is a closed immersion. Then the functor on unbounded
derived categories induced by `N ↦ Ñ` followed by pushforward along `Spec φ` is isomorphic to
restriction of scalars along `φ` followed by `M ↦ M̃`. -/
public def pushforwardTildeMapDerivedCategoryIso (R S : CommRingCat.{u}) (φ : R ⟶ S)
    [IsClosedImmersion (Spec.map φ)] :
    (tilde.functor S).mapDerivedCategory ⋙
        (Scheme.Modules.pushforward (Spec.map φ)).mapDerivedCategory ≅
      (ModuleCat.restrictScalars φ.hom).mapDerivedCategory ⋙
        (tilde.functor R).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIsoOfCompIso
      (Iso.refl (tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ))) ≪≫
    Functor.mapDerivedCategoryCongr (pushforwardTildeIso R S φ) ≪≫
    (Functor.mapDerivedCategoryCompIsoOfCompIso
      (Iso.refl (ModuleCat.restrictScalars φ.hom ⋙ tilde.functor R))).symm

namespace RingedSpace

/-- **Pseudo-coherence of a derived object and of its sheaf.** An object `K` of `D(R)` is
`m`-pseudo-coherent exactly when the object of `D(𝒪_{Spec R})` it determines under derived
sheafification is `m`-pseudo-coherent in the sheaf-level sense of Stacks 08CB. -/
@[sga "6 I 2.13" "special case"]
public theorem isPseudoCoherentFrom_mapDerivedCategory_tilde_iff {R : CommRingCat.{u}}
    (K : DerivedCategory (ModuleCat.{u} R)) (m : ℤ) :
    IsPseudoCoherentFrom (X := (Spec R).toRingedSpace)
        ((tilde.functor R).mapDerivedCategory.obj K) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom K m := by
  let M : CochainComplex (ModuleCat.{u} R) ℤ := DerivedCategory.Q.objPreimage K
  have e : DerivedCategory.Q.obj M ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have e' : DerivedCategory.Q.obj (Stacks.AffineTilde.tildeComplex M) ≅
      (tilde.functor R).mapDerivedCategory.obj K :=
    ((tilde.functor R).mapDerivedCategoryFactors.app M).symm ≪≫
      (tilde.functor R).mapDerivedCategory.mapIso e
  exact ⟨fun h ↦
      (Stacks.AffineTilde.isPseudoCoherentFrom_of_isPseudoCoherentFrom_tildeComplex M m
        (h.of_iso e'.symm)).ofIso e,
    fun h ↦
      (Stacks.AffineTilde.isPseudoCoherentFrom_tildeComplex M m (h.ofIso e.symm)).of_iso e'⟩

end RingedSpace

namespace Scheme.Modules

/-- **The sheaf-level and the module-level local condition agree at a closed immersion of
spectra.** Let
`φ : R ⟶ S` be a morphism of commutative rings whose spectrum is a closed immersion, and let `K`
be an object of `D(S)`. The local condition of Stacks 09UI at `Spec φ` for the object of
`D(𝒪_{Spec S})` determined by `K` holds for `m` if and only if `K`, with its scalars restricted
along `φ`, is `m`-pseudo-coherent over `R`. -/
public theorem isPseudoCoherentFromAfterPushforward_specMap_derivedTilde_iff
    {R S : CommRingCat.{u}} (φ : R ⟶ S) [IsClosedImmersion (Spec.map φ)]
    (K : DerivedCategory (ModuleCat.{u} S)) (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward (Spec.map φ)
        ((tilde.functor S).mapDerivedCategory.obj K) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((ModuleCat.restrictScalars φ.hom).mapDerivedCategory.obj K) m := by
  rw [isPseudoCoherentFromAfterPushforward_iff,
    ← RingedSpace.isPseudoCoherentFrom_mapDerivedCategory_tilde_iff]
  exact ⟨fun h ↦ h.of_iso ((pushforwardTildeMapDerivedCategoryIso R S φ).app K),
    fun h ↦ h.of_iso ((pushforwardTildeMapDerivedCategoryIso R S φ).app K).symm⟩

/-- **The local condition of Stacks 09UI at one closed immersion of an affine open into an affine
space is module-level relative pseudo-coherence over a polynomial ring.** Let `U` be an affine
open of `X`, let `V` be an affine open of `S`, let `i : U ⟶ 𝔸(ULift (Fin n); V)` be a closed
immersion, and let `α` be a ring map whose spectrum is `i` read through
`AlgebraicGeometry.IsAffineOpen.isoSpec` and
`AlgebraicGeometry.AffineSpace.isoSpecFinOfIso`. Then the object of `D(𝒪_U)` determined by
`K : D(Γ(X, U))` is `m`-pseudo-coherent after derived pushforward along `i` if and only if `K`,
with its scalars restricted along `α`, is `m`-pseudo-coherent over `Γ(S, V)[x₁, …, x_n]`. -/
public theorem isPseudoCoherentFromAfterPushforward_derivedTilde_iff {X S : Scheme.{u}}
    {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V)
    {n : ℕ} (i : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.toScheme) [IsClosedImmersion i]
    (α : CommRingCat.of (MvPolynomial (Fin n) Γ(S, V)) ⟶ Γ(X, U))
    (hα : Spec.map α = hU.isoSpec.inv ≫ i ≫ (AffineSpace.isoSpecFinOfIso n hV.isoSpec).hom)
    (K : DerivedCategory (ModuleCat.{u} Γ(X, U))) (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward i
        ((pushforward hU.isoSpec.inv).mapDerivedCategory.obj
          ((tilde.functor Γ(X, U)).mapDerivedCategory.obj K)) m ↔
      StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
        ((ModuleCat.restrictScalars (CommRingCat.Hom.hom α)).mapDerivedCategory.obj K) m := by
  have : IsClosedImmersion (Spec.map α) := by rw [hα]; infer_instance
  have hα' : (hU.isoSpec.inv ≫ i) ≫ (AffineSpace.isoSpecFinOfIso n hV.isoSpec).hom =
      Spec.map α := (Category.assoc _ _ _).trans hα.symm
  refine (isPseudoCoherentFromAfterPushforward_precomp_isIso_iff hU.isoSpec.inv i
    ((tilde.functor Γ(X, U)).mapDerivedCategory.obj K) m).symm.trans ?_
  refine (isPseudoCoherentFromAfterPushforward_postcomp_isIso_iff (hU.isoSpec.inv ≫ i)
    (AffineSpace.isoSpecFinOfIso n hV.isoSpec).hom _ m).symm.trans ?_
  refine (isPseudoCoherentFromAfterPushforward_congr hα' _ m).trans ?_
  exact isPseudoCoherentFromAfterPushforward_specMap_derivedTilde_iff α K m

end Scheme.Modules

/-- **One closed immersion over `V` presents `Γ(X, U)` as a quotient of a polynomial ring over
`Γ(S, V)`, and the local condition of Stacks 09UI at it is `m`-pseudo-coherence of `K` for that
presentation.** Here the algebra structure on `Γ(X, U)` is any instance whose structure map is
`f.appLE V U e`, by `halg`, and the presentation is a surjective morphism of
`Γ(S, V)`-algebras `α`. -/
public theorem exists_algHom_isPseudoCoherentFromAfterPushforward_derivedTilde_iff
    {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens}
    (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) [Algebra Γ(S, V) Γ(X, U)]
    (halg : algebraMap Γ(S, V) Γ(X, U) = (f.appLE V U e).hom)
    {n : ℕ} (i : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.toScheme) [IsClosedImmersion i]
    (hi : i ≫ (AffineSpace.over (ULift.{u} (Fin n)) V.toScheme).hom = f.resLE V U e)
    (K : DerivedCategory (ModuleCat.{u} Γ(X, U))) (m : ℤ) :
    ∃ α : MvPolynomial (Fin n) Γ(S, V) →ₐ[Γ(S, V)] Γ(X, U), Function.Surjective α ∧
      (Scheme.Modules.IsPseudoCoherentFromAfterPushforward i
          ((Scheme.Modules.pushforward hU.isoSpec.inv).mapDerivedCategory.obj
            ((tilde.functor Γ(X, U)).mapDerivedCategory.obj K)) m ↔
        StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
          ((ModuleCat.restrictScalars α.toRingHom).mapDerivedCategory.obj K) m) := by
  obtain ⟨α, hsurj, hC, hspec⟩ :=
    exists_ringHom_of_isClosedImmersion_affineSpace_resLE f hU hV e i hi
  refine ⟨{ CommRingCat.Hom.hom α with commutes' := fun r ↦ ?_ }, hsurj,
    Scheme.Modules.isPseudoCoherentFromAfterPushforward_derivedTilde_iff hU hV i α hspec K m⟩
  rw [MvPolynomial.algebraMap_eq, halg]
  exact congrArg (fun g ↦ (CommRingCat.Hom.hom g) r) hC

/-- **The local condition at an affine pair is relative pseudo-coherence of a presenting
object.** For `f : X ⟶ S`
locally of finite type, an integer `m`, a compatible pair of affine opens `U ⊆ f ⁻¹ᵁ V` and an
object `E` of `D(𝒪_X)` whose restriction to `U` is the sheaf associated to `K : D(Γ(X, U))`, the
local condition of Stacks 09UI for `E` at that pair holds if and only if `K` is
`m`-pseudo-coherent relative to `Γ(S, V)` in the sense of Stacks 065I. -/
public theorem affinePairDerivedTildeComparison {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (E : DerivedCategory X.Modules) (m : ℤ) {U : X.Opens}
    (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)
    (K : DerivedCategory (ModuleCat.{u} Γ(X, U)))
    (hEK : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E ≅
      (Scheme.Modules.pushforward hU.isoSpec.inv).mapDerivedCategory.obj
        ((tilde.functor Γ(X, U)).mapDerivedCategory.obj K)) :
    f.IsPseudoCoherentFromOnAffinePair E m ⟨U, hU⟩ ⟨V, hV⟩ e ↔
      letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
      letI : Algebra.FiniteType Γ(S, V) Γ(X, U) := algebraFiniteType_appLE f U hU V hV e
      PseudoCoherence.IsRelativelyPseudoCoherentFrom (R := Γ(S, V)) (A := Γ(X, U)) K m := by
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let _ : Algebra.FiniteType Γ(S, V) Γ(X, U) := algebraFiniteType_appLE f U hU V hV e
  have hpres := (PseudoCoherence.isPseudoCoherentFrom_polynomialPresentation_independent.{u, u, u}
    (R := Γ(S, V)) (A := Γ(X, U)) K m).1
  refine ⟨fun hL ↦ ?_, fun hR ↦ ?_⟩
  · obtain ⟨N, j, hcj, hoverj, hpc⟩ := hL
    obtain ⟨α, hα, hiff⟩ := exists_algHom_isPseudoCoherentFromAfterPushforward_derivedTilde_iff
      f hU hV e rfl j hoverj K m
    exact hpres.mp ⟨N, α, hα, hiff.mp
      ((Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff_of_iso j hEK m).mp hpc)⟩
  · obtain ⟨N, j, hcj, hoverj⟩ := exists_isClosedImmersion_affineSpace_resLE f ⟨V, hV⟩ ⟨U, hU⟩ e
    obtain ⟨α, hα, hiff⟩ := exists_algHom_isPseudoCoherentFromAfterPushforward_derivedTilde_iff
      f hU hV e rfl j hoverj K m
    exact ⟨N, j, hcj, hoverj, (Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff_of_iso j
      hEK m).mpr (hiff.mpr (hR N α hα))⟩

/-- **The local condition at an affine pair, read on the derived sections.** Under the same
presentation of `E|_U` by `K : D(Γ(X, U))`, if `K` is moreover isomorphic to the derived sections
`RΓ(U, E)` then the local condition of Stacks 09UI for `E` at the pair is the per-pair condition
`AlgebraicGeometry.Scheme.Hom.DerivedSectionsPseudoCoherentOn'` of Stacks 09VF. The derived
sections are the unbounded ones, `AlgebraicGeometry.derivedSectionsUnbounded`. -/
public theorem isPseudoCoherentFromOnAffinePair_iff_derivedSectionsPseudoCoherentOn'
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (E : DerivedCategory X.Modules)
    (m : ℤ) {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) (K : DerivedCategory (ModuleCat.{u} Γ(X, U)))
    (hEK : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E ≅
      (Scheme.Modules.pushforward hU.isoSpec.inv).mapDerivedCategory.obj
        ((tilde.functor Γ(X, U)).mapDerivedCategory.obj K))
    (hKΓ : K ≅ (derivedSectionsUnbounded X U).obj E) :
    f.IsPseudoCoherentFromOnAffinePair E m ⟨U, hU⟩ ⟨V, hV⟩ e ↔
      f.DerivedSectionsPseudoCoherentOn' E m hU hV e := by
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let _ : Algebra.FiniteType Γ(S, V) Γ(X, U) := algebraFiniteType_appLE f U hU V hV e
  exact (affinePairDerivedTildeComparison f E m hU hV e K hEK).trans
    ⟨RingHom.isRelativelyPseudoCoherentFrom_of_iso hKΓ m,
      RingHom.isRelativelyPseudoCoherentFrom_of_iso hKΓ.symm m⟩

end AlgebraicGeometry

end
