module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.LinearAlgebra.Complex.Module
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Reduction
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.ClosedImmersionPushforward
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairLocality
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SideCondition
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TruncatedPolynomial
public import StacksFrontier.Homology.PseudoCoherent.Relative.Finite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative pseudo-coherence along a morphism that is a closed immersion on reductions

Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes locally of finite type and let
`i : X ⟶ Y` be a morphism over `S` whose induced map on reductions is a closed immersion. Then an
object `E` of `D(𝒪_X)` is `m`-pseudo-coherent relative to `S` if and only if its derived
pushforward `Ri_*E` is `m`-pseudo-coherent relative to `S`.

The same equivalence holds when `i` only induces a homeomorphism of `X` with a closed subset of
`Y`, granted either a comparison of charts over each compatible pair of affine opens, or the
pseudo-coherence of the pushforward of the structure sheaf in two charts.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsClosedImmersionOnReductions`: the induced map on reductions is
  a closed immersion, spelled as a commuting square with the canonical immersions of the
  reductions.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward_of_reductionImmersion`:
  the equivalence for a morphism which is a closed immersion on reductions.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward_of_chartComparison`:
  the equivalence for a morphism which is a homeomorphism onto a closed subset, granted a
  comparison of charts at every compatible pair of affine opens.
* `isPseudoCoherentFrom_iff_derivedPushforward_of_structureSheafCharts`, in the namespace
  `AlgebraicGeometry.Scheme.Hom`: the equivalence for a morphism which is a homeomorphism onto a
  closed subset, granted that the pushforward of the structure sheaf is pseudo-coherent in two
  charts.
* `AlgebraicGeometry.Scheme.Hom.IsClosedImmersionOnReductions.universallyClosed` and
  `AlgebraicGeometry.Scheme.Hom.IsClosedImmersionOnReductions.isFinite`: a morphism which is a
  closed immersion on reductions is universally closed, and is finite as soon as it is locally of
  finite type.
* `isPseudoCoherentFromAfterPushforward_iff_of_isPseudoCoherent_unit`, in the namespace
  `AlgebraicGeometry.Scheme.Modules`: the local conditions at two closed embeddings on spaces
  along which the pushforward of the structure sheaf is pseudo-coherent agree.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_restrict_pushforward_iff`:
  the local condition at a chart `b` for the restriction of `i_*E` is the local condition at
  `(i ∣_ U) ≫ b` for the restriction of `E`.
* `AlgebraicGeometry.Scheme.Hom.not_forall_isClosedImmersionOnReductions`: a morphism locally of
  finite type which is a homeomorphism onto a closed subset need not be a closed immersion on
  reductions.

## Implementation notes

Stacks 09VG as printed asks only that `i` induce a homeomorphism of `X` with a closed subset of
`Y`, and so stated it is false, by
`AlgebraicGeometry.Scheme.Hom.not_forall_isPseudoCoherentFrom_iff_derivedPushforward`. The tag is
attached to the statement whose hypothesis is that `i` be a closed immersion on reductions, that
is, that `A/rad(A) → B/rad(B)` be surjective on affine opens, with `rad` the nilradical.

The right-hand side of the main result uses the total derived pushforward
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward`; for `i` a closed embedding
on spaces it agrees with the functor `i_*` induces on derived categories, by
`Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory`.

The derived categories are those of `CategoryTheory.HasDerivedCategory.standard`, made a local
instance.

## References

* [The Stacks Project, Lemma 36.61.6 (09VG)](https://stacks.math.columbia.edu/tag/09VG)
* [The Stacks Project, Lemma 36.61.7 (09UK)](https://stacks.math.columbia.edu/tag/09UK)
* [The Stacks Project, Lemma 36.61.8 (09VF)](https://stacks.math.columbia.edu/tag/09VF)
* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Lemma 36.60.9 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Lemma 29.11.3 (04DE)](https://stacks.math.columbia.edu/tag/04DE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### A morphism which is a closed immersion on reductions -/

/-- A morphism `i : X ⟶ Y` of schemes *is a closed immersion on reductions* if there is a closed
immersion `j` of the reduction of `X` into the reduction of `Y` commuting with `i` and the
canonical immersions of the reductions, the reductions being the closed subschemes cut out by the
nilradicals, `AlgebraicGeometry.Scheme.nilradical`. -/
public abbrev Scheme.Hom.IsClosedImmersionOnReductions {X Y : Scheme.{u}} (i : X ⟶ Y) : Prop :=
  ∃ j : X.nilradical.subscheme ⟶ Y.nilradical.subscheme,
    IsClosedImmersion j ∧
      j ≫ Y.nilradical.subschemeι = X.nilradical.subschemeι ≫ i

/-- A morphism which is a closed immersion on reductions is a closed embedding of topological
spaces. -/
public theorem Scheme.Hom.IsClosedImmersionOnReductions.isClosedEmbedding {X Y : Scheme.{u}}
    {i : X ⟶ Y} (hred : i.IsClosedImmersionOnReductions) :
    Topology.IsClosedEmbedding i.base := by
  obtain ⟨j, _, hji⟩ := hred
  set eX := X.homeomorphNilradicalSubscheme with hex
  set eY := Y.homeomorphNilradicalSubscheme with hey
  have hmap : i.base = eY ∘ j.base ∘ eX.symm := by
    ext x
    have h := congrArg (fun k : X.nilradical.subscheme ⟶ Y => k (eX.symm x)) hji
    change eY (j (eX.symm x)) = i (eX (eX.symm x)) at h
    simpa [hex, hey] using h.symm
  rw [hmap]
  exact eY.isClosedEmbedding.comp (j.isClosedEmbedding.comp eX.symm.isClosedEmbedding)

/-- A morphism which is a closed immersion on reductions is an affine morphism. -/
@[ega "II 1.2.2" "more general", ega "II 1.6.2" "more general"]
public theorem Scheme.Hom.IsClosedImmersionOnReductions.isAffineHom {X Y : Scheme.{u}}
    {i : X ⟶ Y} (hred : i.IsClosedImmersionOnReductions) : IsAffineHom i :=
  isAffineHom_of_isInducing i hred.isClosedEmbedding.isInducing
    hred.isClosedEmbedding.isClosed_range

/-- The immersion of the closed subscheme cut out by the nilradical is surjective. -/
public instance Scheme.surjective_subschemeι_nilradical (Z : Scheme.{u}) :
    Surjective Z.nilradical.subschemeι := by
  rw [surjective_iff]
  intro z
  rw [← Set.mem_range, Z.nilradical.range_subschemeι, Scheme.support_nilradical]
  trivial

/-- A morphism which is a closed immersion on reductions is universally closed. -/
@[ega "II 5.4.9" "special case", ega "IV 2.4.3" "(vi), special case"]
public theorem Scheme.Hom.IsClosedImmersionOnReductions.universallyClosed {X Y : Scheme.{u}}
    {i : X ⟶ Y} (hred : i.IsClosedImmersionOnReductions) : UniversallyClosed i := by
  obtain ⟨j, _, hji⟩ := hred
  have : UniversallyClosed (X.nilradical.subschemeι ≫ i) := by
    rw [← hji]; infer_instance
  exact UniversallyClosed.of_comp_surjective X.nilradical.subschemeι i

/-- A morphism locally of finite type which is a closed immersion on reductions is finite. -/
@[ega "II 1.2.2" "more general", ega "II 1.6.2" "more general"]
public theorem Scheme.Hom.IsClosedImmersionOnReductions.isFinite {X Y : Scheme.{u}}
    {i : X ⟶ Y} [LocallyOfFiniteType i] (hred : i.IsClosedImmersionOnReductions) :
    IsFinite i := by
  have := hred.isAffineHom
  have := IsSeparated.of_isAffineHom i
  have := hred.universallyClosed
  have : LocallyQuasiFinite i :=
    LocallyQuasiFinite.of_injective hred.isClosedEmbedding.injective
  have : IsProper i := ⟨⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite i

/-- If `i : X ⟶ Y` is a closed immersion on reductions and `U` is an affine open of `Y`, every
section of `𝒪_X` over `i⁻¹U` differs from the image of a section of `𝒪_Y` over `U` by a nilpotent.
-/
public theorem Scheme.Hom.IsClosedImmersionOnReductions.exists_isNilpotent_sub_app
    {X Y : Scheme.{u}} {i : X ⟶ Y} (hred : i.IsClosedImmersionOnReductions)
    (U : Y.affineOpens) (b : Γ(X, i ⁻¹ᵁ U.1)) :
    ∃ a : Γ(Y, U.1), IsNilpotent (b - (i.app U.1).hom a) := by
  have : IsAffineHom i := hred.isAffineHom
  obtain ⟨j, _, hji⟩ := hred
  have hpre : (j ≫ Y.nilradical.subschemeι) ⁻¹ᵁ U.1 =
      (X.nilradical.subschemeι ≫ i) ⁻¹ᵁ U.1 := by rw [hji]
  have hδ := ConcreteCategory.bijective_of_isIso
    (X.nilradical.subscheme.presheaf.map (eqToHom hpre).op)
  have hcs : Function.Surjective ((j ≫ Y.nilradical.subschemeι).app U.1) :=
    (j ≫ Y.nilradical.subschemeι).app_surjective U.1 U.2
  rw [Scheme.Hom.congr_app hji U.1] at hcs
  have hsurj : Function.Surjective ((X.nilradical.subschemeι ≫ i).app U.1) := by
    intro y
    obtain ⟨x, hx⟩ := hcs (X.nilradical.subscheme.presheaf.map (eqToHom hpre).op y)
    rw [CommRingCat.comp_apply] at hx
    exact ⟨x, hδ.1 hx⟩
  obtain ⟨a, ha⟩ := hsurj (X.nilradical.subschemeι.app (i ⁻¹ᵁ U.1) b)
  refine ⟨a, ?_⟩
  have hb : X.nilradical.subschemeι.app (i ⁻¹ᵁ U.1) ((i.app U.1).hom a) =
      X.nilradical.subschemeι.app (i ⁻¹ᵁ U.1) b := ha
  have hker : b - (i.app U.1).hom a ∈
      X.nilradical.ideal ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ := by
    rw [← X.nilradical.ker_subschemeι_app ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩]
    show X.nilradical.subschemeι.app (i ⁻¹ᵁ U.1) (b - (i.app U.1).hom a) = 0
    rw [map_sub, hb, sub_self]
  rw [← mem_nilradical]
  show b - (i.app U.1).hom a ∈ (⊥ : Ideal Γ(X, i ⁻¹ᵁ U.1)).radical
  simpa [Scheme.nilradical] using hker

/-! ### Being a closed immersion on reductions is strictly stronger -/

/-- The morphism `Spec ℂ ⟶ Spec ℝ` is not a closed immersion on reductions. -/
public theorem Scheme.Hom.not_isClosedImmersionOnReductions_specMap_complex :
    ¬ (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))).IsClosedImmersionOnReductions := by
  intro hred
  obtain ⟨a, ha⟩ := hred.exists_isNilpotent_sub_app
    ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of ℝ))⟩
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom Complex.I)
  have hsub : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom Complex.I)
      - (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
        (((Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))).appTop).hom a) = 0 := by
    rw [← map_sub]
    exact (ha.map _).eq_zero
  rw [CommRingCat.hom_inv_apply, sub_eq_zero] at hsub
  have hnat := congrArg (fun k : Γ(Spec (CommRingCat.of ℝ), ⊤) ⟶ CommRingCat.of ℂ => k.hom a)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap ℝ ℂ)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat
  rw [hnat] at hsub
  have him := congrArg Complex.im hsub
  simp at him

/-- Not every morphism of schemes locally of finite type which is a closed embedding of topological
spaces is a closed immersion on reductions. -/
public theorem Scheme.Hom.not_forall_isClosedImmersionOnReductions :
    ¬ ∀ {X Y : Scheme.{0}} (i : X ⟶ Y), LocallyOfFiniteType i →
        Topology.IsClosedEmbedding i.base → i.IsClosedImmersionOnReductions := by
  intro h
  refine Scheme.Hom.not_isClosedImmersionOnReductions_specMap_complex
    (h _ ?_ ?_)
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr (Module.Finite.finiteType ℂ)
  · have hb : ⇑(Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ))).base =
        ⇑(Homeomorph.homeomorphOfUnique ↥(Spec (CommRingCat.of ℂ))
          ↥(Spec (CommRingCat.of ℝ))) :=
      funext fun x => Subsingleton.elim _ _
    rw [hb]
    exact (Homeomorph.homeomorphOfUnique _ _).isClosedEmbedding

end AlgebraicGeometry

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### Finite free algebras and relative pseudo-coherence -/

/-- A finite free `R`-module, placed in degree zero, is pseudo-coherent relative to `R` as a
complex of `R`-modules. -/
public theorem isRelativelyPseudoCoherent_single_of_finiteFree {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Free R M] :
    IsRelativelyPseudoCoherent (R := R) (A := R)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) := by
  set e := MvPolynomial.isEmptyAlgEquiv R (Fin 0) with he
  set F := ModuleCat.restrictScalars.{u} e.toRingHom with hF
  have h1 : RingHomInvPair e.toRingHom e.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv e.toRingEquiv
  have h2 : RingHomInvPair e.symm.toRingHom e.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm e.toRingEquiv
  let eM : F.obj M ≃ₛₗ[e.toRingHom] M :=
    { __ := Equiv.refl M
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have : Module.Free (MvPolynomial (Fin 0) R) (F.obj M) := Module.Free.of_equiv eM.symm
  have : Module.Finite (MvPolynomial (Fin 0) R) (F.obj M) :=
    Module.Finite.of_surjective eM.symm.toLinearMap eM.symm.surjective
  intro m
  refine (isPseudoCoherentFrom_polynomialPresentation_independent _ m).1.mp
    ⟨0, e.toAlgHom, e.surjective, ?_⟩
  exact StacksDraft.PseudoCoherence.IsPseudoCoherentFrom.ofIso
    (isPseudoCoherentFrom_single_of_finiteFree (F.obj M) m)
    ((F.mapDerivedCategorySingleFunctor 0).app M).symm

/-- For `A` finite free over `R`, `A` with its scalars restricted to `R` is a finite free
`R`-module. -/
private theorem finite_free_restrictScalars_self (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.Finite R A] [Module.Free R A] :
    Module.Finite R ((ModuleCat.restrictScalars.{u} (algebraMap R A)).obj (ModuleCat.of A A)) ∧
      Module.Free R ((ModuleCat.restrictScalars.{u} (algebraMap R A)).obj (ModuleCat.of A A)) := by
  let eA : A ≃ₗ[R] (ModuleCat.restrictScalars.{u} (algebraMap R A)).obj (ModuleCat.of A A) :=
    { __ := Equiv.refl A
      map_add' := by intros; rfl
      map_smul' := fun r x => Algebra.smul_def r x }
  exact ⟨Module.Finite.equiv eA, Module.Free.of_equiv eA⟩

/-- A finite free `R`-algebra `A` is pseudo-coherent relative to `R` as a module over itself. -/
public theorem isModuleRelativelyPseudoCoherent_self_of_finiteFree {R A : Type u} [CommRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] [Module.Free R A] :
    letI : Algebra.FiniteType R A := Module.Finite.finiteType A
    IsModuleRelativelyPseudoCoherent (R := R) (A := A) A := by
  have : Algebra.FiniteType R A := Module.Finite.finiteType A
  set F := ModuleCat.restrictScalars.{u} (algebraMap R A) with hF
  obtain ⟨_, _⟩ := finite_free_restrictScalars_self R A
  have h := isRelativelyPseudoCoherent_single_of_finiteFree (F.obj (ModuleCat.of A A))
  refine (isRelativelyPseudoCoherentFrom_and_isRelativelyPseudoCoherent_iff_restrictScalars
    (R := R) (A := R) (B := A)
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) 0).2.mpr ?_
  intro m n p hp
  exact StacksDraft.PseudoCoherence.IsPseudoCoherentFrom.ofIso (h m n p hp)
    ((ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategory.mapIso
      ((F.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of A A)).symm)

/-- For `A` finite free over `R` and `p : R[x_1, …, x_n] ↠ A` a surjection of `R`-algebras, `A`
with its scalars restricted along `p` is an `m`-pseudo-coherent `R[x_1, …, x_n]`-module for every
`m`. -/
public theorem isPseudoCoherentFrom_single_restrictScalars_self_of_finiteFree {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A] [Module.Free R A] (n : ℕ)
    (p : MvPolynomial (Fin n) R →ₐ[R] A) (hp : Function.Surjective p) (m : ℤ) :
    StacksDraft.PseudoCoherence.IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) R)) 0).obj
        ((ModuleCat.restrictScalars.{u} p.toRingHom).obj (ModuleCat.of A A))) m := by
  have : Algebra.FiniteType R A := Module.Finite.finiteType A
  exact StacksDraft.PseudoCoherence.IsPseudoCoherentFrom.ofIso
    (isModuleRelativelyPseudoCoherent_self_of_finiteFree (R := R) (A := A) m n p hp)
    (((ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of A A))

end PseudoCoherence

namespace AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### The local condition along an exact pushforward -/

/-- For a morphism `i` along which the pushforward of modules is exact, the local condition
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward` holds at `i` for `E`
exactly when the pushforward of `E` along `i` on derived categories is `m`-pseudo-coherent. -/
public theorem isPseudoCoherentFromAfterPushforward_iff_of_exact {X Y : Scheme.{u}}
    (i : X ⟶ Y) [PreservesFiniteColimits (pushforward i)] (E : DerivedCategory X.Modules)
    (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward i E m ↔
      RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace)
        ((pushforward i).mapDerivedCategory.obj E) m := by
  have hW : (HomologicalComplex.quasiIso X.Modules (ComplexShape.up ℤ)).IsInvertedBy
      ((pushforward i).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) := by
    intro K L φ hφ
    have : QuasiIso φ := hφ
    dsimp
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  constructor
  · rintro ⟨K, ⟨e⟩, c, hc, hpc⟩
    have iso : c.pt ≅ (pushforward i).mapDerivedCategory.obj E :=
      hc.isoObjOfInverts hW ≪≫ ((pushforward i).mapDerivedCategoryFactors.app K).symm ≪≫
        (pushforward i).mapDerivedCategory.mapIso e
    exact hpc.of_iso iso
  · intro h
    have iso : (pushforward i).mapDerivedCategory.obj E ≅
        ((pushforward i).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).obj
          (DerivedCategory.Q.objPreimage E) :=
      (pushforward i).mapDerivedCategory.mapIso
          (DerivedCategory.Q.objObjPreimageIso E).symm ≪≫
        (pushforward i).mapDerivedCategoryFactors.app _
    exact ⟨DerivedCategory.Q.objPreimage E, ⟨DerivedCategory.Q.objObjPreimageIso E⟩,
      Functor.valueCoconeOfInverts _ _ hW _,
      Functor.isRightDerivedValueAt_valueCoconeOfInverts _ _ hW _, h.of_iso iso⟩

/-- Let `k : Y ⟶ Z` be a closed embedding on spaces along which the pushforward of modules is
exact. If `k_*𝒪_Y` is a pseudo-coherent `𝒪_Z`-module, then `k_*A` is `m`-pseudo-coherent exactly
when `A` is. -/
public theorem isPseudoCoherentFrom_pushforward_iff_of_isClosedEmbedding {Y Z : Scheme.{u}}
    (k : Y ⟶ Z) (hk : Topology.IsClosedEmbedding k.base)
    [PreservesFiniteColimits (pushforward k)]
    (hO : RingedSpace.IsPseudoCoherent (X := Z.toRingedSpace)
      ((DerivedCategory.singleFunctor Z.Modules 0).obj
        ((pushforward k).obj (SheafOfModules.unit Y.ringCatSheaf))))
    (m : ℤ) (A : DerivedCategory Y.Modules) :
    RingedSpace.IsPseudoCoherentFrom (X := Z.toRingedSpace)
        ((pushforward k).mapDerivedCategory.obj A) m ↔
      RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace) A m :=
  ⟨RingedSpace.isPseudoCoherentFrom_of_derivedPushforwardOXMod k.toLRSHom.toShHom hk hO m A,
    RingedSpace.isPseudoCoherentFrom_derivedPushforwardOXMod k.toLRSHom.toShHom hk hO m A⟩

/-- The pushforward of modules along a closed embedding on spaces preserves finite colimits. -/
private theorem preservesFiniteColimits_pushforward_of_isClosedEmbedding {X Y : Scheme.{u}}
    (k : X ⟶ Y) (hk : Topology.IsClosedEmbedding k.base) :
    PreservesFiniteColimits (pushforward k) :=
  Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward k.toLRSHom.toShHom hk

/-- For `a : X ⟶ T` and `b : T ⟶ P` closed embeddings on spaces, the local condition at `a ≫ b` for
`E` is the pseudo-coherence of `b_*a_*E`. -/
private theorem isPseudoCoherentFromAfterPushforward_comp_iff_pushforward {X T P : Scheme.{u}}
    (a : X ⟶ T) (b : T ⟶ P) (ha : Topology.IsClosedEmbedding a.base)
    (hb : Topology.IsClosedEmbedding b.base) [PreservesFiniteColimits (pushforward a)]
    [PreservesFiniteColimits (pushforward b)] (E : DerivedCategory X.Modules) (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward (a ≫ b) E m ↔
      RingedSpace.IsPseudoCoherentFrom (X := P.toRingedSpace)
        ((pushforward b).mapDerivedCategory.obj ((pushforward a).mapDerivedCategory.obj E)) m := by
  have := preservesFiniteColimits_pushforward_of_isClosedEmbedding (a ≫ b) (hb.comp ha)
  rw [isPseudoCoherentFromAfterPushforward_iff_of_exact (a ≫ b) E m]
  have e := (Functor.mapDerivedCategoryCompIsoOfCompIso (pushforwardComp a b)).app E
  exact ⟨fun h => h.of_iso e.symm, fun h => h.of_iso e⟩

/-- If `a : X ⟶ T` and `b : T ⟶ P` are closed embeddings on spaces and `b_*𝒪_T` is pseudo-coherent,
the local condition `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward` holds
at `a ≫ b` exactly when it holds at `a`. -/
public theorem isPseudoCoherentFromAfterPushforward_comp_iff_of_isClosedEmbedding
    {X T P : Scheme.{u}} (a : X ⟶ T) (b : T ⟶ P) (ha : Topology.IsClosedEmbedding a.base)
    (hb : Topology.IsClosedEmbedding b.base)
    (hO : RingedSpace.IsPseudoCoherent (X := P.toRingedSpace)
      ((DerivedCategory.singleFunctor P.Modules 0).obj
        ((pushforward b).obj (SheafOfModules.unit T.ringCatSheaf))))
    (E : DerivedCategory X.Modules) (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward (a ≫ b) E m ↔
      IsPseudoCoherentFromAfterPushforward a E m := by
  have := preservesFiniteColimits_pushforward_of_isClosedEmbedding a ha
  have := preservesFiniteColimits_pushforward_of_isClosedEmbedding b hb
  rw [isPseudoCoherentFromAfterPushforward_comp_iff_pushforward a b ha hb E m,
    isPseudoCoherentFromAfterPushforward_iff_of_exact a E m,
    isPseudoCoherentFrom_pushforward_iff_of_isClosedEmbedding b hb hO m]

/-! ### The pushforward of the structure sheaf of a finite free algebra -/

/-- For `A` finite free over `R`, the pushforward of `𝒪_{Spec A}` along `Spec A ⟶ Spec R`, placed
in degree zero, is a pseudo-coherent object of `D(𝒪_{Spec R})`. -/
public theorem isPseudoCoherent_pushforward_unit_specMap_algebraMap_of_finiteFree {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A] [Module.Free R A] :
    RingedSpace.IsPseudoCoherent (X := (Spec (CommRingCat.of R)).toRingedSpace)
      ((DerivedCategory.singleFunctor (Spec (CommRingCat.of R)).Modules 0).obj
        ((pushforward (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj
          (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf))) := by
  refine isPseudoCoherent_singleFunctor_pushforward_unit_specMap
    (CommRingCat.ofHom (algebraMap R A)) fun m => ?_
  set F := ModuleCat.restrictScalars.{u} (CommRingCat.ofHom (algebraMap R A)).hom with hF
  obtain ⟨_, _⟩ := PseudoCoherence.finite_free_restrictScalars_self R A
  exact PseudoCoherence.isPseudoCoherentFrom_single_of_finiteFree (F.obj (ModuleCat.of A A)) m

/-- For `A` finite free over `R` and `p : R[x_1, …, x_n] ↠ A` a surjection of `R`-algebras, the
pushforward of `𝒪_{Spec A}` along `Spec p`, placed in degree zero, is a pseudo-coherent object of
`D(𝒪_{𝔸ⁿ_{Spec R}})`. -/
public theorem isPseudoCoherent_pushforward_unit_specMap_of_finiteFree {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A] [Module.Free R A] (n : ℕ)
    (p : MvPolynomial (Fin n) R →ₐ[R] A) (hp : Function.Surjective p) :
    RingedSpace.IsPseudoCoherent
      (X := (Spec (CommRingCat.of (MvPolynomial (Fin n) R))).toRingedSpace)
      ((DerivedCategory.singleFunctor
          (Spec (CommRingCat.of (MvPolynomial (Fin n) R))).Modules 0).obj
        ((pushforward (Spec.map (CommRingCat.ofHom p.toRingHom))).obj
          (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf))) :=
  isPseudoCoherent_singleFunctor_pushforward_unit_specMap (CommRingCat.ofHom p.toRingHom)
    fun m => PseudoCoherence.isPseudoCoherentFrom_single_restrictScalars_self_of_finiteFree
      n p hp m

/-- For `a : X ⟶ T` and `b : T ⟶ P` closed embeddings on spaces, the local condition
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward` at `a ≫ b` for `E` is the
local condition at `b` for `a_*E`. -/
public theorem isPseudoCoherentFromAfterPushforward_precomp_iff_of_isClosedEmbedding
    {X T P : Scheme.{u}} (a : X ⟶ T) (b : T ⟶ P) (ha : Topology.IsClosedEmbedding a.base)
    (hb : Topology.IsClosedEmbedding b.base) [PreservesFiniteColimits (pushforward a)]
    (E : DerivedCategory X.Modules) (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward (a ≫ b) E m ↔
      IsPseudoCoherentFromAfterPushforward b ((pushforward a).mapDerivedCategory.obj E) m := by
  have := preservesFiniteColimits_pushforward_of_isClosedEmbedding b hb
  rw [isPseudoCoherentFromAfterPushforward_comp_iff_pushforward a b ha hb E m,
    isPseudoCoherentFromAfterPushforward_iff_of_exact b _ m]

/-! ### Charts with a pseudo-coherent structure sheaf -/

/-- If `b : X ⟶ P` is a closed embedding on spaces and `b_*𝒪_X` is a pseudo-coherent `𝒪_P`-module,
the local condition `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward` at `b`
for `E` holds exactly when it holds at the identity of `X`. -/
public theorem isPseudoCoherentFromAfterPushforward_iff_id_of_isPseudoCoherent_unit
    {X P : Scheme.{u}} (b : X ⟶ P) (hb : Topology.IsClosedEmbedding b.base)
    (hO : RingedSpace.IsPseudoCoherent (X := P.toRingedSpace)
      ((DerivedCategory.singleFunctor P.Modules 0).obj
        ((pushforward b).obj (SheafOfModules.unit X.ringCatSheaf))))
    (E : DerivedCategory X.Modules) (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward b E m ↔
      IsPseudoCoherentFromAfterPushforward (𝟙 X) E m := by
  have h := isPseudoCoherentFromAfterPushforward_comp_iff_of_isClosedEmbedding (𝟙 X) b
    (Scheme.Hom.isClosedEmbedding (𝟙 X)) hb hO E m
  rwa [Category.id_comp] at h

/-- Let `b : X ⟶ P` and `b' : X ⟶ P'` be closed embeddings on spaces along which the pushforward of
`𝒪_X` is a pseudo-coherent module. Then the local conditions
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward` at `b` and at `b'` agree,
for every object `E` of `D(𝒪_X)` and every integer `m`. -/
public theorem isPseudoCoherentFromAfterPushforward_iff_of_isPseudoCoherent_unit
    {X P P' : Scheme.{u}} (b : X ⟶ P) (b' : X ⟶ P')
    (hb : Topology.IsClosedEmbedding b.base) (hb' : Topology.IsClosedEmbedding b'.base)
    (hO : RingedSpace.IsPseudoCoherent (X := P.toRingedSpace)
      ((DerivedCategory.singleFunctor P.Modules 0).obj
        ((pushforward b).obj (SheafOfModules.unit X.ringCatSheaf))))
    (hO' : RingedSpace.IsPseudoCoherent (X := P'.toRingedSpace)
      ((DerivedCategory.singleFunctor P'.Modules 0).obj
        ((pushforward b').obj (SheafOfModules.unit X.ringCatSheaf))))
    (E : DerivedCategory X.Modules) (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward b E m ↔
      IsPseudoCoherentFromAfterPushforward b' E m :=
  (isPseudoCoherentFromAfterPushforward_iff_id_of_isPseudoCoherent_unit b hb hO E m).trans
    (isPseudoCoherentFromAfterPushforward_iff_id_of_isPseudoCoherent_unit b' hb' hO' E m).symm

/-! ### The two maps out of a truncated polynomial algebra -/

/-- For nonzero exponents `N`, and `a` a closed embedding on spaces into
`Spec (R[x_1, …, x_r]/(x_j^{N j}))`, the local condition
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward` at the composite of `a`
with the closed immersion into `Spec R[x_1, …, x_r]` agrees with the local condition at the
composite of `a` with the structure map to `Spec R`. -/
public theorem isPseudoCoherentFromAfterPushforward_truncatedPolynomial_iff (R : Type u)
    [CommRing R] (r : ℕ) (N : Fin r → ℕ) (hN : ∀ j, N j ≠ 0) {X : Scheme.{u}}
    (a : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin r) R ⧸
      MvPolynomial.variablePowerIdeal R N)))
    (ha : Topology.IsClosedEmbedding a.base) (E : DerivedCategory X.Modules) (m : ℤ) :
    IsPseudoCoherentFromAfterPushforward
        (a ≫ Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (MvPolynomial.variablePowerIdeal R N)))) E m ↔
      IsPseudoCoherentFromAfterPushforward
        (a ≫ Spec.map (CommRingCat.ofHom (algebraMap R
          (MvPolynomial (Fin r) R ⧸ MvPolynomial.variablePowerIdeal R N)))) E m := by
  have hfin := MvPolynomial.finite_quotient_variablePowerIdeal R N
  have hfree := MvPolynomial.free_quotient_variablePowerIdeal R N
  have hb : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (MvPolynomial.variablePowerIdeal R N)))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hc : Topology.IsClosedEmbedding
      (Spec.map (CommRingCat.ofHom (algebraMap R
        (MvPolynomial (Fin r) R ⧸ MvPolynomial.variablePowerIdeal R N)))).base :=
    (PrimeSpectrum.isHomeomorph_comap_truncatedPolynomial R N hN).isClosedEmbedding
  refine (isPseudoCoherentFromAfterPushforward_comp_iff_of_isClosedEmbedding a _ ha
      hb.isClosedEmbedding ?_ E m).trans
    (isPseudoCoherentFromAfterPushforward_comp_iff_of_isClosedEmbedding a _ ha hc ?_ E m).symm
  · exact isPseudoCoherent_pushforward_unit_specMap_of_finiteFree r
      (Ideal.Quotient.mkₐ R (MvPolynomial.variablePowerIdeal R N))
      Ideal.Quotient.mk_surjective
  · exact isPseudoCoherent_pushforward_unit_specMap_algebraMap_of_finiteFree

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### Charts in an affine space over an affine base -/

/-- A surjection of `Γ(S, ⊤)`-algebras `p : Γ(S, ⊤)[x_1, …, x_r] ↠ B` gives a closed immersion
`j : Spec B ⟶ 𝔸ʳ_S` over `S` such that the local conditions
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward` at `Spec p` and at `j`
agree. -/
public theorem exists_isClosedImmersion_affineSpace_of_surjective (S : Scheme.{u}) [IsAffine S]
    (B : Type u) [CommRing B] [Algebra Γ(S, ⊤) B] (r : ℕ)
    (p : MvPolynomial (Fin r) Γ(S, ⊤) →ₐ[Γ(S, ⊤)] B) (hp : Function.Surjective p) :
    ∃ j : Spec (CommRingCat.of B) ⟶ AffineSpace (ULift.{u} (Fin r)) S,
      IsClosedImmersion j ∧
      j ≫ (AffineSpace.over (ULift.{u} (Fin r)) S).hom =
        Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) B)) ≫ S.isoSpec.inv ∧
      ∀ (E : DerivedCategory (Spec (CommRingCat.of B)).Modules) (m : ℤ),
        Scheme.Modules.IsPseudoCoherentFromAfterPushforward
          (Spec.map (CommRingCat.ofHom p.toRingHom)) E m ↔
        Scheme.Modules.IsPseudoCoherentFromAfterPushforward j E m := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom p.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hp
  refine ⟨Spec.map (CommRingCat.ofHom p.toRingHom) ≫ (AffineSpace.isoSpecFin r S).inv,
    inferInstance, ?_, fun E m =>
      (Scheme.Modules.isPseudoCoherentFromAfterPushforward_postcomp_isIso_iff _
        (AffineSpace.isoSpecFin r S).inv E m).symm⟩
  rw [Category.assoc, AffineSpace.isoSpecFin_inv_over, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext x
  exact p.commutes x

/-- A surjection `p : P[y_1, …, y_r] ↠ B` of algebras over `P = Γ(S, ⊤)[x_1, …, x_n]` gives a
closed immersion `j : Spec B ⟶ 𝔸^{r+n}_S` over `S` such that the local conditions
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward` at `Spec p` and at `j`
agree. -/
public theorem exists_isClosedImmersion_affineSpace_of_surjective_iterated (S : Scheme.{u})
    [IsAffine S] (B : Type u) [CommRing B] [Algebra Γ(S, ⊤) B] (n r : ℕ)
    [Algebra (MvPolynomial (Fin n) Γ(S, ⊤)) B]
    [IsScalarTower Γ(S, ⊤) (MvPolynomial (Fin n) Γ(S, ⊤)) B]
    (p : MvPolynomial (Fin r) (MvPolynomial (Fin n) Γ(S, ⊤)) →ₐ[MvPolynomial (Fin n) Γ(S, ⊤)] B)
    (hp : Function.Surjective p) :
    ∃ j : Spec (CommRingCat.of B) ⟶ AffineSpace (ULift.{u} (Fin (r + n))) S,
      IsClosedImmersion j ∧
      j ≫ (AffineSpace.over (ULift.{u} (Fin (r + n))) S).hom =
        Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) B)) ≫ S.isoSpec.inv ∧
      ∀ (E : DerivedCategory (Spec (CommRingCat.of B)).Modules) (m : ℤ),
        Scheme.Modules.IsPseudoCoherentFromAfterPushforward
          (Spec.map (CommRingCat.ofHom p.toRingHom)) E m ↔
        Scheme.Modules.IsPseudoCoherentFromAfterPushforward j E m := by
  set e := (MvPolynomial.renameEquiv Γ(S, ⊤) finSumFinEquiv.symm).trans
    (MvPolynomial.sumAlgEquiv Γ(S, ⊤) (Fin r) (Fin n)) with hedef
  obtain ⟨j, hj, hcomp, hpc⟩ := exists_isClosedImmersion_affineSpace_of_surjective S B (r + n)
    ((p.restrictScalars Γ(S, ⊤)).comp e.toAlgHom) (hp.comp e.surjective)
  refine ⟨j, hj, hcomp, fun E m => ?_⟩
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom p.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hp
  set eS := Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op with heS
  have he : Spec.map (CommRingCat.ofHom p.toRingHom) ≫ eS.hom =
      Spec.map (CommRingCat.ofHom ((p.restrictScalars Γ(S, ⊤)).comp e.toAlgHom).toRingHom) := by
    rw [heS]
    show Spec.map (CommRingCat.ofHom p.toRingHom) ≫
      Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom) = _
    rw [← Spec.map_comp]
    rfl
  have hc := (Scheme.Modules.isPseudoCoherentFromAfterPushforward_postcomp_isIso_iff
    (Spec.map (CommRingCat.ofHom p.toRingHom)) eS.hom E m).symm
  rw [he] at hc
  exact hc.trans (hpc E m)

/-! ### Comparing the two charts of an affine thickening -/

/-- Let `R ↠ A` be surjective and let `B` be an `A`-algebra generated by elements differing from
elements of `A` by nilpotents of order `N j`. Then there is a surjection `p : R[x_1, …, x_r] ↠ B`
such that the local conditions
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward` at `Spec p` and at
`Spec B ⟶ Spec R` agree. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_polynomial_comparison
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B] (hA : Function.Surjective (algebraMap R A)) {r : ℕ}
    (Q : Algebra.Generators A B (Fin r)) (a : Fin r → A) (N : Fin r → ℕ) (hN : ∀ j, N j ≠ 0)
    (hpow : ∀ j, (Q.val j - algebraMap A B (a j)) ^ N j = 0) :
    ∃ p : MvPolynomial (Fin r) R →ₐ[R] B, Function.Surjective p ∧
      ∀ (E : DerivedCategory (Spec (CommRingCat.of B)).Modules) (m : ℤ),
        Scheme.Modules.IsPseudoCoherentFromAfterPushforward
            (Spec.map (CommRingCat.ofHom p.toRingHom)) E m ↔
          Scheme.Modules.IsPseudoCoherentFromAfterPushforward
            (Spec.map (CommRingCat.ofHom (algebraMap R B))) E m := by
  obtain ⟨ψ, hψ⟩ := MvPolynomial.exists_surjective_truncatedPolynomialMap R hA Q a N hpow
  refine ⟨ψ.comp (Ideal.Quotient.mkₐ R (MvPolynomial.variablePowerIdeal R N)),
    hψ.comp Ideal.Quotient.mk_surjective, fun E m => ?_⟩
  have hkc : IsClosedImmersion (Spec.map (CommRingCat.ofHom ψ.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hψ
  have h₁ : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (MvPolynomial.variablePowerIdeal R N))) =
      Spec.map (CommRingCat.ofHom
        (ψ.comp (Ideal.Quotient.mkₐ R (MvPolynomial.variablePowerIdeal R N))).toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  have h₂ : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (MvPolynomial (Fin r) R ⧸ MvPolynomial.variablePowerIdeal R N))) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact ψ.commutes x
  have h := Scheme.Modules.isPseudoCoherentFromAfterPushforward_truncatedPolynomial_iff R r N hN
    (Spec.map (CommRingCat.ofHom ψ.toRingHom)) hkc.isClosedEmbedding E m
  rwa [h₁, h₂] at h

/-- If `R ↠ A` is surjective, `B` is a finite-type `A`-algebra and every element of `B` differs
from an element of `A` by a nilpotent, then there is a surjection `p : R[x_1, …, x_r] ↠ B` for
which the local conditions `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward`
at `Spec p` and at `Spec B ⟶ Spec R` agree. -/
public theorem exists_isPseudoCoherentFromAfterPushforward_polynomial_comparison_of_nilpotent
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B] [Algebra.FiniteType A B]
    (hA : Function.Surjective (algebraMap R A))
    (hred : ∀ b : B, ∃ a : A, IsNilpotent (b - algebraMap A B a)) :
    ∃ (r : ℕ) (p : MvPolynomial (Fin r) R →ₐ[R] B), Function.Surjective p ∧
      ∀ (E : DerivedCategory (Spec (CommRingCat.of B)).Modules) (m : ℤ),
        Scheme.Modules.IsPseudoCoherentFromAfterPushforward
            (Spec.map (CommRingCat.ofHom p.toRingHom)) E m ↔
          Scheme.Modules.IsPseudoCoherentFromAfterPushforward
            (Spec.map (CommRingCat.ofHom (algebraMap R B))) E m := by
  obtain ⟨r, N, Q, a, hpow⟩ := Algebra.exists_generators_nilpotent_sub_algebraMap hred
  have hpow' (j : Fin r) : (Q.val j - algebraMap A B (a j)) ^ (N + 1) = 0 := by
    rw [pow_succ, hpow, zero_mul]
  exact ⟨r, exists_isPseudoCoherentFromAfterPushforward_polynomial_comparison hA Q a
    (fun _ => N + 1) (fun _ => Nat.succ_ne_zero N) hpow'⟩

/-- A morphism of affine schemes which is locally of finite type is of finite type on global
sections. -/
private theorem finiteType_appTop_hom {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] : f.appTop.hom.FiniteType := by
  have heq : f.appLE ⊤ ⊤ le_top = f.appTop := by
    simpa [Scheme.Hom.appTop] using (Scheme.Hom.appLE_eq_app (f := f) (U := (⊤ : Y.Opens)))
  rw [← heq]
  exact f.finiteType_appLE (isAffineOpen_top Y) (isAffineOpen_top X) le_top

/-- Let `i : X ⟶ Y` and `g : Y ⟶ S` be morphisms of affine schemes locally of finite type with `i`
a closed embedding on spaces along which every section of `𝒪_X` differs from a section of `𝒪_Y` by
a nilpotent. Then there are closed immersions `a : X ⟶ 𝔸ᵏ_S` and `b : Y ⟶ 𝔸ⁿ_S` over `S` for which
the local condition `AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward` holds
at `a` for `E` exactly when it holds at `b` for `i_*E`. -/
@[sga "6 VIII 1.4" "more general"]
public theorem exists_isClosedImmersion_affineSpace_comparison {X Y S : Scheme.{u}} [IsAffine X]
    [IsAffine Y] [IsAffine S] (i : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFiniteType i]
    [LocallyOfFiniteType g] (hi : Topology.IsClosedEmbedding i.base)
    [PreservesFiniteColimits (Scheme.Modules.pushforward i)]
    (hnil : ∀ b : Γ(X, ⊤), ∃ a : Γ(Y, ⊤), IsNilpotent (b - i.appTop.hom a)) :
    ∃ (n k : ℕ) (a : X ⟶ AffineSpace (ULift.{u} (Fin k)) S)
      (b : Y ⟶ AffineSpace (ULift.{u} (Fin n)) S),
      IsClosedImmersion a ∧ IsClosedImmersion b ∧
      a ≫ (AffineSpace.over (ULift.{u} (Fin k)) S).hom = i ≫ g ∧
      b ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = g ∧
      ∀ (E : DerivedCategory X.Modules) (m : ℤ),
        Scheme.Modules.IsPseudoCoherentFromAfterPushforward a E m ↔
        Scheme.Modules.IsPseudoCoherentFromAfterPushforward b
          ((Scheme.Modules.pushforward i).mapDerivedCategory.obj E) m := by
  let _ : Algebra Γ(S, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  let _ : Algebra Γ(Y, ⊤) Γ(X, ⊤) := i.appTop.hom.toAlgebra
  let _ : Algebra Γ(S, ⊤) Γ(X, ⊤) := (i.appTop.hom.comp g.appTop.hom).toAlgebra
  have : IsScalarTower Γ(S, ⊤) Γ(Y, ⊤) Γ(X, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.FiniteType Γ(S, ⊤) Γ(Y, ⊤) :=
    RingHom.finiteType_algebraMap.mp (finiteType_appTop_hom g)
  have : Algebra.FiniteType Γ(Y, ⊤) Γ(X, ⊤) :=
    RingHom.finiteType_algebraMap.mp (finiteType_appTop_hom i)
  obtain ⟨n, ⟨P⟩⟩ := (Algebra.FiniteType.iff_exists_generators
    (R := Γ(S, ⊤)) (S := Γ(Y, ⊤))).mp inferInstance
  let _ : Algebra P.Ring Γ(X, ⊤) :=
    ((algebraMap Γ(Y, ⊤) Γ(X, ⊤)).comp (algebraMap P.Ring Γ(Y, ⊤))).toAlgebra
  have : IsScalarTower P.Ring Γ(Y, ⊤) Γ(X, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(S, ⊤) P.Ring Γ(X, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show i.appTop.hom (g.appTop.hom x) =
        i.appTop.hom (algebraMap P.Ring Γ(Y, ⊤) (MvPolynomial.C x))
      refine congrArg i.appTop.hom ?_
      show algebraMap Γ(S, ⊤) Γ(Y, ⊤) x =
        algebraMap P.Ring Γ(Y, ⊤) (algebraMap Γ(S, ⊤) P.Ring x)
      exact IsScalarTower.algebraMap_apply Γ(S, ⊤) P.Ring Γ(Y, ⊤) x
  obtain ⟨r, p, hp, hpc⟩ :=
    exists_isPseudoCoherentFromAfterPushforward_polynomial_comparison_of_nilpotent
      P.algebraMap_surjective hnil
  obtain ⟨a, ha, hac, hap⟩ := exists_isClosedImmersion_affineSpace_of_surjective_iterated S
    Γ(X, ⊤) n r p hp
  obtain ⟨b, hb, hbc, hbp⟩ := exists_isClosedImmersion_affineSpace_of_surjective S Γ(Y, ⊤) n
    (IsScalarTower.toAlgHom Γ(S, ⊤) P.Ring Γ(Y, ⊤)) P.algebraMap_surjective
  have ht : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap P.Ring Γ(Y, ⊤)))) :=
    IsClosedImmersion.spec_of_surjective _ P.algebraMap_surjective
  have hsquare : X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap P.Ring Γ(X, ⊤))) =
      i ≫ Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap P.Ring Γ(Y, ⊤))) := by
    rw [← Scheme.isoSpec_hom_naturality_assoc, ← Spec.map_comp]
    rfl
  have hs : Topology.IsClosedEmbedding
      (Spec.map (CommRingCat.ofHom (algebraMap P.Ring Γ(X, ⊤)))).base := by
    have he : Spec.map (CommRingCat.ofHom (algebraMap P.Ring Γ(X, ⊤))) = X.isoSpec.inv ≫ i ≫
        Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap P.Ring Γ(Y, ⊤))) := by
      rw [← hsquare, Iso.inv_hom_id_assoc]
    rw [he]
    exact ht.isClosedEmbedding.comp (Y.isoSpec.hom.isClosedEmbedding.comp
      (hi.comp X.isoSpec.inv.isClosedEmbedding))
  refine ⟨n, r + n, X.isoSpec.hom ≫ a, Y.isoSpec.hom ≫ b, inferInstance, inferInstance, ?_, ?_,
    fun E m => ?_⟩
  · rw [Category.assoc, hac]
    show X.isoSpec.hom ≫ Spec.map (g.appTop ≫ i.appTop) ≫ S.isoSpec.inv = _
    rw [← Scheme.Hom.comp_appTop, Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id,
      Category.comp_id]
  · rw [Category.assoc, hbc]
    show Y.isoSpec.hom ≫ Spec.map g.appTop ≫ S.isoSpec.inv = g
    rw [Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  · have hx := Scheme.Modules.isPseudoCoherentFromAfterPushforward_precomp_iff_of_isClosedEmbedding
      X.isoSpec.hom a X.isoSpec.hom.isClosedEmbedding ha.isClosedEmbedding E m
    have hy := Scheme.Modules.isPseudoCoherentFromAfterPushforward_precomp_iff_of_isClosedEmbedding
      Y.isoSpec.hom b Y.isoSpec.hom.isClosedEmbedding hb.isClosedEmbedding
      ((Scheme.Modules.pushforward i).mapDerivedCategory.obj E) m
    refine hx.trans ((hap _ m).symm.trans ((hpc _ m).trans ?_))
    refine (Scheme.Modules.isPseudoCoherentFromAfterPushforward_precomp_iff_of_isClosedEmbedding
      X.isoSpec.hom _ X.isoSpec.hom.isClosedEmbedding hs E m).symm.trans ?_
    rw [hsquare]
    refine (Scheme.Modules.isPseudoCoherentFromAfterPushforward_precomp_iff_of_isClosedEmbedding
      i _ hi (ht.isClosedEmbedding.comp Y.isoSpec.hom.isClosedEmbedding) E m).trans ?_
    refine (Scheme.Modules.isPseudoCoherentFromAfterPushforward_precomp_iff_of_isClosedEmbedding
      Y.isoSpec.hom _ Y.isoSpec.hom.isClosedEmbedding ht.isClosedEmbedding _ m).trans ?_
    exact (hbp _ m).trans hy.symm

/-! ### Restricting the comparison to an affine open -/

/-- The restriction `i ∣_ U` of a closed embedding on spaces `i` is a closed embedding on spaces. -/
private theorem isClosedEmbedding_morphismRestrict_base {X Y : Scheme.{u}} (i : X ⟶ Y)
    (hi : Topology.IsClosedEmbedding i.base) (U : Y.Opens) :
    Topology.IsClosedEmbedding (i ∣_ U).base := by
  rw [AlgebraicGeometry.morphismRestrict_base]
  exact hi.restrictPreimage (U : Set Y)

/-- For a morphism `i` along which pushforward of modules is exact, the restriction to `V` of the
pushforward of `E` on derived categories is the pushforward along `i ∣_ V` of the restriction of
`E` to `i⁻¹V`. -/
public def Scheme.Modules.restrictPushforwardMapDerivedCategoryIso {X Y : Scheme.{u}} (i : X ⟶ Y)
    (V : Y.Opens) [PreservesFiniteColimits (Scheme.Modules.pushforward i)]
    [PreservesFiniteColimits (Scheme.Modules.pushforward (i ∣_ V))] :
    (Scheme.Modules.pushforward i).mapDerivedCategory ⋙
        (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory ≅
      (Scheme.Modules.restrictFunctor (i ⁻¹ᵁ V).ι).mapDerivedCategory ⋙
        (Scheme.Modules.pushforward (i ∣_ V)).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIsoOfCompIso (Iso.refl _) ≪≫
    Functor.mapDerivedCategoryCongr
      (Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso i V) ≪≫
    (Functor.mapDerivedCategoryCompIsoOfCompIso (Iso.refl _)).symm

/-- Let `i : X ⟶ Y` be a closed embedding on spaces, let `U` be an open of `Y` and let `b : U ⟶ Z`
be a closed embedding on spaces. Then the local condition
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward` at `b` for the restriction
of `i_*E` to `U` is the local condition at `(i ∣_ U) ≫ b` for the restriction of `E` to `i⁻¹U`. -/
public theorem Scheme.Modules.isPseudoCoherentFromAfterPushforward_restrict_pushforward_iff
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (hi : Topology.IsClosedEmbedding i.base)
    [PreservesFiniteColimits (Scheme.Modules.pushforward i)] (U : Y.Opens)
    (b : U.toScheme ⟶ Z) (hb : Topology.IsClosedEmbedding b.base)
    (E : DerivedCategory X.Modules) (m : ℤ) :
    Scheme.Modules.IsPseudoCoherentFromAfterPushforward b
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
          ((Scheme.Modules.pushforward i).mapDerivedCategory.obj E)) m ↔
      Scheme.Modules.IsPseudoCoherentFromAfterPushforward ((i ∣_ U) ≫ b)
        ((Scheme.Modules.restrictFunctor (i ⁻¹ᵁ U).ι).mapDerivedCategory.obj E) m := by
  have hjemb := isClosedEmbedding_morphismRestrict_base i hi U
  have := Scheme.Modules.preservesFiniteColimits_pushforward_of_isClosedEmbedding _ hjemb
  refine (Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff_of_iso b
    ((Scheme.Modules.restrictPushforwardMapDerivedCategoryIso i U).app E) m).trans ?_
  exact (Scheme.Modules.isPseudoCoherentFromAfterPushforward_precomp_iff_of_isClosedEmbedding
    (i ∣_ U) b hjemb hb _ m).symm

/-- For `i : X ⟶ Y` a closed immersion on reductions and `g : Y ⟶ S` locally of finite type, and
for a pair of affine opens `U ⊆ g⁻¹V`, there are closed immersions `a : i⁻¹U ⟶ 𝔸ᵏ_V` and
`b : U ⟶ 𝔸ⁿ_V` over `V` at which the local conditions
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward` for `E|_{i⁻¹U}` and for
`(i_*E)|_U` agree. -/
public theorem exists_isClosedImmersion_affineSpace_comparison_on_affineOpens {X Y S : Scheme.{u}}
    (i : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFiniteType i] [LocallyOfFiniteType g]
    (hred : i.IsClosedImmersionOnReductions)
    [PreservesFiniteColimits (Scheme.Modules.pushforward i)] (U : Y.affineOpens)
    (V : S.affineOpens) (hUV : U.1 ≤ g ⁻¹ᵁ V.1) (E : DerivedCategory X.Modules) (m : ℤ) :
    ∃ (n k : ℕ) (a : (i ⁻¹ᵁ U.1).toScheme ⟶ AffineSpace (ULift.{u} (Fin k)) V.1.toScheme)
      (b : U.1.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.1.toScheme),
      IsClosedImmersion a ∧ IsClosedImmersion b ∧
      a ≫ (AffineSpace.over (ULift.{u} (Fin k)) V.1.toScheme).hom =
        (i ≫ g).resLE V.1 (i ⁻¹ᵁ U.1) ((Opens.map i.base).monotone hUV) ∧
      b ≫ (AffineSpace.over (ULift.{u} (Fin n)) V.1.toScheme).hom = g.resLE V.1 U.1 hUV ∧
      (Scheme.Modules.IsPseudoCoherentFromAfterPushforward a
          ((Scheme.Modules.restrictFunctor (i ⁻¹ᵁ U.1).ι).mapDerivedCategory.obj E) m ↔
        Scheme.Modules.IsPseudoCoherentFromAfterPushforward b
          ((Scheme.Modules.restrictFunctor U.1.ι).mapDerivedCategory.obj
            ((Scheme.Modules.pushforward i).mapDerivedCategory.obj E)) m) := by
  have : IsAffineHom i := hred.isAffineHom
  have hi : Topology.IsClosedEmbedding i.base := hred.isClosedEmbedding
  have hWaff : IsAffine (i ⁻¹ᵁ U.1).toScheme := U.2.preimage i
  have hUaff : IsAffine U.1.toScheme := U.2
  have hVaff : IsAffine V.1.toScheme := V.2
  have hjemb := isClosedEmbedding_morphismRestrict_base i hi U.1
  have := Scheme.Modules.preservesFiniteColimits_pushforward_of_isClosedEmbedding _ hjemb
  have hnil : ∀ b : Γ((i ⁻¹ᵁ U.1).toScheme, ⊤), ∃ a : Γ(U.1.toScheme, ⊤),
      IsNilpotent (b - (i ∣_ U.1).appTop.hom a) := by
    intro b
    obtain ⟨a, ha⟩ := hred.exists_isNilpotent_sub_app U ((i ⁻¹ᵁ U.1).topIso.hom b)
    refine ⟨U.1.topIso.inv a, ?_⟩
    have hh := ha.map (i ⁻¹ᵁ U.1).topIso.inv.hom
    have htop : (i ∣_ U.1).appTop =
        U.1.topIso.hom ≫ i.app U.1 ≫ (i ⁻¹ᵁ U.1).topIso.inv := by
      rw [← Scheme.Hom.resLE_eq_morphismRestrict]
      show (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl).app ⊤ = _
      rw [Scheme.Hom.resLE_app_top, Scheme.Hom.appLE_eq_app]
    rw [htop]
    show IsNilpotent (b - (i ⁻¹ᵁ U.1).topIso.inv
      ((i.app U.1) (U.1.topIso.hom (U.1.topIso.inv a))))
    change IsNilpotent ((i ⁻¹ᵁ U.1).topIso.inv
      ((i ⁻¹ᵁ U.1).topIso.hom b - (i.app U.1) a)) at hh
    simpa only [map_sub, Iso.hom_inv_id_apply, Iso.inv_hom_id_apply] using hh
  obtain ⟨n, k, a, b, ha, hb, hac, hbc, hpc⟩ :=
    exists_isClosedImmersion_affineSpace_comparison (i ∣_ U.1) (g.resLE V.1 U.1 hUV) hjemb hnil
  refine ⟨n, k, a, b, ha, hb, ?_, hbc, ?_⟩
  · rw [← Scheme.Hom.resLE_eq_morphismRestrict] at hac
    exact hac.trans (i.resLE_comp_resLE le_rfl g hUV)
  · exact (hpc _ m).trans
      (Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff_of_iso b
        ((Scheme.Modules.restrictPushforwardMapDerivedCategoryIso i U.1).app E).symm m)

/-! ### Relative pseudo-coherence of the pushforward, granted a comparison of charts -/

/-- The affine opens contained in an open `W` of a scheme cover `W`. -/
public theorem iSup_affineOpens_le_eq (X : Scheme.{u}) (W : X.Opens) :
    (⨆ U : {U : X.affineOpens // U.1 ≤ W}, U.val.1) = W := by
  refine le_antisymm (iSup_le fun U => U.property) fun x hx => ?_
  obtain ⟨O, hOa, hxO, hOW⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
  exact (le_iSup (fun U : {U : X.affineOpens // U.1 ≤ W} => U.val.1) ⟨⟨O, hOa⟩, hOW⟩) hxO

/-- Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes locally of finite type and let
`i : X ⟶ Y` be a morphism over `S` which induces a homeomorphism of `X` with a closed subset of
`Y`. Assume that over every compatible pair of affine opens `U ⊆ g⁻¹V` there are closed immersions
`a : i⁻¹U ⟶ 𝔸ᵏ_V` and `b : U ⟶ 𝔸ⁿ_V` over `V` at which the local conditions
`AlgebraicGeometry.Scheme.Modules.IsPseudoCoherentFromAfterPushforward` for `E|_{i⁻¹U}` and for
`(i_*E)|_U` agree. Then, for every integer `m`, `E` is `m`-pseudo-coherent relative to `S` if and
only if `Ri_*E` is. -/
public theorem Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward_of_chartComparison
    {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFiniteType f] [LocallyOfFiniteType g] (i : X ⟶ Y)
    (hi : i ≫ g = f) (hemb : Topology.IsClosedEmbedding i.base)
    [PreservesFiniteColimits (Scheme.Modules.pushforward i)]
    (E : DerivedCategory X.Modules) (m : ℤ)
    (hcomp : ∀ (U : Y.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ g ⁻¹ᵁ V.1),
      ∃ (n k : ℕ) (a : (i ⁻¹ᵁ U.1).toScheme ⟶ AffineSpace (ULift.{u} (Fin k)) V.1.toScheme)
        (b : U.1.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.1.toScheme),
        IsClosedImmersion a ∧ IsClosedImmersion b ∧
        a ≫ (AffineSpace.over (ULift.{u} (Fin k)) V.1.toScheme).hom =
          (i ≫ g).resLE V.1 (i ⁻¹ᵁ U.1) ((Opens.map i.base).monotone hUV) ∧
        b ≫ (AffineSpace.over (ULift.{u} (Fin n)) V.1.toScheme).hom = g.resLE V.1 U.1 hUV ∧
        (Scheme.Modules.IsPseudoCoherentFromAfterPushforward a
            ((Scheme.Modules.restrictFunctor (i ⁻¹ᵁ U.1).ι).mapDerivedCategory.obj E) m ↔
          Scheme.Modules.IsPseudoCoherentFromAfterPushforward b
            ((Scheme.Modules.restrictFunctor U.1.ι).mapDerivedCategory.obj
              ((Scheme.Modules.pushforward i).mapDerivedCategory.obj E)) m)) :
    Scheme.Hom.IsPseudoCoherentFrom f E m ↔
      Scheme.Hom.IsPseudoCoherentFrom g
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          i.toLRSHom.toShHom).obj E) m := by
  have hift : LocallyOfFiniteType (i ≫ g) := hi ▸ (inferInstance : LocallyOfFiniteType f)
  have : LocallyOfFiniteType i := locallyOfFiniteType_of_comp i g
  have : IsAffineHom i := isAffineHom_of_isInducing i hemb.isInducing hemb.isClosed_range
  have hcol' : PreservesFiniteColimits
      (RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom) := ‹_›
  have ebridge := (Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory
    i.toLRSHom.toShHom).app E
  suffices h : Scheme.Hom.IsPseudoCoherentFrom f E m ↔
      Scheme.Hom.IsPseudoCoherentFrom g
        ((Scheme.Modules.pushforward i).mapDerivedCategory.obj E) m by
    exact h.trans ⟨fun hh => Scheme.Hom.IsPseudoCoherentFrom.of_iso g hh ebridge.symm,
      fun hh => Scheme.Hom.IsPseudoCoherentFrom.of_iso g hh ebridge⟩
  constructor
  · intro hE
    refine (Scheme.Hom.isPseudoCoherentFrom_iff_forall_affinePair g _ m).2 fun U V hUV => ?_
    obtain ⟨n, k, a, b, ha, hb, hac, hbc, hpc⟩ := hcomp U V hUV
    have hUX : i ⁻¹ᵁ U.1 ≤ f ⁻¹ᵁ V.1 := by
      rw [← hi]
      exact (Opens.map i.base).monotone hUV
    have hac' : a ≫ (AffineSpace.over (ULift.{u} (Fin k)) V.1.toScheme).hom =
        f.resLE V.1 (i ⁻¹ᵁ U.1) hUX := by simpa [hi] using hac
    refine ⟨n, b, hb, hbc, hpc.1 ?_⟩
    exact Scheme.Hom.IsPseudoCoherentFromOnAffinePair.forall_isClosedImmersion f
      ((Scheme.Hom.isPseudoCoherentFrom_iff_forall_affinePair f E m).1 hE
        ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ V hUX) k a ha hac'
  · intro hE
    refine ⟨S.affineOpens, id, iSup_affineOpens_eq_top S, fun V => ?_⟩
    refine ⟨{U : Y.affineOpens // U.1 ≤ g ⁻¹ᵁ V.1},
      fun U => ⟨i ⁻¹ᵁ U.val.1, U.val.2.preimage i⟩, ?_, fun U => ?_⟩
    · show (⨆ U : {U : Y.affineOpens // U.1 ≤ g ⁻¹ᵁ V.1}, i ⁻¹ᵁ U.val.1) = f ⁻¹ᵁ V.1
      rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_le_eq, ← Scheme.Hom.comp_preimage, hi]
    · obtain ⟨n, k, a, b, ha, hb, hac, hbc, hpc⟩ := hcomp U.val V U.property
      have hUX : i ⁻¹ᵁ U.val.1 ≤ f ⁻¹ᵁ V.1 := by
        rw [← hi]
        exact (Opens.map i.base).monotone U.property
      refine ⟨hUX, k, a, ha, ?_, hpc.2 ?_⟩
      · simpa [hi] using hac
      · exact Scheme.Hom.IsPseudoCoherentFromOnAffinePair.forall_isClosedImmersion g
          ((Scheme.Hom.isPseudoCoherentFrom_iff_forall_affinePair g _ m).1 hE U.val V
            U.property) n b hb hbc

/-- Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes locally of finite type and let
`i : X ⟶ Y` be a morphism over `S` which induces a closed immersion on reductions: there is a
closed immersion `j` of the reduction of `X` into the reduction of `Y` making the square with the
canonical immersions of the reductions commute. Let `E` be an object of `D(𝒪_X)` and `m` an
integer. Then `E` is `m`-pseudo-coherent relative to `S` if and only if `Ri_*E` is
`m`-pseudo-coherent relative to `S`.

With the hypothesis on `i` weakened to a homeomorphism of `X` with a closed subset of `Y` the
equivalence fails, by
`AlgebraicGeometry.Scheme.Hom.not_forall_isPseudoCoherentFrom_iff_derivedPushforward`. -/
@[stacks 09VG "corrected statement — Stacks erratum. The source's \
topological hypothesis, that i induce a homeomorphism of X with a closed subset of Y, makes the \
lemma false (AlgebraicGeometry.Scheme.Hom.not_forall_isPseudoCoherentFrom_iff_derivedPushforward, \
over the nodal curve A = {h ∈ k[s] | h(0) = h(1)} with B = k[s, 1/s]); it is replaced here by the \
hypothesis the source's proof actually uses, that i be a closed immersion on reductions, i.e. \
that A/rad(A) → B/rad(B) be surjective. Both directions, E and m arbitrary"]
public theorem Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward_of_reductionImmersion
    {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFiniteType f] [LocallyOfFiniteType g] (i : X ⟶ Y)
    (hi : i ≫ g = f)
    (hred : ∃ j : X.nilradical.subscheme ⟶ Y.nilradical.subscheme,
      IsClosedImmersion j ∧
        j ≫ Y.nilradical.subschemeι = X.nilradical.subschemeι ≫ i)
    (E : DerivedCategory X.Modules) (m : ℤ) :
    Scheme.Hom.IsPseudoCoherentFrom f E m ↔
      Scheme.Hom.IsPseudoCoherentFrom g
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          i.toLRSHom.toShHom).obj E) m := by
  have hemb : Topology.IsClosedEmbedding i.base :=
    Scheme.Hom.IsClosedImmersionOnReductions.isClosedEmbedding hred
  have hift : LocallyOfFiniteType (i ≫ g) := hi ▸ (inferInstance : LocallyOfFiniteType f)
  have : LocallyOfFiniteType i := locallyOfFiniteType_of_comp i g
  have : IsAffineHom i := Scheme.Hom.IsClosedImmersionOnReductions.isAffineHom hred
  have hcol := Scheme.Modules.preservesFiniteColimits_pushforward_of_isClosedEmbedding i hemb
  exact Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward_of_chartComparison f g i hi hemb
    E m fun U V hUV =>
      exists_isClosedImmersion_affineSpace_comparison_on_affineOpens i g hred U V hUV E m

/-! ### Relative pseudo-coherence of the pushforward, granted conditions on the structure sheaf -/

/-- Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes locally of finite type and let
`i : X ⟶ Y` be a morphism over `S` which induces a homeomorphism of `X` with a closed subset of
`Y`. Assume that over every compatible pair of affine opens `U ⊆ g⁻¹V` there are closed immersions
`a : i⁻¹U ⟶ 𝔸ᵏ_V` and `b : U ⟶ 𝔸ⁿ_V` over `V` along which the pushforward of `𝒪_{i⁻¹U}` is a
pseudo-coherent module, for `a` directly and for `b` after composing with the restriction `i ∣_ U`.
Then, for every integer `m`, `E` is `m`-pseudo-coherent relative to `S` if and only if `Ri_*E` is.
-/
public theorem Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward_of_structureSheafCharts
    {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFiniteType f] [LocallyOfFiniteType g] (i : X ⟶ Y)
    (hi : i ≫ g = f) (hemb : Topology.IsClosedEmbedding i.base)
    [PreservesFiniteColimits (Scheme.Modules.pushforward i)]
    (hOX : ∀ (U : Y.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ g ⁻¹ᵁ V.1),
      ∃ (k : ℕ) (a : (i ⁻¹ᵁ U.1).toScheme ⟶ AffineSpace (ULift.{u} (Fin k)) V.1.toScheme),
        IsClosedImmersion a ∧
        a ≫ (AffineSpace.over (ULift.{u} (Fin k)) V.1.toScheme).hom =
          (i ≫ g).resLE V.1 (i ⁻¹ᵁ U.1) ((Opens.map i.base).monotone hUV) ∧
        RingedSpace.IsPseudoCoherent
          (X := (AffineSpace (ULift.{u} (Fin k)) V.1.toScheme).toRingedSpace)
          ((DerivedCategory.singleFunctor
              (AffineSpace (ULift.{u} (Fin k)) V.1.toScheme).Modules 0).obj
            ((Scheme.Modules.pushforward a).obj
              (SheafOfModules.unit (i ⁻¹ᵁ U.1).toScheme.ringCatSheaf))))
    (hOY : ∀ (U : Y.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ g ⁻¹ᵁ V.1),
      ∃ (n : ℕ) (b : U.1.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.1.toScheme),
        IsClosedImmersion b ∧
        b ≫ (AffineSpace.over (ULift.{u} (Fin n)) V.1.toScheme).hom = g.resLE V.1 U.1 hUV ∧
        RingedSpace.IsPseudoCoherent
          (X := (AffineSpace (ULift.{u} (Fin n)) V.1.toScheme).toRingedSpace)
          ((DerivedCategory.singleFunctor
              (AffineSpace (ULift.{u} (Fin n)) V.1.toScheme).Modules 0).obj
            ((Scheme.Modules.pushforward ((i ∣_ U.1) ≫ b)).obj
              (SheafOfModules.unit (i ⁻¹ᵁ U.1).toScheme.ringCatSheaf))))
    (E : DerivedCategory X.Modules) (m : ℤ) :
    Scheme.Hom.IsPseudoCoherentFrom f E m ↔
      Scheme.Hom.IsPseudoCoherentFrom g
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          i.toLRSHom.toShHom).obj E) m := by
  refine Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward_of_chartComparison f g i hi hemb
    E m fun U V hUV => ?_
  obtain ⟨k, a, ha, hac, hOa⟩ := hOX U V hUV
  obtain ⟨n, b, hb, hbc, hOb⟩ := hOY U V hUV
  have hjemb := isClosedEmbedding_morphismRestrict_base i hemb U.1
  exact ⟨n, k, a, b, ha, hb, hac, hbc,
    (Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff_of_isPseudoCoherent_unit a
        ((i ∣_ U.1) ≫ b) ha.isClosedEmbedding (hb.isClosedEmbedding.comp hjemb) hOa hOb
        ((Scheme.Modules.restrictFunctor (i ⁻¹ᵁ U.1).ι).mapDerivedCategory.obj E) m).trans
      (Scheme.Modules.isPseudoCoherentFromAfterPushforward_restrict_pushforward_iff i hemb
        U.1 b hb.isClosedEmbedding E m).symm⟩

end AlgebraicGeometry

end

