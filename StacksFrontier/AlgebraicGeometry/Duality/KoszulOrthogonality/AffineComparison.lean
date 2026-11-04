module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulOrthogonality.AffineDetection
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictAdjunction
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.QuasiCoherentDirectImage
public import StacksFrontier.RingTheory.Koszul.Truncation.DerivedKoszulObject
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Koszul detection on an affine scheme

Let `A` be a commutative ring, `f₁, …, f_r ∈ A`, `X = Spec A` and `U = D(f₁) ∪ … ∪ D(f_r)`. This
file proves the geometric form of the detection statement behind [Stacks, Tag 09IR]:

> an object `M` of `D(𝒪_X)` with quasi-coherent cohomology sheaves which restricts to zero on `U`
> and receives no nonzero morphism from any shift of the sheafified Koszul complex `K` is zero.

The algebraic counterpart over `A` is
`Stacks.Koszul.Truncation.isZero_of_forall_hom_derivedKoszul_eq_zero`
(`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/AffineDetection.lean`), and this file
carries `M` across the affine derived Spec–Γ equivalence of [Stacks, Tag 06Z0] to meet it. There
are three things to transport.

* **The object.** Derived sheafification `derivedTilde A : D(A) ⥤ D_QCoh(𝒪_X)` is an equivalence
  by `AlgebraicGeometry.derivedTilde_isEquivalence`, so the counit identifies `M` with the
  sheafification of `N = RΓ(X, M)`.
* **The Hom-vanishing.** `K` is the termwise sheafification of the Koszul cochain complex, so it
  *is* the derived sheafification of the Koszul object of `D(A)`, by
  `AlgebraicGeometry.derivedTildeFactors`. Derived sheafification is fully faithful and commutes
  with the shift, so the vanishing of `Hom(K⟦n⟧, M)` is the vanishing of `Hom(K_A⟦n⟧, N)`.
* **The torsion.** Restriction to `U` is exact, so `M|_U = 0` says that every cohomology sheaf of
  `M` restricts to zero on `U`; and the cohomology sheaves of `M` are the sheafifications of the
  cohomology modules of `N`. The sections of a sheafified module over `D(f_i)` are its
  localization at `f_i` — Mathlib's `AlgebraicGeometry.tilde` makes this an instance of
  `IsLocalizedModule.Away` — so a vanishing restriction to `U` says exactly that every element of
  every cohomology module of `N` is killed by a power of every `f_i`, which is the hypothesis the
  algebraic statement asks for.

## Main results

* `Stacks.Duality.OpenImmersion.isZero_restrictFunctor_homology_of_isZero_derivedRestrict` — an
  object killed by `j^*` has all its cohomology sheaves killed by `j^*`.
* `Stacks.Koszul.Truncation.torsion_of_isZero_restrict_tilde` — a module whose sheafification
  restricts to zero on `⋃ᵢ D(f_i)` is `f_i`-power torsion for every `i`.
* `AlgebraicGeometry.hom_eq_zero_of_hom_mapHomologicalComplex_eq_zero` — Hom-vanishing out of a
  sheafified complex descends to Hom-vanishing out of the complex.
* `Stacks.DerivedModel.derivedCategoryB_derivedPushforward_of_model` — whether `Rg_*` preserves a
  cohomological property does not depend on the chosen model of the derived categories.
* `AlgebraicGeometry.derivedCategoryB_derivedPushforward_of_qcqs` — **[Stacks, Tag 08D5] part
  (1)** at the locally small model.
* `Stacks.Koszul.Truncation.derivedCategoryB_derivedPushforward_openComplement` — the same for the
  open immersion `⋃ᵢ D(f_i) ⟶ Spec A`.
* `Stacks.Koszul.Truncation.isZero_of_forall_hom_koszulObject_eq_zero` — the detection statement
  on `Spec A`.

## Implementation notes

No `@[stacks]` attribute is attached: what is proved here is the geometric half of the *proof* of
[Stacks, Tag 09IR], and the tag itself — the equivalence of the two conditions on the unit of
`j^* ⊣ Rj_*` — is proved in
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/AffineSituation.lean`.

Quasi-coherence of `M` is taken in the form `DerivedCategoryB.derivedCategoryB _ M`, which unfolds
to "every cohomology sheaf of `M` is quasi-coherent", because that is what the full subcategory
`D_QCoh(𝒪_X)` of [Stacks, Tag 06Z0] is defined by and so what the equivalence consumes without
further plumbing.

Everything is stated at the derived categories supplied by
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` rather than at a free
`[HasDerivedCategory.{w} _]` binder, because [Stacks, Tag 06Z0] is available at that model and at
no other. `CategoryTheory.HasDerivedCategory.standard` is mentioned nowhere.

[Stacks, Tag 08D5] part (1) is proved in the library at
`CategoryTheory.HasDerivedCategory.standard`
(`AlgebraicGeometry.isQuasicoherent_derivedPushforward` of
`StacksFrontier/AlgebraicGeometry/TotalDirectImage/QuasiCoherentDirectImage.lean`, whose
`attribute [local instance 10000] HasDerivedCategory.standard` forces that model), and is needed
here at the locally small one. It is not reproved: `Rg_*` is computed by a K-injective resolution
at *every* model, by `Stacks.DerivedModel.derivedPushforwardQIsoOfIsKInjective`, so whether it
preserves a cohomological property is a statement about cochain complexes and therefore the same at
any two models. That is `Stacks.DerivedModel.derivedCategoryB_derivedPushforward_of_model`, and
feeding it the standard model on one side and the locally small one on the other transports the
tag.

Two statements are proved at a general `R : CommRingCat.{u}` and then used at `CommRingCat.of A`:
the Hom-descent and the invertibility of the counit. This is not for generality — instance
synthesis for `tilde.functor` and for the counit stalls on the literal `CommRingCat.of A`,
whose carrier is only definitionally `A`, while it succeeds at an opaque `R`.

## References

* [Stacks Project, Tag 09IR](https://stacks.math.columbia.edu/tag/09IR)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated Opposite

universe w₁ w₂ w₃ w₄ v₁ v₂ u₁ u₂ u

/-! ### Restriction along an open immersion, and cohomology -/

namespace Stacks.Duality.OpenImmersion

/-- **An object of `D(𝒪_Y)` killed by `j^*` has all its cohomology sheaves killed by `j^*`.**
Restriction along an open immersion is exact, so it commutes with cohomology by
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`, and an additive functor sends a zero
object to a zero object. -/
theorem isZero_restrictFunctor_homology_of_isZero_derivedRestrict
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : DerivedCategory Y.Modules)
    (hM : IsZero ((derivedRestrict j).obj M)) (m : ℤ) :
    IsZero ((Scheme.Modules.restrictFunctor j).obj
      ((DerivedCategory.homologyFunctor Y.Modules m).obj M)) :=
  IsZero.of_iso ((DerivedCategory.homologyFunctor X.Modules m).map_isZero hM)
    (((Scheme.Modules.restrictFunctor j).mapDerivedCategoryHomologyIso m).app M).symm

/-- **Restriction along an open immersion preserves quasi-coherent cohomology.** Restriction is
exact, so it commutes with cohomology, and the restriction of a quasi-coherent module is
quasi-coherent by Mathlib's `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor`. -/
theorem derivedCategoryB_derivedRestrict {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (E : DerivedCategory Y.Modules)
    (hE : DerivedCategoryB.derivedCategoryB (A := Y.Modules)
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf) E) :
    DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) ((derivedRestrict j).obj E) := by
  intro n
  refine (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (((Scheme.Modules.restrictFunctor j).mapDerivedCategoryHomologyIso n).app E).symm ?_
  have : ((DerivedCategory.homologyFunctor Y.Modules n).obj E).IsQuasicoherent := hE n
  exact (inferInstance : ((Scheme.Modules.restrictFunctor j).obj
    ((DerivedCategory.homologyFunctor Y.Modules n).obj E)).IsQuasicoherent)

end Stacks.Duality.OpenImmersion

/-! ### Quasi-coherence of the third vertex of a triangle -/

namespace AlgebraicGeometry

/-- **The objects of `D(𝒪_X)` with quasi-coherent cohomology are closed under cones.** The
quasi-coherent modules are a weak Serre subcategory, so the objects of the derived category whose
cohomology lies in it form a triangulated subcategory. -/
theorem derivedCategoryB_obj₃_of_distTriang {X : Scheme.{u}}
    (T : Triangle (DerivedCategory X.Modules)) (hT : T ∈ distTriang (DerivedCategory X.Modules))
    (h₁ : DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) T.obj₁)
    (h₂ : DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) T.obj₂) :
    DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) T.obj₃ := by
  have hiso := DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms
    (A := X.Modules) (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
  exact ObjectProperty.ext_of_isTriangulatedClosed₃ _ T hT h₁ h₂

end AlgebraicGeometry

/-! ### Descending Hom-vanishing along derived sheafification -/

namespace AlgebraicGeometry

/-- **Derived sheafification reflects Hom-vanishing.** Let `C` be a cochain complex of
`R`-modules, let `N` be an object of `D(R)` whose derived sheafification is `Z`, and suppose no
nonzero morphism goes into `Z` from a shift of the class of the termwise sheafification of `C`.
Then no nonzero morphism goes into `N` from the corresponding shift of the class of `C`.

Derived sheafification `(tilde.functor R).mapDerivedCategory` is fully faithful — it agrees with
`derivedTilde R` followed by the inclusion of `D_QCoh(𝒪_{Spec R})`, by
`AlgebraicGeometry.derivedTildeCompι` — and it commutes with the shift and factors through the
termwise sheafification by `AlgebraicGeometry.derivedTildeFactors`; so a morphism out of a shift
of `Q C` is carried to a morphism out of the corresponding shift of the sheafified complex, and
faithfulness carries the vanishing back. -/
theorem hom_eq_zero_of_hom_mapHomologicalComplex_eq_zero (R : CommRingCat.{u})
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (N : DerivedCategory (ModuleCat.{u} R))
    (Z : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory)
    (e : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.obj
      ((derivedTilde R).obj N) ≅ Z.obj)
    (n : ℤ)
    (h : ∀ g : (DerivedCategory.Q.obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj C))⟦n⟧ ⟶ Z.obj,
      g = 0)
    (g : (DerivedCategory.Q.obj C)⟦n⟧ ⟶ N) :
    g = 0 := by
  have hfaithful : (tilde.functor R).mapDerivedCategory.Faithful :=
    Functor.Faithful.of_iso (derivedTildeCompι R)
  let δ : (tilde.functor R).mapDerivedCategory.obj N ≅ Z.obj :=
    ((derivedTildeCompι R).app N).symm ≪≫ e
  let α : (tilde.functor R).mapDerivedCategory.obj ((DerivedCategory.Q.obj C)⟦n⟧) ≅
      (DerivedCategory.Q.obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj C))⟦n⟧ :=
    ((tilde.functor R).mapDerivedCategory.commShiftIso n).app (DerivedCategory.Q.obj C) ≪≫
      (shiftFunctor (DerivedCategory (Spec R).Modules) n).mapIso
        (((tilde.functor R).mapDerivedCategoryFactors).app C)
  exact (tilde.functor R).mapDerivedCategory.map_injective <| by
    simpa using h (α.inv ≫ (tilde.functor R).mapDerivedCategory.map g ≫ δ.hom)

/-- **The counit of the affine derived Spec–Γ adjunction is invertible**, derived sheafification
being an equivalence. Stated at an opaque `R` so that instance synthesis succeeds; at a literal
`CommRingCat.of A` it does not. -/
theorem isIso_derivedTildeQuasicoherentAdjunction_counit_app (R : CommRingCat.{u})
    (Z : (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory) :
    IsIso ((derivedTildeQuasicoherentAdjunction R).counit.app Z) :=
  inferInstance

end AlgebraicGeometry

/-! ### Quasi-coherence of the derived direct image, at any model -/

section Pushforward

open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace DerivedCategoryB

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]

/-- **An object property holds of every cohomology object of `Q K` exactly when it holds of every
cohomology object of the complex `K`.** -/
theorem derivedCategoryB_q_obj_iff (P : ObjectProperty A) (hP : P.IsClosedUnderIsomorphisms)
    (K : CochainComplex A ℤ) :
    DerivedCategoryB.derivedCategoryB P (DerivedCategory.Q.obj K) ↔
      ∀ n : ℤ, P (K.homology n) := by
  have := hP
  exact ⟨fun h n => P.prop_of_iso ((DerivedCategory.homologyFunctorFactors A n).app K) (h n),
    fun h n => P.prop_of_iso ((DerivedCategory.homologyFunctorFactors A n).app K).symm (h n)⟩

/-- **`D_P(A)` is closed under isomorphism as soon as `P` is.** -/
theorem derivedCategoryB_of_iso (P : ObjectProperty A) (hP : P.IsClosedUnderIsomorphisms)
    {E F : DerivedCategory A} (e : E ≅ F)
    (h : DerivedCategoryB.derivedCategoryB P E) :
    DerivedCategoryB.derivedCategoryB P F := by
  have := hP
  exact fun n => P.prop_of_iso ((DerivedCategory.homologyFunctor A n).mapIso e) (h n)

end DerivedCategoryB

namespace Stacks.DerivedModel

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]

/-- **Every object of the derived category is the class of a K-injective cochain complex**, as
soon as every complex admits a quasi-isomorphism into a K-injective one. -/
theorem exists_isKInjective_iso
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (φ : K ⟶ I),
      I.IsKInjective ∧ QuasiIso φ)
    (E : DerivedCategory A) :
    ∃ I : CochainComplex A ℤ, I.IsKInjective ∧ Nonempty (E ≅ DerivedCategory.Q.obj I) := by
  obtain ⟨I, φ, hI, hφ⟩ := hres (DerivedCategory.Q.objPreimage E)
  have : IsIso (DerivedCategory.Q.map φ) := inferInstance
  exact ⟨I, hI,
    ⟨(DerivedCategory.Q.objObjPreimageIso E).symm ≪≫ asIso (DerivedCategory.Q.map φ)⟩⟩

section ModelFree

variable {X Y : RingedSpace.{u, u}} (g : X ⟶ Y)
  [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]

/-- **`Rg_*` is computed by a K-injective complex**: `Rg_*(Q I) ≅ Q(g_* I)`. The derivation unit
of `Rg_*` is invertible at the K-injective complexes by construction, which is what
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.isIso_derivedPushforwardUnit_app_of_isKInjective`
records; no model of the derived categories is fixed. -/
def derivedPushforwardQIsoOfIsKInjective
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective) :
    (derivedPushforward g).obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj
        (((modulePushforward g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  have h := isIso_derivedPushforwardUnit_app_of_isKInjective g I hI
  exact (derivedPushforward g).mapIso
      ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (structureSheafRing X))).app I).symm ≪≫
    (asIso ((derivedPushforwardUnit g).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))).symm ≪≫
    DerivedCategory.Qh.mapIso
      (((modulePushforward g).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app I) ≪≫
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Y))).app _

end ModelFree

/-- **Whether `Rg_*` preserves a cohomological property does not depend on the chosen model of
the derived categories.** Every object of `D(𝒪_X)` is the class of a K-injective complex `I`, and
`Rg_*(Q I)` is the class of `g_* I` at any model; so the hypothesis, read at one pair of models,
and the conclusion, read at another, are both the statement that the cohomology objects of the
cochain complex `g_* I` have the property. -/
theorem derivedCategoryB_derivedPushforward_of_model {X Y : RingedSpace.{u, u}} (g : X ⟶ Y)
    (h₁ : HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X)))
    (k₁ : HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y)))
    (h₂ : HasDerivedCategory.{w₃} (SheafOfModules.{u} (structureSheafRing X)))
    (k₂ : HasDerivedCategory.{w₄} (SheafOfModules.{u} (structureSheafRing Y)))
    (P : ObjectProperty (SheafOfModules.{u} (structureSheafRing X)))
    (hP : P.IsClosedUnderIsomorphisms)
    (R : ObjectProperty (SheafOfModules.{u} (structureSheafRing Y)))
    (hR : R.IsClosedUnderIsomorphisms)
    (hbase : ∀ E : @DerivedCategory _ _ _ h₂,
      @DerivedCategoryB.derivedCategoryB _ _ _ h₂ P E →
        @DerivedCategoryB.derivedCategoryB _ _ _ k₂ R
          ((@derivedPushforward _ _ g h₂ k₂).obj E))
    (E : @DerivedCategory _ _ _ h₁)
    (hE : @DerivedCategoryB.derivedCategoryB _ _ _ h₁ P E) :
    @DerivedCategoryB.derivedCategoryB _ _ _ k₁ R ((@derivedPushforward _ _ g h₁ k₁).obj E) := by
  obtain ⟨I, hI, ⟨e⟩⟩ :=
    @exists_isKInjective_iso _ _ _ h₁ (exists_quasiIso_isKInjective X) E
  have hIP : ∀ n : ℤ, P (I.homology n) :=
    (@DerivedCategoryB.derivedCategoryB_q_obj_iff _ _ _ h₁ P hP I).1
      (@DerivedCategoryB.derivedCategoryB_of_iso _ _ _ h₁ P hP _ _ e hE)
  have hpush : ∀ n : ℤ,
      R ((((modulePushforward g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I).homology n) :=
    (@DerivedCategoryB.derivedCategoryB_q_obj_iff _ _ _ k₂ R hR _).1
      (@DerivedCategoryB.derivedCategoryB_of_iso _ _ _ k₂ R hR _ _
        (@derivedPushforwardQIsoOfIsKInjective _ _ g h₂ k₂ I hI)
        (hbase _ ((@DerivedCategoryB.derivedCategoryB_q_obj_iff _ _ _ h₂ P hP I).2 hIP)))
  exact @DerivedCategoryB.derivedCategoryB_of_iso _ _ _ k₁ R hR _ _
    (((@derivedPushforward _ _ g h₁ k₁).mapIso e).trans
      (@derivedPushforwardQIsoOfIsKInjective _ _ g h₁ k₁ I hI)).symm
    ((@DerivedCategoryB.derivedCategoryB_q_obj_iff _ _ _ k₁ R hR _).2 hpush)

end Stacks.DerivedModel

namespace AlgebraicGeometry

/-- **[Stacks, Tag 08D5] part (1) at the locally small model.** For a quasi-compact and
quasi-separated morphism of schemes, `Rg_*` carries objects with quasi-coherent cohomology sheaves
to objects with quasi-coherent cohomology sheaves.

The tag is proved in the library at `CategoryTheory.HasDerivedCategory.standard`; this transports
it by `Stacks.DerivedModel.derivedCategoryB_derivedPushforward_of_model`. -/
theorem derivedCategoryB_derivedPushforward_of_qcqs {X S : Scheme.{u}} (g : X ⟶ S)
    [QuasiCompact g] [QuasiSeparated g] (E : DerivedCategory X.Modules)
    (hE : DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) E) :
    DerivedCategoryB.derivedCategoryB (A := S.Modules)
      (SheafOfModules.isQuasicoherent S.ringCatSheaf)
      ((Stacks.Duality.derivedPushforward g).obj E) := by
  refine Stacks.DerivedModel.derivedCategoryB_derivedPushforward_of_model g.toLRSHom.toShHom
    (Scheme.Modules.hasDerivedCategory X) (Scheme.Modules.hasDerivedCategory S)
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf) ?_
    (SheafOfModules.isQuasicoherent S.ringCatSheaf) ?_
    (fun E₂ hE₂ => AlgebraicGeometry.isQuasicoherent_derivedPushforward g ⟨E₂, hE₂⟩) E hE
  · exact inferInstanceAs
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderIsomorphisms
  · exact inferInstanceAs
      (SheafOfModules.isQuasicoherent S.ringCatSheaf).IsClosedUnderIsomorphisms

end AlgebraicGeometry

namespace Stacks.Koszul.Truncation

/-- The open `⋃ᵢ D(f_i) ⊆ Spec A` is quasi-compact: it is a finite union of principal opens,
each of which is affine and so quasi-compact. -/
@[ega "I 1.1.10" "more general"]
instance compactSpace_openComplement {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) :
    CompactSpace (openComplement f).toScheme :=
  isCompact_iff_compactSpace.mp (by
    rw [TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun i => ((isAffineOpen_top (Spec (.of A))).basicOpen _).isCompact)

/-- **[Stacks, Tag 08D5] part (1) for the open immersion of `⋃ᵢ D(f_i)` into `Spec A`.** -/
theorem derivedCategoryB_derivedPushforward_openComplement {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A) (E : DerivedCategory (openComplement f).toScheme.Modules)
    (hE : DerivedCategoryB.derivedCategoryB (A := (openComplement f).toScheme.Modules)
      (SheafOfModules.isQuasicoherent (openComplement f).toScheme.ringCatSheaf) E) :
    DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of A)).Modules)
      (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf)
      ((Stacks.Duality.derivedPushforward (openComplement f).ι).obj E) :=
  AlgebraicGeometry.derivedCategoryB_derivedPushforward_of_qcqs _ E hE

end Stacks.Koszul.Truncation

end Pushforward

namespace Stacks.Koszul.Truncation

/-! ### Power torsion from a vanishing restriction -/

/-- **A module whose sheafification restricts to zero on `⋃ᵢ D(f_i)` is `f_i`-power torsion for
every `i`.** The principal open `D(f_i)` is contained in `⋃ᵢ D(f_i)`, so the sections of the
sheafification of `P` over `D(f_i)` are the sections of a zero object and hence vanish; and those
sections are the localization `P[1/f_i]`, by Mathlib's `IsLocalizedModule.Away` instance for
`AlgebraicGeometry.tilde.toOpen`. -/
theorem torsion_of_isZero_restrict_tilde {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (P : ModuleCat.{u} A)
    (hzero : IsZero ((Scheme.Modules.restrictFunctor (openComplement f).ι).obj
      ((tilde.functor (CommRingCat.of A)).obj P)))
    (i : Fin r) (x : P) : ∃ k : ℕ, f i ^ k • x = 0 := by
  have key : ∀ {X : Scheme.{u}} (U : X.Opens) (M : X.Modules),
      IsZero ((Scheme.Modules.restrictFunctor U.ι).obj M) →
      ∀ V : X.Opens, V ≤ U → Subsingleton (M.val.obj (op V)) := by
    intro X U M hM V hV
    have hW : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
      simpa [Scheme.Hom.image_preimage_eq_opensRange_inf] using hV
    have : (SheafOfModules.evaluation U.toScheme.ringCatSheaf
        (op (U.ι ⁻¹ᵁ V))).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
    have h1 := ModuleCat.isZero_iff_subsingleton.mp (Functor.map_isZero
      (SheafOfModules.evaluation U.toScheme.ringCatSheaf (op (U.ι ⁻¹ᵁ V))) hM)
    have h2 : Subsingleton (M.val.obj (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ V)))) := h1
    rwa [hW] at h2
  have main : ∀ (R : CommRingCat.{u}) (Q : ModuleCat.{u} R) (b : R) (y : Q),
      Subsingleton ((modulesSpecToSheaf.obj (tilde Q)).presheaf.obj
        (op (PrimeSpectrum.basicOpen b))) → ∃ k : ℕ, b ^ k • y = 0 := by
    intro R Q b y hsub
    have h4 : (tilde.toOpen Q (PrimeSpectrum.basicOpen b)).hom y = 0 := Subsingleton.elim _ _
    obtain ⟨⟨s, k, rfl⟩, hk⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers b) _).mp h4
    exact ⟨k, hk⟩
  have hVle : (Spec (CommRingCat.of A)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (f i)) ≤ openComplement f :=
    le_iSup (fun j => (Spec (CommRingCat.of A)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (f j))) i
  have h2 := key _ _ hzero _ hVle
  rw [AlgebraicGeometry.basicOpen_eq_of_affine] at h2
  exact main (CommRingCat.of A) P (f i) x h2

/-! ### The cohomology sheaves of a derived sheafification -/

/-- **The cohomology sheaves of a derived sheafification are the sheafifications of the cohomology
modules.** Derived sheafification agrees with the termwise sheafification of complexes, by
`AlgebraicGeometry.derivedTildeCompι`, and the termwise sheafification is exact, so
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` applies. -/
theorem nonempty_homology_derivedTilde_iso {A : Type u} [CommRing A]
    (N : DerivedCategory (ModuleCat.{u} A)) (m : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules m).obj
        ((DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of A)).Modules)
          (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf)).ι.obj
            ((derivedTilde (CommRingCat.of A)).obj N)) ≅
      (tilde.functor (CommRingCat.of A)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) m).obj N)) := by
  have : (tilde.functor (CommRingCat.of A)).Additive :=
    AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor
  have : PreservesFiniteLimits (tilde.functor (CommRingCat.of A)) :=
    AlgebraicGeometry.tilde.preservesFiniteLimits _
  have : (tilde.functor (CommRingCat.of A)).IsLeftAdjoint := tilde.adjunction.isLeftAdjoint
  exact ⟨(DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules m).mapIso
      ((derivedTildeCompι (CommRingCat.of A)).app N) ≪≫
    ((tilde.functor (CommRingCat.of A)).mapDerivedCategoryHomologyIso m).app N⟩

/-! ### Detection on `Spec A` -/

/-- **Degreewise Koszul detection on `Spec A`.** Let `A` be a commutative ring,
`f₁, …, f_r ∈ A`, `X = Spec A` and `U = D(f₁) ∪ … ∪ D(f_r) ⊆ X`. Let `M` be an object of
`D(𝒪_X)` with quasi-coherent cohomology sheaves which restricts to zero on `U`, and let `q` be
an integer. If every morphism `K⟦-q⟧ ⟶ M` out of that one shift of the sheafified Koszul complex
vanishes, then `H^q(M) = 0`.

This is the geometric content of the implication "(2) implies (1)" of [Stacks, Tag 09IR], in the
degreewise form the truncated criteria of [Stacks, Tag 0GEJ] and [Stacks, Tag 0GEK] need: there
only a half-line of shifts is assumed orthogonal and only a half-line of cohomology is claimed to
vanish. The proof transports `M` across the affine derived Spec–Γ equivalence of
[Stacks, Tag 06Z0] to `N = RΓ(X, M)` in `D(A)`, where the hypotheses become those of
`Stacks.Koszul.Truncation.isZero_homology_of_forall_hom_derivedKoszul_eq_zero`: the Hom-vanishing
at the shift `-q` by full faithfulness of derived sheafification, and the power torsion of the
cohomology modules of `N` because the cohomology sheaves of `M` are their sheafifications and
restrict to zero on `U`. The conclusion comes back through `H^q(M) ≅ (H^q(N))~`. -/
theorem isZero_homology_of_forall_hom_koszulObject_eq_zero {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A) (M : DerivedCategory (Spec (CommRingCat.of A)).Modules)
    (hM : (DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of A)).Modules)
      (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf)) M)
    (hres : IsZero ((Stacks.Duality.OpenImmersion.derivedRestrict
      (openComplement f).ι).obj M))
    (q : ℤ) (h : ∀ g : (koszulObject f)⟦-q⟧ ⟶ M, g = 0) :
    IsZero ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules q).obj M) := by
  have : (tilde.functor (CommRingCat.of A)).Additive :=
    AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor
  let Z : (DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of A)).Modules)
    (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf)).FullSubcategory :=
    ⟨M, hM⟩
  let N := (derivedGlobalSectionsQuasicoherent (CommRingCat.of A)).obj Z
  have hcounit :=
    AlgebraicGeometry.isIso_derivedTildeQuasicoherentAdjunction_counit_app (CommRingCat.of A) Z
  let eZ : (DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of A)).Modules)
      (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf)).ι.obj
        ((derivedTilde (CommRingCat.of A)).obj N) ≅ Z.obj :=
    (DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of A)).Modules)
      (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf)).ι.mapIso
        (asIso ((derivedTildeQuasicoherentAdjunction (CommRingCat.of A)).counit.app Z))
  have hN : ∀ g : (derivedKoszul f)⟦-q⟧ ⟶ N, g = 0 :=
    fun g => AlgebraicGeometry.hom_eq_zero_of_hom_mapHomologicalComplex_eq_zero
      (CommRingCat.of A) ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat) N Z eZ
      (-q) h g
  have hε := fun m : ℤ => (nonempty_homology_derivedTilde_iso N m).map fun ε =>
    ε.symm ≪≫ (DerivedCategory.homologyFunctor (Spec (CommRingCat.of A)).Modules m).mapIso eZ
  have htor : ∀ (i : Fin r) (m : ℤ)
      (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) m).obj N),
      ∃ k : ℕ, f i ^ k • x = 0 := by
    intro i m x
    obtain ⟨ε⟩ := hε m
    exact torsion_of_isZero_restrict_tilde f _ (IsZero.of_iso
      (Stacks.Duality.OpenImmersion.isZero_restrictFunctor_homology_of_isZero_derivedRestrict
        (openComplement f).ι M hres m)
      ((Scheme.Modules.restrictFunctor (openComplement f).ι).mapIso ε)) i x
  obtain ⟨ε⟩ := hε q
  exact IsZero.of_iso ((tilde.functor (CommRingCat.of A)).map_isZero
    (isZero_homology_of_forall_hom_derivedKoszul_eq_zero f N htor q hN)) ε.symm

/-- **Koszul detection on `Spec A`.** Let `A` be a commutative ring, `f₁, …, f_r ∈ A` and
`U = D(f₁) ∪ … ∪ D(f_r) ⊆ X = Spec A`. An object `M` of `D(𝒪_X)` with quasi-coherent cohomology
sheaves which restricts to zero on `U` and receives no nonzero morphism from any shift of the
sheafified Koszul complex `K` of the sequence is zero.

This is the geometric content of the implication "(2) implies (1)" of [Stacks, Tag 09IR], and it
is `Stacks.Koszul.Truncation.isZero_homology_of_forall_hom_koszulObject_eq_zero` in every degree:
an object of `D(𝒪_X)` with no cohomology at all is zero. -/
theorem isZero_of_forall_hom_koszulObject_eq_zero {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A) (M : DerivedCategory (Spec (CommRingCat.of A)).Modules)
    (hM : (DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of A)).Modules)
      (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf)) M)
    (hres : IsZero ((Stacks.Duality.OpenImmersion.derivedRestrict
      (openComplement f).ι).obj M))
    (h : ∀ (n : ℤ) (g : (koszulObject f)⟦n⟧ ⟶ M), g = 0) :
    IsZero M :=
  Stacks.Duality.isZero_of_forall_isZero_homology M fun q =>
    isZero_homology_of_forall_hom_koszulObject_eq_zero f M hM hres q (h (-q))

end Stacks.Koszul.Truncation

end
