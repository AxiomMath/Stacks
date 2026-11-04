module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.AffinePerfectGenerator
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration

/-!
# Compact generation of `D_{QCoh,T}(𝒪_X)` for a quasi-compact quasi-separated scheme

Let `X` be a quasi-compact quasi-separated scheme and `T ⊆ X` a closed subset with quasi-compact
complement. This file proves that `D_{QCoh,T}(𝒪_X)` — the objects of `D(𝒪_X)` with quasi-coherent
cohomology sheaves supported on `T` — is generated, in the sense of [Stacks, Tag 09SJ], by a
single object `G` of `D_QCoh(𝒪_X)` which is compact in `D_QCoh(𝒪_X)` and supported on `T`. This
is the induction carrying the proof of [Stacks, Tag 0A9A]; the companion file
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/QcqsPerfectGenerator.lean` shows that
such a `G` is perfect, which is the statement of the tag.

## The proof

The source runs the induction principle [Stacks, Tag 08DR]; as in
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/QcqsCompactGeneration.lean` it is run here
as an induction on the number of affine opens covering `X`. Write `X = U ∪ V` with `U`
quasi-compact, `V = Spec A`, `W = U ∩ V = D(f₁) ∪ … ∪ D(f_r)`, `Z = V ∖ U`, and let `P` generate
`D_{QCoh,T ∩ U}(𝒪_U)`.

* *The affine case* is the Koszul complex on a sequence cutting out `T`
  (`Stacks.Duality.Supported.isZero_of_quasiCoherentSupported_of_forall_hom_koszulObject_eq_zero`,
  [Stacks, Tag 09IR]); in the induction it enters through the Koszul complex `K` on
  `g₁, …, g_s` with `V(g) = Z ∩ T`, glued with `0` on `U` to the source's `K' = R(V → X)_*K`.
* *The extension of `P`* is where the source cites [Stacks, Tag 09IM]. Here Thomason's trick
  replaces it: `P|_W` is extended by zero to `W ∪ (V ∖ T) = D(g₁) ∪ … ∪ D(g_s)`, lifted to a
  compact `Q` on `V` with `Q|_W = P|_W ⊕ P|_W[1]` by [Stacks, Tag 08EK], and `Q` is supported on
  `T` because it vanishes on `V ∖ T`; then `P ⊕ P[1]` and `Q` glue to `R` ([Stacks, Tag 08DG]).
* *Generation* by `K' ⊕ R` is the source's argument, the omitted detail `E = R(U → X)_*E|_U`
  included: the cone of `E ⟶ R(U → X)_*E|_U` vanishes on `U`, is supported on `T`, and its
  restriction to `V` is right orthogonal to `K`, so it vanishes on `V` by the affine case.

## Main results

* `exists_isCompactObject_derivedSupported_restrict_iso_biprod_shift` — the lift with support on
  an affine scheme.
* `Stacks.Duality.SupportedGeneration.exists_supported_generator_of_step` — the inductive step.
* `Stacks.Duality.SupportedGeneration.hasCompactSupportedGenerators` — the conclusion for every
  quasi-compact quasi-separated scheme.

## Implementation notes

All derived categories are the locally small ones,
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, at which compactness is tested against
direct sums indexed by the morphism universe. Supports are
handled stalkwise: `Stacks.Duality.SupportedGeneration.stalkHomologyDerivedRestrictIso` identifies
the stalks of the cohomology sheaves of a restriction along an open immersion with those of the
object.

No `@[stacks]` attribute is placed in this file: the statement of [Stacks, Tag 0A9A] asks for a
perfect generator, which is the companion file's.

## References

* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Tag 09IR](https://stacks.math.columbia.edu/tag/09IR)
* [Stacks Project, Tag 09SJ](https://stacks.math.columbia.edu/tag/09SJ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated ZeroObject TopologicalSpace

universe u

namespace Stacks.Duality.SupportedGeneration

open Stacks.Duality.OpenImmersion Stacks.Duality.QcqsGeneration Stacks.Duality.Supported

/-! ### Supports and restriction along open immersions -/

section Support

variable {Y U : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]

/-- The stalk at `x` of a cohomology sheaf of the restriction of `E` along an open immersion `j`
is the stalk at `j x` of the cohomology sheaf of `E`. -/
def stalkHomologyDerivedRestrictIso (E : DerivedCategory Y.Modules) (n : ℤ) (x : U) :
    (SheafOfModules.stalkAddCommGroupFunctor U.ringCatSheaf x).obj
        ((DerivedCategory.homologyFunctor U.Modules n).obj ((derivedRestrict j).obj E)) ≅
      (SheafOfModules.stalkAddCommGroupFunctor Y.ringCatSheaf (j x)).obj
        ((DerivedCategory.homologyFunctor Y.Modules n).obj E) :=
  (SheafOfModules.stalkAddCommGroupFunctor U.ringCatSheaf x).mapIso
      ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (Scheme.Modules.restrictFunctor j) n).app E) ≪≫
    (Scheme.Modules.restrictStalkNatIso j x).app _

/-- The restriction of an object of `D_T(𝒪_Y)` along an open immersion `j` lies in
`D_{j⁻¹T}`. -/
theorem derivedSupported_derivedRestrict {T : Set Y} {E : DerivedCategory Y.Modules}
    (hE : derivedSupported Y.ringCatSheaf T E) :
    derivedSupported U.ringCatSheaf (j ⁻¹' T) ((derivedRestrict j).obj E) :=
  fun n x hx => (hE n (j x) hx).of_iso (stalkHomologyDerivedRestrictIso j E n x)

/-- The stalks of the cohomology sheaves of `E` at the points of an open `j` along which `E`
restricts into `D_{j⁻¹T}` and which lie off `T` vanish. -/
theorem isZero_stalk_of_derivedSupported_derivedRestrict {T : Set Y}
    {E : DerivedCategory Y.Modules}
    (h : derivedSupported U.ringCatSheaf (j ⁻¹' T) ((derivedRestrict j).obj E)) (n : ℤ) (x : U)
    (hx : j x ∉ T) :
    IsZero ((SheafOfModules.stalkAddCommGroupFunctor Y.ringCatSheaf (j x)).obj
      ((DerivedCategory.homologyFunctor Y.Modules n).obj E)) :=
  (h n x hx).of_iso (stalkHomologyDerivedRestrictIso j E n x).symm

/-- An object of `D_S(𝒪_Y)` restricts to zero along an open immersion whose image misses `S`. -/
theorem isZero_derivedRestrict_of_derivedSupported' {S : Set Y} {E : DerivedCategory Y.Modules}
    (hE : derivedSupported Y.ringCatSheaf S E) (hj : ∀ x, j x ∉ S) :
    IsZero ((derivedRestrict j).obj E) :=
  (DerivedCategory.isZero_iff_forall_isZero_homology _).2 fun n =>
    Stacks.Cohomology.PushforwardRestriction.isZero_sheafOfModules_of_stalk_isZero
      U.ringCatSheaf _ fun x => (hE n (j x) (hj x)).of_iso (stalkHomologyDerivedRestrictIso j E n x)

/-- The stalks at the points of an open `j` of the cohomology sheaves of an object restricting to
zero along `j` vanish. -/
theorem isZero_stalk_of_isZero_derivedRestrict {E : DerivedCategory Y.Modules}
    (h : IsZero ((derivedRestrict j).obj E)) (n : ℤ) (x : U) :
    IsZero ((SheafOfModules.stalkAddCommGroupFunctor Y.ringCatSheaf (j x)).obj
      ((DerivedCategory.homologyFunctor Y.Modules n).obj E)) :=
  have _ := AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor_preservesZeroMorphisms
    U.ringCatSheaf x
  (Functor.map_isZero (SheafOfModules.stalkAddCommGroupFunctor U.ringCatSheaf x)
    ((DerivedCategory.isZero_iff_forall_isZero_homology _).1 h n)).of_iso
    (stalkHomologyDerivedRestrictIso j E n x).symm

/-- **The derived direct image along an open immersion `j` of an object of `D_{j⁻¹T}` lies in
`D_T`**, for `T` closed. Restricted to the open complement of `T`, it is the direct image of the
restriction of the object to the preimage of that complement ([Stacks, Tag 08FE] for open
immersions), which vanishes. -/
theorem derivedSupported_derivedPushforward {T : Set Y} (hT : IsClosed T)
    (M : DerivedCategory U.Modules) (hM : derivedSupported U.ringCatSheaf (j ⁻¹' T) M) :
    derivedSupported Y.ringCatSheaf T ((Stacks.Duality.derivedPushforward j).obj M) := by
  let O : Y.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  refine derivedSupported_of_isZero_derivedRestrict O T subset_rfl _ ?_
  have := Functor.preservesZeroMorphisms_of_isRightAdjoint
    (Stacks.Duality.derivedPushforward (j ∣_ O))
  exact (Functor.map_isZero _ (isZero_derivedRestrict_of_derivedSupported' (j ⁻¹ᵁ O).ι hM
    fun x => x.2)).of_iso
    (baseChangeIso j (j ⁻¹ᵁ O).ι O.ι (j ∣_ O) (isPullback_morphismRestrict j O).flip M)

/-- **Support is detected on an open containing the complement.** If the restriction of `E` along
an open immersion `j` whose image contains the complement of `T` lies in `D_{j⁻¹T}`, then `E`
lies in `D_T`. -/
theorem derivedSupported_of_derivedSupported_derivedRestrict {T : Set Y}
    (hTj : ∀ y : Y, y ∉ T → ∃ x, j x = y) {E : DerivedCategory Y.Modules}
    (h : derivedSupported U.ringCatSheaf (j ⁻¹' T) ((derivedRestrict j).obj E)) :
    derivedSupported Y.ringCatSheaf T E := fun n y hy => by
  obtain ⟨x, rfl⟩ := hTj y hy
  exact isZero_stalk_of_derivedSupported_derivedRestrict j h n x hy

/-- An object of `D(𝒪_Z)` all of whose cohomology sheaves have vanishing stalks everywhere is
zero: this is `D_∅(𝒪_Z) = 0`. -/
theorem isZero_of_derivedSupported_of_forall_not_mem {Z : Scheme.{u}} {T : Set Z}
    (hT : ∀ z, z ∉ T) {E : DerivedCategory Z.Modules} (hE : derivedSupported Z.ringCatSheaf T E) :
    IsZero E :=
  (DerivedCategory.isZero_iff_forall_isZero_homology _).2 fun n =>
    Stacks.Cohomology.PushforwardRestriction.isZero_sheafOfModules_of_stalk_isZero
      Z.ringCatSheaf _ fun z => hE n z (hT z)

/-- The zero object lies in `D_T(𝒪_Z)`. -/
theorem derivedSupported_of_isZero {Z : Scheme.{u}} (T : Set Z) {E : DerivedCategory Z.Modules}
    (h : IsZero E) : derivedSupported Z.ringCatSheaf T E := fun n z _ =>
  have _ := AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor_preservesZeroMorphisms
    Z.ringCatSheaf z
  Functor.map_isZero (SheafOfModules.stalkAddCommGroupFunctor Z.ringCatSheaf z)
    ((DerivedCategory.isZero_iff_forall_isZero_homology _).1 h n)

section Closure

variable {X : TopCat.{u}} {𝒪 : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} {T : Set X}
  [HasDerivedCategory.{u} (SheafOfModules.{u} 𝒪)]

/-- `D_T(𝒪)` is closed under isomorphisms; the form in which it is used along the two
definitionally equal spellings `SheafOfModules 𝒪_Z` and `Z.Modules` of the modules. -/
private theorem derivedSupported_of_iso {M N : DerivedCategory (SheafOfModules.{u} 𝒪)}
    (e : M ≅ N) (h : derivedSupported 𝒪 T M) : derivedSupported 𝒪 T N :=
  (derivedSupported 𝒪 T).prop_of_iso e h

/-- `D_T(𝒪)` is closed under the shift. -/
private theorem derivedSupported_shift {M : DerivedCategory (SheafOfModules.{u} 𝒪)} (n : ℤ)
    (h : derivedSupported 𝒪 T M) : derivedSupported 𝒪 T (M⟦n⟧) :=
  (derivedSupported 𝒪 T).le_shift n _ h

/-- `D_T(𝒪)` is closed under extensions. -/
private theorem derivedSupported_ext₂ (Tr : Triangle (DerivedCategory (SheafOfModules.{u} 𝒪)))
    (hTr : Tr ∈ distTriang _) (h₁ : derivedSupported 𝒪 T Tr.obj₁)
    (h₃ : derivedSupported 𝒪 T Tr.obj₃) : derivedSupported 𝒪 T Tr.obj₂ :=
  ObjectProperty.ext_of_isTriangulatedClosed₂ _ _ hTr h₁ h₃

/-- `D_T(𝒪)` is closed under cones. -/
private theorem derivedSupported_ext₃ (Tr : Triangle (DerivedCategory (SheafOfModules.{u} 𝒪)))
    (hTr : Tr ∈ distTriang _) (h₁ : derivedSupported 𝒪 T Tr.obj₁)
    (h₂ : derivedSupported 𝒪 T Tr.obj₂) : derivedSupported 𝒪 T Tr.obj₃ :=
  ObjectProperty.ext_of_isTriangulatedClosed₃ _ _ hTr h₁ h₂

end Closure

/-- `D_T(𝒪_Z)` is closed under isomorphisms of `D_QCoh(𝒪_Z)`. -/
private theorem derivedSupported_obj_of_iso {Z : Scheme.{u}} {T : Set Z}
    {M N : Stacks.Duality.quasiCoherentDerivedCategory Z} (e : M ≅ N)
    (h : derivedSupported Z.ringCatSheaf T M.obj) : derivedSupported Z.ringCatSheaf T N.obj :=
  derivedSupported_of_iso ((DerivedCategoryB.derivedCategoryB (A := Z.Modules)
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).ι.mapIso e) h

/-- The underlying object of a zero object of `D_QCoh(𝒪_Z)` is zero. -/
private theorem isZero_obj_of_isZero {Z : Scheme.{u}}
    {N : Stacks.Duality.quasiCoherentDerivedCategory Z} (h : IsZero N) : IsZero N.obj :=
  (DerivedCategoryB.derivedCategoryB (A := Z.Modules)
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).ι.map_isZero h

/-- `Rj_*` on the quasi-coherent derived categories of a quasi-compact open immersion is
additive. -/
private theorem additive_quasiCoherentDerivedPushforward {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [AlgebraicGeometry.QuasiCompact j] [CompactSpace X] :
    (Stacks.Duality.quasiCoherentDerivedPushforward j
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs j)).Additive :=
  (restrictedDerivedRestrictAdjunction j).right_adjoint_additive

/-- Preimages along two equal composites agree. -/
private theorem preimage_preimage_eq_of_comp_eq {A B C D : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ D}
    {c : A ⟶ C} {d : C ⟶ D} (h : a ≫ b = c ≫ d) (T : Set D) :
    a ⁻¹' (b ⁻¹' T) = c ⁻¹' (d ⁻¹' T) := by
  ext p
  exact Iff.of_eq (congrArg (· ∈ T) congr($h p))

/-- `D_T(𝒪_Z)` is closed under the direct sums of `D_QCoh(𝒪_Z)`. -/
theorem derivedSupported_biprod {Z : Scheme.{u}} {T : Set Z}
    {K L : Stacks.Duality.quasiCoherentDerivedCategory Z}
    (hK : derivedSupported Z.ringCatSheaf T K.obj) (hL : derivedSupported Z.ringCatSheaf T L.obj) :
    derivedSupported Z.ringCatSheaf T (K ⊞ L).obj :=
  derivedSupported_ext₂ _ ((DerivedCategoryB.derivedCategoryB (A := Z.Modules)
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).ι.map_distinguished _
      (binaryBiproductTriangle_distinguished K L)) hK hL

/-- `D_T(𝒪_Z)` contains `K ⊕ K[1]` with `K`, for `K` in `D_QCoh(𝒪_Z)`. -/
theorem derivedSupported_biprod_shift {Z : Scheme.{u}} {T : Set Z}
    (K : Stacks.Duality.quasiCoherentDerivedCategory Z)
    (hK : derivedSupported Z.ringCatSheaf T K.obj) :
    derivedSupported Z.ringCatSheaf T (K ⊞ K⟦(1 : ℤ)⟧).obj := by
  let ι := (DerivedCategoryB.derivedCategoryB (A := Z.Modules)
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).ι
  exact derivedSupported_ext₂ _
    (ι.map_distinguished _ (binaryBiproductTriangle_distinguished K (K⟦(1 : ℤ)⟧))) hK
    (derivedSupported_of_iso ((ι.commShiftIso (1 : ℤ)).app K).symm
      (derivedSupported_shift (1 : ℤ) hK))

end Support

/-! ### Restriction along a composite of open immersions -/

/-- Restriction to `D_QCoh` along a composite `a ≫ b` of open immersions is restriction along `b`
followed by restriction along `a`. -/
def restrictedDerivedRestrictCompIso {X₁ X₂ X₃ : Scheme.{u}} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃)
    [IsOpenImmersion a] [IsOpenImmersion b] (K : Stacks.Duality.quasiCoherentDerivedCategory X₃) :
    (restrictedDerivedRestrict (a ≫ b)).obj K ≅
      (restrictedDerivedRestrict a).obj ((restrictedDerivedRestrict b).obj K) :=
  (DerivedCategoryB.derivedCategoryB (A := X₁.Modules)
    (SheafOfModules.isQuasicoherent X₁.ringCatSheaf)).fullyFaithfulι.preimageIso
    ((Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso _ _
        (Scheme.Modules.restrictFunctorComp a b)).app K.obj ≪≫
      (Stacks.DerivedQCoh.mapDerivedCategoryComp (Scheme.Modules.restrictFunctor b)
        (Scheme.Modules.restrictFunctor a)).app K.obj)

/-- Restriction to `D_QCoh` along equal open immersions. -/
def restrictedDerivedRestrictCongrIso {X₁ X₂ : Scheme.{u}} {a b : X₁ ⟶ X₂} (h : a = b)
    [IsOpenImmersion a] [IsOpenImmersion b] (K : Stacks.Duality.quasiCoherentDerivedCategory X₂) :
    (restrictedDerivedRestrict a).obj K ≅ (restrictedDerivedRestrict b).obj K :=
  (DerivedCategoryB.derivedCategoryB (A := X₁.Modules)
    (SheafOfModules.isQuasicoherent X₁.ringCatSheaf)).fullyFaithfulι.preimageIso
    ((Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso _ _
        (Scheme.Modules.restrictFunctorCongr h)).app K.obj)

/-! ### Two open immersions covering a scheme -/

section Pair

variable {Y U V W : Scheme.{u}} (jU : U ⟶ Y) (jV : V ⟶ Y) (iU : W ⟶ U) (iV : W ⟶ V)
  [IsOpenImmersion jU] [IsOpenImmersion jV] [IsOpenImmersion iU] [IsOpenImmersion iV]
  (hsq : IsPullback iU iV jU jV) (hcov : ∀ y : Y, (∃ x, jU x = y) ∨ (∃ x, jV x = y))

include hcov in
/-- Two open immersions covering `Y` jointly detect isomorphisms of `D(𝒪_Y)`. -/
theorem isIso_of_isIso_derivedRestrict_pair {E F : DerivedCategory Y.Modules} (φ : E ⟶ F)
    (hφU : IsIso ((derivedRestrict jU).map φ)) (hφV : IsIso ((derivedRestrict jV).map φ)) :
    IsIso φ := by
  let Us : Bool → Scheme.{u} := fun b => cond b U V
  let js : ∀ b, Us b ⟶ Y := fun b => match b with
    | true => jU
    | false => jV
  have : ∀ b, IsOpenImmersion (js b) := fun b => by cases b <;> (dsimp [js]; infer_instance)
  refine isIso_of_isIso_derivedRestrict φ js (fun y => ?_) fun b => ?_
  · rcases hcov y with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact ⟨true, x, hx⟩
    · exact ⟨false, x, hx⟩
  · cases b
    · exact hφV
    · exact hφU

include hcov in
/-- An object of `D(𝒪_Y)` restricting into `D_{j⁻¹T}` along two open immersions covering `Y`
lies in `D_T`. -/
theorem derivedSupported_of_derivedSupported_restrict_pair {T : Set Y}
    {E : DerivedCategory Y.Modules}
    (hU : derivedSupported U.ringCatSheaf (jU ⁻¹' T) ((derivedRestrict jU).obj E))
    (hV : derivedSupported V.ringCatSheaf (jV ⁻¹' T) ((derivedRestrict jV).obj E)) :
    derivedSupported Y.ringCatSheaf T E := fun n y hy => by
  rcases hcov y with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact isZero_stalk_of_derivedSupported_derivedRestrict jU hU n x hy
  · exact isZero_stalk_of_derivedSupported_derivedRestrict jV hV n x hy

include hsq hcov in
/-- **An object of `D_QCoh(𝒪_Y)` vanishing on `V` comes from `U`**, for two open immersions
covering `Y` with Cartesian overlap: the unit `N ⟶ Rj_{U,*}(N|_U)` is invertible. It is so on `U`
because `Rj_{U,*}` is fully faithful, and on `V` both sides vanish, the target by base change to
the overlap. -/
theorem isIso_unit_of_isZero_restrict_pair [CompactSpace Y] [AlgebraicGeometry.QuasiCompact jU]
    (N : Stacks.Duality.quasiCoherentDerivedCategory Y)
    (hN : IsZero ((restrictedDerivedRestrict jV).obj N)) :
    IsIso ((restrictedDerivedRestrictAdjunction jU).unit.app N) := by
  rw [isIso_restrictedDerivedRestrictAdjunction_unit_app_iff]
  have hNV : IsZero ((derivedRestrict jV).obj N.obj) := isZero_obj_of_isZero hN
  refine isIso_of_isIso_derivedRestrict_pair jU jV hcov _ ?_ ?_
  · exact isIso_map_unit_of_isIso_counit (derivedRestrictPushforwardAdjunction jU) N.obj
      inferInstance
  · have : (Stacks.Duality.derivedPushforward iV).IsRightAdjoint := inferInstance
    refine isIso_of_source_target_iso_zero _ hNV.isoZero ?_
    exact baseChangeIso jU iU jV iV hsq _ ≪≫
      ((Stacks.Duality.derivedPushforward iV).map_isZero
        (isZero_derivedRestrict_comp_of_isZero iU iV jU jV hsq.w hNV)).isoZero

include hsq hcov in
/-- **Extending a compact object by zero across a second open.** Let `Y` be covered by two
quasi-compact opens `U` and `V` with Cartesian overlap `W`, and let `M` be a compact object of
`D_QCoh(𝒪_U)` vanishing on `W`. Then `Rj_{U,*}M` is a compact object of `D_QCoh(𝒪_Y)` restricting
to `M` on `U` and to zero on `V`: its restriction to `V` is the direct image of `M|_W = 0` by base
change, and compactness is local
(`CategoryTheory.Pretriangulated.isCompactObject_of_isCompactObject_restrict`). -/
theorem exists_isCompactObject_extend [CompactSpace Y] [AlgebraicGeometry.QuasiCompact jU]
    [AlgebraicGeometry.QuasiCompact jV]
    (M : Stacks.Duality.quasiCoherentDerivedCategory U) (hM : IsCompactObject.{u} M)
    (hMW : IsZero ((restrictedDerivedRestrict iU).obj M)) :
    ∃ M' : Stacks.Duality.quasiCoherentDerivedCategory Y, IsCompactObject.{u} M' ∧
      Nonempty ((restrictedDerivedRestrict jU).obj M' ≅ M) ∧
      IsZero ((restrictedDerivedRestrict jV).obj M') := by
  let adjU := restrictedDerivedRestrictAdjunction jU
  let adjV := restrictedDerivedRestrictAdjunction jV
  let : (Stacks.Duality.quasiCoherentDerivedPushforward jU
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).CommShift ℤ :=
    adjU.rightAdjointCommShift ℤ
  have := additive_quasiCoherentDerivedPushforward jU
  have := additive_quasiCoherentDerivedPushforward jV
  have := preservesColimitsOfShape_discrete_restrictedDerivedPushforward jU
  have := preservesColimitsOfShape_discrete_restrictedDerivedPushforward jV
  let M' := (Stacks.Duality.quasiCoherentDerivedPushforward jU
    (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).obj M
  have hV : IsZero ((restrictedDerivedRestrict jV).obj M') := by
    refine isZero_fullSubcategory_of_isZero_obj ?_
    have := Functor.preservesZeroMorphisms_of_isRightAdjoint
      (Stacks.Duality.derivedPushforward iV)
    exact (Functor.map_isZero _ (isZero_obj_of_isZero hMW)).of_iso
      (baseChangeIso jU iU jV iV hsq M.obj)
  refine ⟨M', isCompactObject_of_isCompactObject_restrict adjU adjV
    (isIso_unit_of_isZero_restrict_pair jU jV iU iV hsq hcov) M' ?_ ?_,
    ⟨asIso (adjU.counit.app M)⟩, hV⟩
  · exact isCompactObject_of_iso (asIso (adjU.counit.app M)) hM
  · exact isCompactObject_of_iso hV.isoZero
      (isCompactObject_zero' (T := Stacks.Duality.quasiCoherentDerivedCategory V))

end Pair

/-! ### Lifting a compact object with support from an open of an affine scheme -/

section AffineLift

open Stacks.Koszul.Truncation

variable {A : Type u} [CommRing A]

/-- **Lifting a compact object with support from `D(f₁) ∪ … ∪ D(f_r)` to `Spec A`.** Let
`W = D(f₁) ∪ … ∪ D(f_r) ⊆ Spec A`, let `S ⊆ Spec A` be closed with quasi-compact complement, and
let `g₁, …, g_s` cut out `(Spec A ∖ W) ∩ S`. For every compact object `M` of `D_QCoh(𝒪_W)`
supported on `W ∩ S` there is a compact object `Q` of `D_QCoh(𝒪_{Spec A})` supported on `S` whose
restriction to `W` is `M ⊕ M[1]`.

`M` is first extended by zero to a compact object `M'` on
`W' = W ∪ (Spec A ∖ S) = D(g₁) ∪ … ∪ D(g_s)`
(`Stacks.Duality.SupportedGeneration.exists_isCompactObject_extend`), then `M'` is lifted to `Q`
with `Q|_{W'} = M' ⊕ M'[1]` by [Stacks, Tag 08EK]
(`Stacks.Duality.QcqsGeneration.exists_isCompactObject_restrict_iso_biprod_shift`). Off `S` the
object `Q` is `M' ⊕ M'[1]` restricted to `Spec A ∖ S`, which vanishes. -/
theorem exists_isCompactObject_derivedSupported_restrict_iso_biprod_shift {r s : ℕ}
    (f : Fin r → A) (g : Fin s → A) (S : Set (Spec (CommRingCat.of A))) (hS : IsClosed S)
    (hSc : IsCompact Sᶜ)
    (hg : ((openComplement g : (Spec (CommRingCat.of A)).Opens) : Set (Spec (CommRingCat.of A))) =
      ((openComplement f : (Spec (CommRingCat.of A)).Opens) : Set (Spec (CommRingCat.of A))) ∪ Sᶜ)
    (M : Stacks.Duality.quasiCoherentDerivedCategory (openComplement f).toScheme)
    (hM : IsCompactObject.{u} M)
    (hMS : derivedSupported (openComplement f).toScheme.ringCatSheaf
      ((openComplement f).ι ⁻¹' S) M.obj) :
    ∃ Q : Stacks.Duality.quasiCoherentDerivedCategory (Spec (CommRingCat.of A)),
      IsCompactObject.{u} Q ∧ derivedSupported (Spec (CommRingCat.of A)).ringCatSheaf S Q.obj ∧
        Nonempty ((restrictedDerivedRestrict (openComplement f).ι).obj Q ≅ M ⊞ M⟦(1 : ℤ)⟧) := by
  let X := Spec (CommRingCat.of A)
  let W : X.Opens := openComplement f
  let W' : X.Opens := openComplement g
  let O : X.Opens := ⟨Sᶜ, hS.isOpen_compl⟩
  have hWW : W ≤ W' := fun x hx => hg.superset (Or.inl hx)
  have hOW : O ≤ W' := fun x hx => hg.superset (Or.inr hx)
  have : CompactSpace O.toScheme := isCompact_iff_compactSpace.mp hSc
  have : QuasiSeparatedSpace W'.toScheme := W'.ι.isOpenEmbedding.quasiSeparatedSpace
  let iW := X.homOfLE hWW
  let iO := X.homOfLE hOW
  have hsq := AlgebraicGeometry.isPullback_opens_inf_le hWW hOW
  have hcov : ∀ y : W'.toScheme, (∃ x, iW x = y) ∨ (∃ x, iO x = y) := fun y => by
    have hy : y.1 ∈ (W' : Set X) := y.2
    rw [hg] at hy
    rcases hy with hy | hy
    · exact Or.inl ⟨⟨y.1, hy⟩, Subtype.ext (X.homOfLE_apply hWW ⟨y.1, hy⟩)⟩
    · exact Or.inr ⟨⟨y.1, hy⟩, Subtype.ext (X.homOfLE_apply hOW ⟨y.1, hy⟩)⟩
  have hMWO : IsZero ((restrictedDerivedRestrict (X.homOfLE (inf_le_left : W ⊓ O ≤ W))).obj M) :=
    isZero_fullSubcategory_of_isZero_obj
      (isZero_derivedRestrict_of_derivedSupported' _ hMS fun x hx => by
        have h2 : (x.1 : X) ∈ (O : Set X) := x.2.2
        refine h2 ?_
        have e := congr($(X.homOfLE_ι (inf_le_left : W ⊓ O ≤ W)) x)
        change W.ι (X.homOfLE (inf_le_left : W ⊓ O ≤ W) x) ∈ S at hx
        exact (congrArg (· ∈ S) e).mp hx)
  obtain ⟨M', hM'c, ⟨eW⟩, hO⟩ := exists_isCompactObject_extend iW iO _ _ hsq hcov M hM hMWO
  obtain ⟨Q, hQc, ⟨eQ⟩⟩ := exists_isCompactObject_restrict_iso_biprod_shift g M' hM'c
  -- `M'` is supported on `S`
  have hM'S : derivedSupported W'.toScheme.ringCatSheaf (W'.ι ⁻¹' S) M'.obj := fun n y hy => by
    rcases hcov y with ⟨z, rfl⟩ | ⟨z, rfl⟩
    · have hz : derivedSupported W.toScheme.ringCatSheaf (iW ⁻¹' (W'.ι ⁻¹' S))
          ((derivedRestrict iW).obj M'.obj) := by
        rw [preimage_preimage_eq_of_comp_eq ((X.homOfLE_ι hWW).trans (Category.comp_id _).symm) S]
        exact derivedSupported_obj_of_iso eW.symm hMS
      exact isZero_stalk_of_derivedSupported_derivedRestrict iW hz n z hy
    · exact isZero_stalk_of_isZero_derivedRestrict iO (isZero_obj_of_isZero hO) n z
  have hQW' : derivedSupported W'.toScheme.ringCatSheaf (W'.ι ⁻¹' S)
      ((derivedRestrict W'.ι).obj Q.obj) :=
    derivedSupported_obj_of_iso eQ.symm (derivedSupported_biprod_shift M' hM'S)
  have : PreservesBinaryBiproducts (restrictedDerivedRestrict iW) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  refine ⟨Q, hQc, derivedSupported_of_derivedSupported_derivedRestrict W'.ι
    (fun y hy => ⟨⟨y, hOW hy⟩, rfl⟩) hQW', ⟨?_⟩⟩
  exact restrictedDerivedRestrictCongrIso (X.homOfLE_ι hWW).symm Q ≪≫
    restrictedDerivedRestrictCompIso iW W'.ι Q ≪≫
    (restrictedDerivedRestrict iW).mapIso eQ ≪≫
    (restrictedDerivedRestrict iW).mapBiprod _ _ ≪≫
    biprod.mapIso eW (((restrictedDerivedRestrict iW).commShiftIso (1 : ℤ)).app M' ≪≫
      (shiftFunctor _ (1 : ℤ)).mapIso eW)

end AffineLift

/-! ### The inductive step -/

section Step

open Stacks.Koszul.Truncation

variable {Y : Scheme.{u}} [QuasiSeparatedSpace Y] [CompactSpace Y]
  {U : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U] (jU : U ⟶ Y) [IsOpenImmersion jU]
  {A : Type u} [CommRing A] (jV : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion jV]
  {r : ℕ} (f : Fin r → A) (iU : (openComplement f).toScheme ⟶ U) [IsOpenImmersion iU]
  (hsq : IsPullback iU (openComplement f).ι jU jV)
  (hcov : ∀ y : Y, (∃ x, jU x = y) ∨ (∃ x, jV x = y))

include hsq hcov in
/-- **The inductive step of [Stacks, Tag 0A9A]**, with the generator exhibited as a compact object
of `D_QCoh`. Let `Y` be a quasi-compact quasi-separated scheme covered by a quasi-compact open
`j_U : U ⟶ Y` and an affine open `j_V : Spec A ⟶ Y` whose overlap is
`W = D(f₁) ∪ … ∪ D(f_r) ⊆ Spec A`, let `T ⊆ Y` be closed, and let `g₁, …, g_s ∈ A` cut out
`(Spec A ∖ W) ∩ j_V⁻¹T`. If `P` is a compact object of `D_QCoh(𝒪_U)` supported on `T ∩ U` which
generates `D_{QCoh,T ∩ U}(𝒪_U)`, then `D_{QCoh,T}(𝒪_Y)` is generated by a compact object of
`D_QCoh(𝒪_Y)` supported on `T`.

This is the source's argument with Thomason's trick in place of [Stacks, Tag 09IM]. The object
`P ⊕ P[1]` on `U` and a compact object `Q` on `Spec A` supported on `j_V⁻¹T` with
`Q|_W = P|_W ⊕ P|_W[1]` (`exists_isCompactObject_derivedSupported_restrict_iso_biprod_shift`)
glue to `R`; the Koszul complex `K` on the `g_j`, which is supported on `(Spec A ∖ W) ∩ j_V⁻¹T`,
and `0` on `U` glue to `K'` (the source's `R(V → X)_*K`). The generator is `K' ⊕ R`. If `E` in
`D_{QCoh,T}(𝒪_Y)` receives no nonzero map from its shifts, then `E|_V` is right orthogonal to `K`;
the cone `C` of `E ⟶ Rj_{U,*}(E|_U)` vanishes on `U`, is supported on `T`, and `C|_V` is right
orthogonal to `K`, so `C|_V` is an object of `D_{QCoh,V(g)}` orthogonal to `K`, which vanishes by
the affine case
(`Stacks.Duality.Supported.isZero_of_quasiCoherentSupported_of_forall_hom_koszulObject_eq_zero`);
hence `E = Rj_{U,*}(E|_U)` ("small detail omitted" in the source), and then `E|_U` is right
orthogonal to `P`, hence zero. -/
theorem exists_supported_generator_of_step {T : Set Y} (hTcl : IsClosed T) {s : ℕ}
    (g : Fin s → A)
    (hg : ((openComplement g : (Spec (CommRingCat.of A)).Opens) : Set (Spec (CommRingCat.of A))) =
      ((openComplement f : (Spec (CommRingCat.of A)).Opens) : Set (Spec (CommRingCat.of A))) ∪
        (jV ⁻¹' T)ᶜ)
    (hTV : IsCompact (jV ⁻¹' T)ᶜ)
    (P : Stacks.Duality.quasiCoherentDerivedCategory U) (hPc : IsCompactObject.{u} P)
    (hPT : derivedSupported U.ringCatSheaf (jU ⁻¹' T) P.obj)
    (hPgen : ∀ E : Stacks.Duality.quasiCoherentDerivedCategory U,
      derivedSupported U.ringCatSheaf (jU ⁻¹' T) E.obj →
        (∀ (n : ℤ) (g' : P⟦n⟧ ⟶ E), g' = 0) → IsZero E) :
    ∃ G : Stacks.Duality.quasiCoherentDerivedCategory Y, IsCompactObject.{u} G ∧
      derivedSupported Y.ringCatSheaf T G.obj ∧
      ∀ E : Stacks.Duality.quasiCoherentDerivedCategory Y, derivedSupported Y.ringCatSheaf T E.obj →
        (∀ (n : ℤ) (g' : G⟦n⟧ ⟶ E), g' = 0) → IsZero E := by
  -- the four adjunctions
  let adjU := restrictedDerivedRestrictAdjunction jU
  let adjV := restrictedDerivedRestrictAdjunction jV
  let adjU' := restrictedDerivedRestrictAdjunction iU
  let adjV' := restrictedDerivedRestrictAdjunction (openComplement f).ι
  let : (Stacks.Duality.quasiCoherentDerivedPushforward jU
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).CommShift ℤ :=
    adjU.rightAdjointCommShift ℤ
  let : adjU.CommShift ℤ := adjU.commShift_of_leftAdjoint ℤ
  let : (Stacks.Duality.quasiCoherentDerivedPushforward jV
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jV)).CommShift ℤ :=
    adjV.rightAdjointCommShift ℤ
  let : adjV.CommShift ℤ := adjV.commShift_of_leftAdjoint ℤ
  let : adjV.IsTriangulated := Adjunction.IsTriangulated.mk' adjV
  have := adjV.isTriangulated_rightAdjoint
  have : PreservesBinaryBiproducts (restrictedDerivedRestrict iU) :=
    have := adjU'.leftAdjoint_preservesColimits
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have := additive_quasiCoherentDerivedPushforward jU
  have := additive_quasiCoherentDerivedPushforward jV
  have := additive_quasiCoherentDerivedPushforward iU
  have := preservesColimitsOfShape_discrete_restrictedDerivedPushforward jU
  have := preservesColimitsOfShape_discrete_restrictedDerivedPushforward jV
  have := preservesColimitsOfShape_discrete_restrictedDerivedPushforward iU
  -- base change
  let βVU : ∀ A' : Stacks.Duality.quasiCoherentDerivedCategory U,
      (restrictedDerivedRestrict jV).obj ((Stacks.Duality.quasiCoherentDerivedPushforward jU
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).obj A') ≅
      (Stacks.Duality.quasiCoherentDerivedPushforward (openComplement f).ι
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs
          (openComplement f).ι)).obj ((restrictedDerivedRestrict iU).obj A') := fun A' =>
    (DerivedCategoryB.derivedCategoryB (A := Spec (CommRingCat.of A) |>.Modules)
      (SheafOfModules.isQuasicoherent
        (Spec (CommRingCat.of A)).ringCatSheaf)).fullyFaithfulι.preimageIso
      (baseChangeIso jU iU jV (openComplement f).ι hsq A'.obj)
  let βUV : ∀ Q' : Stacks.Duality.quasiCoherentDerivedCategory (Spec (CommRingCat.of A)),
      (restrictedDerivedRestrict jU).obj ((Stacks.Duality.quasiCoherentDerivedPushforward jV
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jV)).obj Q') ≅
      (Stacks.Duality.quasiCoherentDerivedPushforward iU
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs iU)).obj
          ((restrictedDerivedRestrict (openComplement f).ι).obj Q') := fun Q' =>
    (DerivedCategoryB.derivedCategoryB (A := U.Modules)
      (SheafOfModules.isQuasicoherent U.ringCatSheaf)).fullyFaithfulι.preimageIso
      (baseChangeIso jV (openComplement f).ι jU iU hsq.flip Q'.obj)
  have hker : ∀ N : Stacks.Duality.quasiCoherentDerivedCategory Y,
      IsZero ((restrictedDerivedRestrict jV).obj N) → IsIso (adjU.unit.app N) :=
    isIso_unit_of_isZero_restrict jU jV f iU hsq hcov
  -- the lifts and the glued objects
  let ιY := (DerivedCategoryB.derivedCategoryB (A := Y.Modules)
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι
  let ιU := (DerivedCategoryB.derivedCategoryB (A := U.Modules)
    (SheafOfModules.isQuasicoherent U.ringCatSheaf)).ι
  let ιV := (DerivedCategoryB.derivedCategoryB (A := (Spec (CommRingCat.of A)).Modules)
    (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of A)).ringCatSheaf)).ι
  have hpt : ∀ p, jU (iU p) = jV ((openComplement f).ι p) := fun p => congr($(hsq.w) p)
  -- the lift `Q` of `P|_W ⊕ P|_W[1]`, supported on `j_V⁻¹T`, and the glued object `R`
  have hPWS : derivedSupported (openComplement f).toScheme.ringCatSheaf
      ((openComplement f).ι ⁻¹' (jV ⁻¹' T)) ((restrictedDerivedRestrict iU).obj P).obj := by
    rw [← preimage_preimage_eq_of_comp_eq hsq.w T]
    exact derivedSupported_derivedRestrict iU hPT
  obtain ⟨Q, hQc, hQS, ⟨eQ⟩⟩ :=
    exists_isCompactObject_derivedSupported_restrict_iso_biprod_shift f g (jV ⁻¹' T)
      (hTcl.preimage jV.continuous) hTV hg _
      (isCompactObject_map_of_adjunction adjU' hPc) hPWS
  let φ : (restrictedDerivedRestrict iU).obj (P ⊞ P⟦(1 : ℤ)⟧) ≅
      (restrictedDerivedRestrict (openComplement f).ι).obj Q :=
    (restrictedDerivedRestrict iU).mapBiprod _ _ ≪≫
      biprod.mapIso (Iso.refl _) (((restrictedDerivedRestrict iU).commShiftIso (1 : ℤ)).app _) ≪≫
      eQ.symm
  obtain ⟨R, ⟨eRU⟩, ⟨eRV⟩⟩ := exists_glue adjU adjV adjV' βVU βUV (P ⊞ P⟦(1 : ℤ)⟧) Q φ
  -- the Koszul complex on the `g_j` and the glued object `K'`
  have hgc : ∀ x : Spec (CommRingCat.of A), x ∉ (jV ⁻¹' T) →
      x ∈ ((openComplement g : (Spec (CommRingCat.of A)).Opens) : Set (Spec (CommRingCat.of A))) :=
    fun x hx => hg.superset (Or.inr hx)
  have hKS : derivedSupported (Spec (CommRingCat.of A)).ringCatSheaf
      (((openComplement g : (Spec (CommRingCat.of A)).Opens) :
        Set (Spec (CommRingCat.of A)))ᶜ) (koszulQC g).obj :=
    (derivedSupported _ _).prop_of_iso (koszulQC_obj_iso g).symm (derivedSupported_koszulObject g)
  have hKW : IsZero ((restrictedDerivedRestrict (openComplement f).ι).obj (koszulQC g)) :=
    isZero_fullSubcategory_of_isZero_obj
      (isZero_derivedRestrict_of_derivedSupported' _ hKS fun x hx =>
        hx (hg.superset (Or.inl x.2)))
  obtain ⟨K', ⟨eK'U⟩, ⟨eK'V⟩⟩ := exists_glue adjU adjV adjV' βVU βUV 0 (koszulQC g)
    (((restrictedDerivedRestrict iU).map_isZero (isZero_zero _)).iso hKW)
  have hK'U0 : IsZero ((restrictedDerivedRestrict jU).obj K') :=
    (isZero_zero _).of_iso eK'U
  -- compactness and support of `R` and `K'`
  have hK'c : IsCompactObject.{u} K' :=
    isCompactObject_of_isCompactObject_restrict adjU adjV hker K'
      (isCompactObject_of_iso eK'U
        (isCompactObject_zero' (T := Stacks.Duality.quasiCoherentDerivedCategory U)))
      (isCompactObject_of_iso eK'V (isCompactObject_koszulQC g))
  have hRc : IsCompactObject.{u} R :=
    isCompactObject_of_isCompactObject_restrict adjU adjV hker R
      (isCompactObject_of_iso eRU (isCompactObject_biprod hPc (isCompactObject_shift hPc 1)))
      (isCompactObject_of_iso eRV hQc)
  have hRT : derivedSupported Y.ringCatSheaf T R.obj :=
    derivedSupported_of_derivedSupported_restrict_pair jU jV hcov
      (derivedSupported_obj_of_iso eRU.symm (derivedSupported_biprod_shift P hPT))
      (derivedSupported_obj_of_iso eRV.symm hQS)
  have hK'T : derivedSupported Y.ringCatSheaf T K'.obj :=
    derivedSupported_of_derivedSupported_restrict_pair jU jV hcov
      (derivedSupported_of_isZero _ (isZero_obj_of_isZero hK'U0))
      (derivedSupported_obj_of_iso eK'V.symm fun n x hx => hKS n x fun hx' => hx' (hgc x hx))
  refine ⟨K' ⊞ R, isCompactObject_biprod hK'c hRc, derivedSupported_biprod hK'T hRT, ?_⟩
  intro E hET hE
  have hsum : ∀ {X : Stacks.Duality.quasiCoherentDerivedCategory Y} (i : X ⟶ K' ⊞ R)
      (p : K' ⊞ R ⟶ X), i ≫ p = 𝟙 X → ∀ (n : ℤ) (h : X⟦n⟧ ⟶ E), h = 0 :=
    fun i p hip n h => by
      simpa [← Functor.map_comp_assoc, hip] using congrArg ((shiftFunctor _ n).map i ≫ ·)
        (hE n ((shiftFunctor _ n).map p ≫ h))
  have hK'0 := hsum biprod.inl biprod.fst (by simp)
  have hR0 := hsum biprod.inr biprod.snd (by simp)
  -- Step 1: `E|_{Spec A}` is right orthogonal to the Koszul complex
  have h1 : ∀ (n : ℤ) (g' : (koszulQC g)⟦n⟧ ⟶ (restrictedDerivedRestrict jV).obj E),
      g' = 0 := by
    intro n g'
    obtain ⟨N, π, δ, hTr⟩ := distinguished_cocone_triangle (adjV.unit.app E)
    have hNV : IsZero ((restrictedDerivedRestrict jV).obj N) :=
      Triangle.isZero₃_of_isIso₁ _ ((restrictedDerivedRestrict jV).map_distinguished _ hTr)
        (isIso_map_unit_of_isIso_counit adjV E inferInstance)
    have hK'n : IsZero ((restrictedDerivedRestrict jU).obj (K'⟦n⟧)) :=
      ((shiftFunctor _ n).map_isZero hK'U0).of_iso
        (((restrictedDerivedRestrict jU).commShiftIso n).app K')
    let g₁ : (restrictedDerivedRestrict jV).obj (K'⟦n⟧) ⟶ (restrictedDerivedRestrict jV).obj E :=
      ((restrictedDerivedRestrict jV).commShiftIso n).hom.app K' ≫
        (shiftFunctor _ n).map eK'V.hom ≫ g'
    have hπ : adjV.homEquiv _ _ g₁ ≫ π = 0 :=
      eq_zero_of_isZero_obj_of_isIso_unit adjU hK'n (hker N hNV) _
    obtain ⟨h, hh⟩ := Triangle.coyoneda_exact₂ _ hTr _ hπ
    have hg₁ : g₁ = 0 := by
      rw [← (adjV.homEquiv _ _).symm_apply_apply g₁, hh, hK'0 n h, zero_comp,
        Adjunction.homEquiv_counit, Functor.map_zero, zero_comp]
    have : g' = (shiftFunctor _ n).map eK'V.inv ≫
        ((restrictedDerivedRestrict jV).commShiftIso n).inv.app K' ≫ g₁ := by
      simp [g₁, ← Functor.map_comp_assoc]
    rw [this, hg₁, comp_zero, comp_zero]
  -- Step 2: `E ≅ Rj_{U,*}(E|_U)`
  have h2 : IsIso (adjU.unit.app E) := by
    obtain ⟨C, g₂, g₃, hTr⟩ := distinguished_cocone_triangle (adjU.unit.app E)
    have hCU : IsZero ((restrictedDerivedRestrict jU).obj C) :=
      Triangle.isZero₃_of_isIso₁ _ ((restrictedDerivedRestrict jU).map_distinguished _ hTr)
        (isIso_map_unit_of_isIso_counit adjU E inferInstance)
    have hE1 : ((ObjectProperty.singleton (koszulQC g)).shiftClosure ℤ).rightOrthogonal
        ((restrictedDerivedRestrict jV).obj E) := by
      rw [rightOrthogonal_shiftClosure_ofObj_iff]
      exact fun _ => h1
    have hE2 : ((ObjectProperty.singleton (koszulQC g)).shiftClosure ℤ).rightOrthogonal
        ((restrictedDerivedRestrict jV).obj ((Stacks.Duality.quasiCoherentDerivedPushforward jU
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).obj
            ((restrictedDerivedRestrict jU).obj E))) :=
      ObjectProperty.prop_of_iso _ (βVU _).symm
        (rightOrthogonal_shiftClosure_singleton_rightAdjoint_obj adjV' hKW _)
    have hC : ((ObjectProperty.singleton (koszulQC g)).shiftClosure ℤ).rightOrthogonal
        ((restrictedDerivedRestrict jV).obj C) :=
      ObjectProperty.ext_of_isTriangulatedClosed₃ _ _
        ((restrictedDerivedRestrict jV).map_distinguished _ hTr) hE1 hE2
    rw [rightOrthogonal_shiftClosure_ofObj_iff] at hC
    have hC' := (forall_hom_shift_eq_zero_iff _ _ _).1 (hC PUnit.unit)
    have hCT : derivedSupported Y.ringCatSheaf T C.obj :=
      derivedSupported_ext₃ _ (ιY.map_distinguished _ hTr) hET
        (derivedSupported_derivedPushforward jU hTcl _ (derivedSupported_derivedRestrict jU hET))
    have hCV : IsZero ((restrictedDerivedRestrict jV).obj C) := by
      refine isZero_fullSubcategory_of_isZero_obj
        (isZero_of_quasiCoherentSupported_of_forall_hom_koszulObject_eq_zero g _
          ⟨((restrictedDerivedRestrict jV).obj C).2, ?_⟩ fun n g' => ?_)
      · intro n x hx
        have hx' : x ∈ ((openComplement g : (Spec (CommRingCat.of A)).Opens) :
            Set (Spec (CommRingCat.of A))) := not_not.1 hx
        rw [hg] at hx'
        refine IsZero.of_iso ?_ (stalkHomologyDerivedRestrictIso jV C.obj n x)
        rcases hx' with hxW | hxT
        · rw [← show jU (iU ⟨x, hxW⟩) = jV x from hpt ⟨x, hxW⟩]
          exact isZero_stalk_of_isZero_derivedRestrict jU (isZero_obj_of_isZero hCU) n _
        · exact hCT n (jV x) hxT
      · have := hC' n ((shiftFunctor _ n).map (koszulQC_obj_iso g).hom ≫ g')
        rw [← cancel_epi ((shiftFunctor _ n).map (koszulQC_obj_iso g).hom), this, comp_zero]
    have hC0 : IsZero C := isZero_fullSubcategory_of_isZero_obj
      (isZero_of_isZero_derivedRestrict₂ jU jV (isZero_obj_of_isZero hCU)
        (isZero_obj_of_isZero hCV) hcov)
    exact (Triangle.isZero₃_iff_isIso₁ _ hTr).1 hC0
  -- Step 3: `E|_U = 0`
  have h3 : IsZero ((restrictedDerivedRestrict jU).obj E) := by
    refine hPgen _ (derivedSupported_derivedRestrict jU hET) fun n g' => ?_
    let k : (restrictedDerivedRestrict jU).obj (R⟦n⟧) ⟶ (restrictedDerivedRestrict jU).obj E :=
      ((restrictedDerivedRestrict jU).commShiftIso n).hom.app R ≫
        (shiftFunctor _ n).map (eRU.hom ≫ biprod.fst) ≫ g'
    have : g' = (shiftFunctor _ n).map (biprod.inl ≫ eRU.inv) ≫
        ((restrictedDerivedRestrict jU).commShiftIso n).inv.app R ≫ k := by
      simp only [k, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Category.assoc,
        Iso.inv_hom_id_assoc, biprod.inl_fst]
      simp
    rw [this, eq_zero_of_isIso_unit adjU h2 (hR0 n) k, comp_zero, comp_zero]
  exact ((Stacks.Duality.quasiCoherentDerivedPushforward jU
    (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs jU)).map_isZero h3).of_iso
      (asIso (adjU.unit.app E))

end Step

/-! ### The induction on the number of affine opens -/

section Induction

open Stacks.Koszul.Truncation

/-- The statement proved by induction: `D_{QCoh,T}(𝒪_Y)` is generated, in the sense of
[Stacks, Tag 09SJ], by a single object of `D_QCoh(𝒪_Y)` which is compact there and supported on
`T`, for every closed `T ⊆ Y` with quasi-compact complement. -/
def HasCompactSupportedGenerators (Y : Scheme.{u}) : Prop :=
  ∀ T : Set Y, IsClosed T → IsCompact Tᶜ →
    ∃ G : Stacks.Duality.quasiCoherentDerivedCategory Y, IsCompactObject.{u} G ∧
      derivedSupported Y.ringCatSheaf T G.obj ∧
      ∀ E : Stacks.Duality.quasiCoherentDerivedCategory Y, derivedSupported Y.ringCatSheaf T E.obj →
        (∀ (n : ℤ) (g : G⟦n⟧ ⟶ E), g = 0) → IsZero E

/-- `Stacks.Duality.SupportedGeneration.exists_supported_generator_of_step` with the overlap given
as an open of `Spec A` equal to `D(f₁) ∪ … ∪ D(f_r)`. -/
theorem exists_supported_generator_of_step' {Y : Scheme.{u}} [QuasiSeparatedSpace Y]
    [CompactSpace Y] {U : Scheme.{u}} [CompactSpace U] [QuasiSeparatedSpace U] (jU : U ⟶ Y)
    [IsOpenImmersion jU] {A : Type u} [CommRing A] (jV : Spec (CommRingCat.of A) ⟶ Y)
    [IsOpenImmersion jV] {r : ℕ} (f : Fin r → A) {W : (Spec (CommRingCat.of A)).Opens}
    (hW : W = openComplement f) (iU : W.toScheme ⟶ U) [IsOpenImmersion iU]
    (hsq : IsPullback iU W.ι jU jV) (hcov : ∀ y : Y, (∃ x, jU x = y) ∨ (∃ x, jV x = y))
    {T : Set Y} (hTcl : IsClosed T) {s : ℕ} (g : Fin s → A)
    (hg : ((openComplement g : (Spec (CommRingCat.of A)).Opens) : Set (Spec (CommRingCat.of A))) =
      (W : Set (Spec (CommRingCat.of A))) ∪ (jV ⁻¹' T)ᶜ)
    (hTV : IsCompact (jV ⁻¹' T)ᶜ)
    (P : Stacks.Duality.quasiCoherentDerivedCategory U) (hPc : IsCompactObject.{u} P)
    (hPT : derivedSupported U.ringCatSheaf (jU ⁻¹' T) P.obj)
    (hPgen : ∀ E : Stacks.Duality.quasiCoherentDerivedCategory U,
      derivedSupported U.ringCatSheaf (jU ⁻¹' T) E.obj →
        (∀ (n : ℤ) (g' : P⟦n⟧ ⟶ E), g' = 0) → IsZero E) :
    ∃ G : Stacks.Duality.quasiCoherentDerivedCategory Y, IsCompactObject.{u} G ∧
      derivedSupported Y.ringCatSheaf T G.obj ∧
      ∀ E : Stacks.Duality.quasiCoherentDerivedCategory Y, derivedSupported Y.ringCatSheaf T E.obj →
        (∀ (n : ℤ) (g' : G⟦n⟧ ⟶ E), g' = 0) → IsZero E := by
  subst hW
  exact exists_supported_generator_of_step jU jV f iU hsq hcov hTcl g hg hTV P hPc hPT hPgen

/-- **The inductive step, for a cover by a quasi-compact open and an affine open.** Let `Y` be a
quasi-compact quasi-separated scheme covered by a quasi-compact open `U` and the image of an open
immersion `Spec A ⟶ Y`. If `U` has compact supported generators, so does `Y`.

The preimage of `U` in `Spec A` is quasi-compact, `Y` being quasi-separated, hence a finite union
of basic opens `D(f₁) ∪ … ∪ D(f_r)`; and for `T ⊆ Y` closed with quasi-compact complement,
`D(f₁) ∪ … ∪ D(f_r) ∪ j_V⁻¹(Y ∖ T)` is quasi-compact, hence of the form `D(g₁) ∪ … ∪ D(g_s)`. -/
theorem hasCompactSupportedGenerators_of_cover {Y : Scheme.{u}} [QuasiSeparatedSpace Y]
    [CompactSpace Y] (U : Y.Opens) (hUc : IsCompact (U : Set Y)) {A : Type u} [CommRing A]
    (jV : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion jV]
    (hcov : ∀ y : Y, y ∈ U ∨ (∃ x, jV x = y))
    (hU : HasCompactSupportedGenerators U.toScheme) : HasCompactSupportedGenerators Y := by
  intro T hTcl hTc
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hUc
  have : QuasiSeparatedSpace U.toScheme := U.ι.isOpenEmbedding.quasiSeparatedSpace
  have hc := jV.isCompact_preimage hUc
  obtain ⟨s, hs⟩ := Stacks.AlgebraicGeometry.InductionPrinciple.exists_finset_basicOpen_of_isCompact
    (isAffineOpen_top (Spec (CommRingCat.of A))) hc le_top
  let e := s.equivFin
  let f : Fin s.card → A := fun i => (Scheme.ΓSpecIso (CommRingCat.of A)).hom (e.symm i)
  have hW : jV ⁻¹ᵁ U = openComplement f := by
    rw [hs]
    refine le_antisymm (iSup₂_le fun g hg => ?_) (iSup_le fun i => ?_)
    · refine le_trans (le_of_eq ?_) (le_iSup _ (e ⟨g, hg⟩))
      congr 1
      simp [f]
    · refine le_trans (le_of_eq ?_)
        (le_iSup₂ (f := fun g _ => (Spec (CommRingCat.of A)).basicOpen g) (e.symm i).1 (e.symm i).2)
      congr 1
      simp [f]
  let O : Y.Opens := ⟨Tᶜ, hTcl.isOpen_compl⟩
  have hTV : IsCompact (jV ⁻¹' T)ᶜ := jV.isCompact_preimage (U := O) hTc
  obtain ⟨t, g, hg⟩ := exists_coe_openComplement_eq_compl
    ((((jV ⁻¹ᵁ U : (Spec (CommRingCat.of A)).Opens) : Set (Spec (CommRingCat.of A))) ∪
      (jV ⁻¹' T)ᶜ)ᶜ)
    (isClosed_compl_iff.2 ((jV ⁻¹ᵁ U).isOpen.union (hTcl.preimage jV.continuous).isOpen_compl))
    (by rw [compl_compl]; exact hc.union hTV)
  rw [compl_compl] at hg
  obtain ⟨P, hPc, hPT, hPgen⟩ := hU (U.ι ⁻¹' T) (hTcl.preimage U.ι.continuous)
    (U.ι.isCompact_preimage (U := O) hTc)
  refine exists_supported_generator_of_step' U.ι jV f hW (jV ∣_ U)
    (isPullback_morphismRestrict jV U) (fun y => ?_) hTcl g hg hTV P hPc hPT hPgen
  rcases hcov y with hy | hy
  · exact Or.inl ⟨⟨y, hy⟩, rfl⟩
  · exact Or.inr hy

/-- **Compact supported generators for a scheme covered by `n` affine opens**, by induction on
`n`. -/
theorem hasCompactSupportedGenerators_of_affineCover : ∀ (n : ℕ) (Y : Scheme.{u})
    [QuasiSeparatedSpace Y] (V : Fin n → Y.Opens), (∀ i, IsAffineOpen (V i)) →
    (⨆ i, V i) = ⊤ → HasCompactSupportedGenerators Y
  | 0, Y, _, V, _, hcov => by
      have hY : IsEmpty Y := ⟨fun y => by
        have hy : y ∈ (⊤ : Y.Opens) := trivial
        rw [← hcov] at hy
        simp at hy⟩
      intro T _ _
      refine ⟨0, isCompactObject_zero' (T := Stacks.Duality.quasiCoherentDerivedCategory Y),
        derivedSupported_of_isZero T (isZero_obj_of_isZero (isZero_zero _)),
        fun E hE _ => isZero_fullSubcategory_of_isZero_obj
          (isZero_of_derivedSupported_of_forall_not_mem (fun z => hY.elim z) hE)⟩
  | n + 1, Y, _, V, hV, hcov => by
      have hcomp : ∀ (m : ℕ) (W : Fin m → Y.Opens), (∀ i, IsAffineOpen (W i)) →
          IsCompact (((⨆ i, W i : Y.Opens)) : Set Y) := fun m W hW => by
        rw [TopologicalSpace.Opens.coe_iSup]
        exact isCompact_iUnion fun i => (hW i).isCompact
      have : CompactSpace Y := ⟨by
        have := hcomp _ V hV
        rwa [hcov, TopologicalSpace.Opens.coe_top] at this⟩
      let U : Y.Opens := ⨆ i : Fin n, V i.castSucc
      have hUc : IsCompact (U : Set Y) := hcomp _ _ fun i => hV _
      have : QuasiSeparatedSpace U.toScheme := U.ι.isOpenEmbedding.quasiSeparatedSpace
      have hIH := hasCompactSupportedGenerators_of_affineCover n U.toScheme
        (fun i => U.ι ⁻¹ᵁ V i.castSucc)
        (fun i => (hV i.castSucc).preimage_of_isOpenImmersion U.ι (by
          rw [Scheme.Opens.opensRange_ι]
          exact le_iSup (fun i : Fin n => V i.castSucc) i))
        (by
          rw [← Scheme.Hom.preimage_iSup]
          exact Scheme.Opens.ι_preimage_self U)
      refine hasCompactSupportedGenerators_of_cover U hUc (A := Γ(Y, V (Fin.last n)))
        (hV (Fin.last n)).fromSpec (fun y => ?_) hIH
      have hy : y ∈ (⊤ : Y.Opens) := trivial
      rw [← hcov, TopologicalSpace.Opens.mem_iSup] at hy
      obtain ⟨i, hi⟩ := hy
      refine Fin.lastCases
        (motive := fun i => y ∈ V i → y ∈ U ∨ ∃ x, (hV (Fin.last n)).fromSpec x = y)
        (fun h => Or.inr ?_) (fun j h => Or.inl ?_) i hi
      · show y ∈ Set.range (hV (Fin.last n)).fromSpec
        rwa [(hV (Fin.last n)).range_fromSpec]
      · exact (TopologicalSpace.Opens.mem_iSup.mpr ⟨j, h⟩ : y ∈ U)

end Induction

/-- **`D_{QCoh,T}(𝒪_X)` is generated by a single compact object of `D_QCoh(𝒪_X)`.** Let `X` be a
quasi-compact and quasi-separated scheme and `T ⊆ X` a closed subset with quasi-compact
complement. There is an object `G` of `D_QCoh(𝒪_X)`, compact there and supported on `T`, such
that an object of `D_{QCoh,T}(𝒪_X)` receiving no nonzero morphism from any shift of `G` is zero.

This is the induction of [Stacks, Tag 0A9A] over a finite affine cover, the inductive step being
`exists_supported_generator_of_step`. That `G` is moreover perfect is
`exists_isPerfect_quasiCoherentSupported_isWeakGenerator_of_qcqs`.
-/
theorem hasCompactSupportedGenerators (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    HasCompactSupportedGenerators X := by
  obtain ⟨s, hs, hX⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (U := (⊤ : X.Opens))).mp (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)
  let t := hs.toFinset
  let e := t.equivFin
  refine hasCompactSupportedGenerators_of_affineCover t.card X (fun i => ((e.symm i).1 : X.Opens))
    (fun i => (e.symm i).1.2) ?_
  rw [hX]
  refine le_antisymm (iSup_le fun i => ?_) (iSup₂_le fun W hW => ?_)
  · exact le_iSup₂ (f := fun (W : X.affineOpens) (_ : W ∈ s) => (W : X.Opens)) (e.symm i).1
      (hs.mem_toFinset.mp (e.symm i).2)
  · exact le_trans (le_of_eq rfl) (le_iSup (fun i => ((e.symm i).1 : X.Opens))
      (e ⟨W, hs.mem_toFinset.mpr hW⟩) |>.trans' (by simp))

end Stacks.Duality.SupportedGeneration

end
