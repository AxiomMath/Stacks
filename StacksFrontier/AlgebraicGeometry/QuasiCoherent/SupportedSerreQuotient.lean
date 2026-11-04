module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Properties.GabberResult.Abelian
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.QcohPushforwardOpen.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.SupportedSerreSubcategory
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# The Serre quotient of quasi-coherent modules by those supported on a closed subset

Let `X` be a quasi-compact and quasi-separated scheme, let `Z ⊆ X` be closed and suppose the
open complement `U = X \ Z` is quasi-compact.  The quasi-coherent `𝒪_X`-modules supported on `Z`
form a Serre subcategory `𝒜 ⊆ QCoh(𝒪_X)`, and restriction along `U ↪ X` identifies the Serre
quotient `QCoh(𝒪_X)/𝒜` with `QCoh(𝒪_U)`.

## Main definitions

* `AlgebraicGeometry.IsSupportedOnSet` is support containment in a subset of the scheme,
  expressed by vanishing of stalks away from that subset.
* `AlgebraicGeometry.quasicoherentSupportedOn` is the full subcategory `𝒜 ⊆ QCoh(𝒪_X)` of
  quasi-coherent modules supported on a subset.
* `AlgebraicGeometry.quasicoherentRestriction` is restriction of quasi-coherent modules along
  an open immersion.
* `AlgebraicGeometry.quasicoherentSupportedQuotientEquivalence` is the equivalence
  `QCoh(𝒪_X)/𝒜 ≌ QCoh(𝒪_U)`.

## Main results

* `AlgebraicGeometry.quasicoherentSupportedOn_isSerreClass`: the quasi-coherent modules
  supported on a subset form a Serre subcategory.
* `AlgebraicGeometry.quasicoherentRestriction_isLocalization`: restriction to the open
  complement of a closed subset is the localization of `QCoh(𝒪_X)` at the morphisms that are
  isomorphisms modulo that Serre subcategory.
* `AlgebraicGeometry.quasicoherentSupportedQuotientEquivalenceFunctorIso`: the equivalence is
  induced by the restriction functor.

## Implementation notes

Support containment in a subset is expressed by nonvanishing of stalks of the underlying sheaf
of abelian groups, the same encoding as `AlgebraicGeometry.IsSupportedOn`, which compares the
support of one module with that of another.

The quotient `QCoh(𝒪_X)/𝒜` is the localization of `QCoh(𝒪_X)` at the class
`𝒜.isoModSerre` of morphisms whose kernel and cokernel lie in `𝒜`; this is the Serre quotient.
Restriction is shown to be such a localization by exhibiting its right adjoint, pushforward
along the open immersion, as fully faithful, so that the kernel of restriction is exactly `𝒜`.

## References

* [Stacks Project, Lemma 56.6.4 (Tag 0GPH)](https://stacks.math.columbia.edu/tag/0GPH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Modules supported on a subset -/

/-- A module sheaf `E` on `X` is set-theoretically supported on `Z ⊆ X` when its stalk vanishes
at every point outside `Z`.  This is the support containment of [Stacks, Tag 0GPH]. -/
public def IsSupportedOnSet {X : Scheme.{u}} (E : X.Modules) (Z : Set X) : Prop :=
  ∀ x : X, (∃ a : ((Scheme.Modules.toPresheaf X).obj E).stalk x, a ≠ 0) → x ∈ Z

/-- Support containment between two modules is support containment in the support of the
second one. -/
public theorem isSupportedOn_iff_isSupportedOnSet {X : Scheme.{u}} (E F : X.Modules) :
    IsSupportedOn E F ↔
      IsSupportedOnSet E {x : X | ∃ a : ((Scheme.Modules.toPresheaf X).obj F).stalk x, a ≠ 0} :=
  Iff.rfl

/-- The full subcategory `𝒜 ⊆ QCoh(𝒪_X)` of quasi-coherent modules supported on `Z ⊆ X`. -/
public def quasicoherentSupportedOn (X : Scheme.{u}) (Z : Set X) :
    ObjectProperty (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  fun F ↦ IsSupportedOnSet F.obj Z

/-- Restriction of quasi-coherent modules along an open immersion, as a functor between the
categories of quasi-coherent modules. -/
public noncomputable def quasicoherentRestriction {V Y : Scheme.{u}} (j : V ⟶ Y)
    [IsOpenImmersion j] :
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent V.ringCatSheaf).FullSubcategory :=
  ObjectProperty.lift (SheafOfModules.isQuasicoherent V.ringCatSheaf)
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent Y.ringCatSheaf) ⋙
      Scheme.Modules.restrictFunctor j)
    (fun M ↦ Scheme.Modules.isQuasicoherent_restrictFunctor j M.obj)

section

private lemma preservesFiniteLimits_quasicoherentRestriction {V Y : Scheme.{u}} (j : V ⟶ Y)
    [IsOpenImmersion j] : PreservesFiniteLimits (quasicoherentRestriction j) := by
  have h2 : PreservesFiniteLimits
      (quasicoherentRestriction j ⋙ (SheafOfModules.isQuasicoherent V.ringCatSheaf).ι) := by
    show PreservesFiniteLimits ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι ⋙
      Scheme.Modules.restrictFunctor j)
    exact @comp_preservesFiniteLimits _ _ _ _ _ _
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι (Scheme.Modules.restrictFunctor j)
      (ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _)
      (Scheme.Modules.restrictFunctor_preservesFiniteLimits j)
  exact preservesFiniteLimits_of_reflects_of_preserves (quasicoherentRestriction j)
    (SheafOfModules.isQuasicoherent V.ringCatSheaf).ι

private lemma preservesFiniteColimits_quasicoherentRestriction {V Y : Scheme.{u}} (j : V ⟶ Y)
    [IsOpenImmersion j] : PreservesFiniteColimits (quasicoherentRestriction j) := by
  have h2 : PreservesFiniteColimits
      (quasicoherentRestriction j ⋙ (SheafOfModules.isQuasicoherent V.ringCatSheaf).ι) := by
    show PreservesFiniteColimits ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι ⋙
      Scheme.Modules.restrictFunctor j)
    exact @comp_preservesFiniteColimits _ _ _ _ _ _
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι (Scheme.Modules.restrictFunctor j)
      (ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _)
      (inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.restrictFunctor j)))
  exact preservesFiniteColimits_of_reflects_of_preserves (quasicoherentRestriction j)
    (SheafOfModules.isQuasicoherent V.ringCatSheaf).ι

private lemma module_isZero_iff_stalk_isZero (X : Scheme.{u}) (M : X.Modules) :
    IsZero M ↔ ∀ x : X, IsZero (((Scheme.Modules.toPresheaf X).obj M).stalk x) := by
  let P := (Scheme.Modules.toPresheaf X).obj M
  let H : TopCat.Sheaf AddCommGrpCat (↑X.toPresheafedSpace) := ⟨P, M.isSheaf⟩
  refine ⟨fun h x ↦ Functor.map_isZero (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
    (Functor.map_isZero (Scheme.Modules.toPresheaf X) h), fun h ↦ ?_⟩
  have hP : IsZero P := Functor.map_isZero (TopCat.Sheaf.forget AddCommGrpCat.{u} _)
    ((TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero H).mpr h)
  refine (IsZero.iff_id_eq_zero M).2 (Functor.map_injective (Scheme.Modules.toPresheaf X) ?_)
  have hmap0 : (Scheme.Modules.toPresheaf X).map (0 : M ⟶ M) = 0 := by
    ext U s
    rfl
  have hmapid : (Scheme.Modules.toPresheaf X).map (𝟙 M) = 𝟙 P := by
    ext U s
    rfl
  rw [hmapid, hmap0]
  exact (IsZero.iff_id_eq_zero P).mp hP

private lemma quasicoherentSupportedOn_iff_stalk_isZero (X : Scheme.{u}) (Z : Set X)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    quasicoherentSupportedOn X Z F ↔
      ∀ x : X, x ∉ Z → IsZero (((Scheme.Modules.toPresheaf X).obj F.obj).stalk x) := by
  refine ⟨fun h x hx ↦ ?_, fun h x ⟨a, ha⟩ ↦ ?_⟩
  · refine (IsZero.iff_id_eq_zero _).2 ?_
    ext a
    by_contra ha
    exact hx (h x ⟨a, ha⟩)
  · by_contra hx
    exact ha (by simpa using congrArg (fun f => f a) ((IsZero.iff_id_eq_zero _).mp (h x hx)))

/-- The stalk at `x` of the underlying sheaf of abelian groups, as a functor on quasi-coherent
modules. -/
private noncomputable def quasicoherentStalkFunctor (X : Scheme.{u}) (x : X) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤ AddCommGrpCat.{u} :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
    SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x

private instance quasicoherentStalkFunctor_preservesZeroMorphisms (X : Scheme.{u}) (x : X) :
    (quasicoherentStalkFunctor X x).PreservesZeroMorphisms := by
  let P := SheafOfModules.isQuasicoherent X.ringCatSheaf
  constructor
  intro A B
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      ((SheafOfModules.forget X.ringCatSheaf).map (P.ι.map (0 : A ⟶ B)))) = 0
  simp only [Functor.map_zero]

private lemma quasicoherentStalkFunctor_preservesZeroMorphisms_of (X : Scheme.{u}) (x : X)
    (z : HasZeroMorphisms
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    @Functor.PreservesZeroMorphisms _ _ _ _ z _ (quasicoherentStalkFunctor X x) := by
  have hz : z =
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).instHasZeroMorphismsFullSubcategory :=
    Subsingleton.elim _ _
  cases hz
  exact quasicoherentStalkFunctor_preservesZeroMorphisms X x

private lemma quasicoherentStalkFunctor_preservesExact (X : Scheme.{u}) (x : X)
    {z : HasZeroMorphisms (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory}
    [hF : @Functor.PreservesZeroMorphisms _ _ _ _ z _ (quasicoherentStalkFunctor X x)]
    (S : @ShortComplex _ _ z) (hS : S.Exact) :
    (S.map (quasicoherentStalkFunctor X x)).Exact := by
  let P := SheafOfModules.isQuasicoherent X.ringCatSheaf
  let _hz : HasZeroMorphisms P.FullSubcategory := z
  let _hl : PreservesFiniteLimits P.ι := P.preservesFiniteLimits_ι_of_isWeakSerreClass
  let _hc : PreservesFiniteColimits P.ι := P.preservesFiniteColimits_ι_of_isWeakSerreClass
  have hStalk := (SheafOfModules.exact_iff_stalkShortComplex_exact X.ringCatSheaf
    (S.map P.ι)).1 (hS.map P.ι) x
  change ((S.map P.ι).map
    (SheafOfModules.stalkAddCommGroupFunctor X.ringCatSheaf x)).Exact at hStalk
  simpa [quasicoherentStalkFunctor, Functor.comp_map] using hStalk

/-- The stalk functor on quasi-coherent modules preserves monomorphisms and epimorphisms. -/
private lemma quasicoherentStalkFunctor_preserves_mono_and_epi (X : Scheme.{u}) (x : X) :
    Functor.PreservesMonomorphisms (quasicoherentStalkFunctor X x) ∧
      Functor.PreservesEpimorphisms (quasicoherentStalkFunctor X x) := by
  let P := SheafOfModules.isQuasicoherent X.ringCatSheaf
  let z : HasZeroMorphisms P.FullSubcategory :=
    @Preadditive.preadditiveHasZeroMorphisms P.FullSubcategory _
      (AlgebraicGeometry.quasicoherentModules_abelian X).toPreadditive
  let hF : @Functor.PreservesZeroMorphisms _ _ _ _ z _ (quasicoherentStalkFunctor X x) :=
    quasicoherentStalkFunctor_preservesZeroMorphisms_of X x z
  have h := fun S hS ↦ @quasicoherentStalkFunctor_preservesExact X x z hF S hS
  exact ⟨@Functor.preservesMonomorphisms_of_map_exact _ _ _ _ _ _ _ hF h,
    @Functor.preservesEpimorphisms_of_map_exact _ _ _ _ _ _ _ hF h⟩

private lemma quasicoherentStalkFunctor_preservesMonomorphisms (X : Scheme.{u}) (x : X) :
    Functor.PreservesMonomorphisms (quasicoherentStalkFunctor X x) :=
  (quasicoherentStalkFunctor_preserves_mono_and_epi X x).1

private lemma quasicoherentStalkFunctor_preservesEpimorphisms (X : Scheme.{u}) (x : X) :
    Functor.PreservesEpimorphisms (quasicoherentStalkFunctor X x) :=
  (quasicoherentStalkFunctor_preserves_mono_and_epi X x).2

end

/-! ### The supported modules form a Serre subcategory -/

/-- Quasi-coherent modules supported on a fixed subset of a scheme form a Serre subcategory of
the category of all quasi-coherent modules. -/
@[stacks 0GPH "the full subcategory of modules supported on `Z` is a Serre subcategory"]
public instance quasicoherentSupportedOn_isSerreClass (X : Scheme.{u}) (Z : Set X) :
    (quasicoherentSupportedOn X Z).IsSerreClass where
  exists_zero := by
    refine ⟨HasZeroObject.zero.choose, HasZeroObject.zero.choose_spec, ?_⟩
    refine (quasicoherentSupportedOn_iff_stalk_isZero X Z _).2 fun x _ ↦ ?_
    exact Functor.map_isZero (quasicoherentStalkFunctor X x) (isZero_zero _)
  prop_of_mono := by
    intro E G f hf hG
    refine (quasicoherentSupportedOn_iff_stalk_isZero X Z E).2 fun x hx ↦ ?_
    exact @IsZero.of_mono _ _ _ _ _ ((quasicoherentStalkFunctor X x).map f)
      ((quasicoherentStalkFunctor_preservesMonomorphisms X x).preserves f)
      ((quasicoherentSupportedOn_iff_stalk_isZero X Z G).1 hG x hx)
  prop_of_epi := by
    intro E G f hf hE
    refine (quasicoherentSupportedOn_iff_stalk_isZero X Z G).2 fun x hx ↦ ?_
    exact @IsZero.of_epi _ _ _ _ _ ((quasicoherentStalkFunctor X x).map f)
      ((quasicoherentStalkFunctor_preservesEpimorphisms X x).preserves f)
      ((quasicoherentSupportedOn_iff_stalk_isZero X Z E).1 hE x hx)
  prop_X₂_of_shortExact := by
    intro S hS h₁ h₃
    refine (quasicoherentSupportedOn_iff_stalk_isZero X Z S.X₂).2 fun x hx ↦ ?_
    exact (@quasicoherentStalkFunctor_preservesExact X x _
      (quasicoherentStalkFunctor_preservesZeroMorphisms_of X x _) S hS.exact).isZero_of_both_isZero
      ((quasicoherentSupportedOn_iff_stalk_isZero X Z S.X₁).1 h₁ x hx)
      ((quasicoherentSupportedOn_iff_stalk_isZero X Z S.X₃).1 h₃ x hx)

section

private lemma restriction_isZero_iff_supportedOn (X : Scheme.{u}) (Z : Set X) (U : X.Opens)
    (hUZ : (U : Set X) = Zᶜ)
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    IsZero ((quasicoherentRestriction U.ι).obj F) ↔ quasicoherentSupportedOn X Z F := by
  let j := U.ι
  let P_U := SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf
  let R := Scheme.Modules.restrictFunctor j
  have hCategory : IsZero ((quasicoherentRestriction j).obj F) ↔ IsZero (R.obj F.obj) :=
    ⟨fun h ↦ Functor.map_isZero P_U.ι h, fun h ↦ (IsZero.iff_id_eq_zero _).2
      (P_U.ι.map_injective ((IsZero.iff_id_eq_zero (R.obj F.obj)).mp h))⟩
  have hStalk (y : U.toScheme) :
      IsZero (((Scheme.Modules.toPresheaf U.toScheme).obj (R.obj F.obj)).stalk y) ↔
        IsZero (((Scheme.Modules.toPresheaf X).obj F.obj).stalk (j.base y)) :=
    ⟨fun h ↦ h.of_iso ((Scheme.Modules.restrictStalkNatIso j y).app F.obj).symm,
      fun h ↦ h.of_iso ((Scheme.Modules.restrictStalkNatIso j y).app F.obj)⟩
  have hPoints :
      (∀ y : U.toScheme,
        IsZero (((Scheme.Modules.toPresheaf X).obj F.obj).stalk (j.base y))) ↔
      (∀ x : X, x ∉ Z → IsZero (((Scheme.Modules.toPresheaf X).obj F.obj).stalk x)) := by
    constructor
    · intro h x hx
      have hxU : x ∈ (U : Set X) := by rwa [hUZ]
      have hy : j.base (⟨x, hxU⟩ : U.toScheme) = x := Scheme.Opens.ι_apply U _
      simpa [hy] using h ⟨x, hxU⟩
    · intro h y
      refine h (j.base y) ?_
      show y.val ∉ Z
      have hy : y.val ∈ (U : Set X) := y.property
      rwa [hUZ] at hy
  calc
    IsZero ((quasicoherentRestriction j).obj F) ↔ IsZero (R.obj F.obj) := hCategory
    _ ↔ ∀ y : U.toScheme,
        IsZero (((Scheme.Modules.toPresheaf U.toScheme).obj (R.obj F.obj)).stalk y) :=
      module_isZero_iff_stalk_isZero U.toScheme (R.obj F.obj)
    _ ↔ ∀ y : U.toScheme,
        IsZero (((Scheme.Modules.toPresheaf X).obj F.obj).stalk (j.base y)) :=
      forall_congr' hStalk
    _ ↔ quasicoherentSupportedOn X Z F :=
      hPoints.trans (quasicoherentSupportedOn_iff_stalk_isZero X Z F).symm

end

/-! ### Restriction is the Serre quotient -/

/-- **[Stacks, Tag 0GPH].** Let `X` be a quasi-compact and quasi-separated scheme and let `U` be
a quasi-compact open whose complement is the closed subset `Z`.  Restriction along `U ↪ X`
exhibits `QCoh(𝒪_U)` as the localization of `QCoh(𝒪_X)` at the morphisms whose kernel and
cokernel are supported on `Z`, that is, as the Serre quotient of `QCoh(𝒪_X)` by the full
subcategory of quasi-coherent modules supported on `Z`. -/
@[stacks 0GPH "restriction is the localization at the supported Serre subcategory"]
public theorem quasicoherentRestriction_isLocalization (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (Z : Set X) (U : X.Opens) (hUZ : (U : Set X) = Zᶜ)
    (hU : IsCompact (U : Set X)) :
    (quasicoherentRestriction U.ι).IsLocalization
      (quasicoherentSupportedOn X Z).isoModSerre := by
  have hcs : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have hqc : QuasiCompact U.ι := inferInstance
  have hqs : QuasiSeparated U.ι := inferInstance
  have hpush (M : (SheafOfModules.isQuasicoherent
      U.toScheme.ringCatSheaf).FullSubcategory) :
      SheafOfModules.isQuasicoherent X.ringCatSheaf
        (((SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι ⋙
          Scheme.Modules.pushforward U.ι).obj M) := by
    have hM : M.obj.IsQuasicoherent := M.property
    show ((Scheme.Modules.pushforward U.ι).obj M.obj).IsQuasicoherent
    exact AlgebraicGeometry.pushforward_isQuasicoherent U.ι M.obj
  set F : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).lift
      ((SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι ⋙
        Scheme.Modules.pushforward U.ι) hpush with hFdef
  have hlim : PreservesFiniteLimits (quasicoherentRestriction U.ι) :=
    preservesFiniteLimits_quasicoherentRestriction U.ι
  have hcolim : PreservesFiniteColimits (quasicoherentRestriction U.ι) :=
    preservesFiniteColimits_quasicoherentRestriction U.ι
  have comm1 : (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙
      Scheme.Modules.restrictFunctor U.ι ≅ quasicoherentRestriction U.ι ⋙
        (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι :=
    ((SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).liftCompιIso _ _).symm
  have comm2 : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι ⋙
      Scheme.Modules.pushforward U.ι ≅
        F ⋙ (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι :=
    hFdef ▸ ((SheafOfModules.isQuasicoherent X.ringCatSheaf).liftCompιIso _ _).symm
  have hcfull : ((SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι ⋙
      Scheme.Modules.pushforward U.ι).Full :=
    @Functor.Full.comp _ _ _ _ _ _
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι
      (Scheme.Modules.pushforward U.ι)
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).full_ι
      (inferInstanceAs ((Scheme.Modules.pushforward U.ι).Full))
  have hcfaith : ((SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι ⋙
      Scheme.Modules.pushforward U.ι).Faithful :=
    @Functor.Faithful.comp _ _ _ _ _ _
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).ι
      (Scheme.Modules.pushforward U.ι)
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).faithful_ι
      (inferInstanceAs ((Scheme.Modules.pushforward U.ι).Faithful))
  have hFfaith : F.Faithful :=
    @Functor.Faithful.of_comp_iso _ _ _ _ _ _ F
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι _ hcfaith comm2.symm
  have hFfull : F.Full :=
    @Functor.Full.of_comp_faithful_iso _ _ _ _ _ _ F
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι _ hcfull
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).faithful_ι) comm2.symm
  have adj := (Scheme.Modules.restrictAdjunction U.ι).restrictFullyFaithful
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).fullyFaithfulι
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).fullyFaithfulι comm1 comm2
  have hKernel : (quasicoherentRestriction U.ι).kernel = quasicoherentSupportedOn X Z := by
    ext M
    exact restriction_isZero_iff_supportedOn X Z U hUZ M
  have hW : (quasicoherentRestriction U.ι).kernel.isoModSerre =
      (quasicoherentSupportedOn X Z).isoModSerre := by
    ext A B f
    simp [ObjectProperty.isoModSerre, hKernel]
  exact hW ▸ Abelian.isLocalization_isoModSerre_kernel_of_leftAdjoint adj

/-- **[Stacks, Tag 0GPH].** The equivalence `QCoh(𝒪_X)/𝒜 ≌ QCoh(𝒪_U)` induced by restriction,
where `𝒜` is the Serre subcategory of quasi-coherent modules supported on the closed complement
`Z` of the quasi-compact open `U`, and `QCoh(𝒪_X)/𝒜` is the Serre quotient, that is the
localization of `QCoh(𝒪_X)` at the morphisms that are isomorphisms modulo `𝒜`. -/
@[stacks 0GPH "the induced equivalence from the quotient category"]
public noncomputable def quasicoherentSupportedQuotientEquivalence (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (Z : Set X) (U : X.Opens)
    (hUZ : (U : Set X) = Zᶜ) (hU : IsCompact (U : Set X)) :
    (quasicoherentSupportedOn X Z).isoModSerre.Localization ≌
      (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory :=
  have := quasicoherentRestriction_isLocalization X Z U hUZ hU
  Localization.equivalenceFromModel (quasicoherentRestriction U.ι)
    (quasicoherentSupportedOn X Z).isoModSerre

/-- The equivalence `QCoh(𝒪_X)/𝒜 ≌ QCoh(𝒪_U)` of [Stacks, Tag 0GPH] is the one induced by the
restriction functor: composing it with the quotient functor gives back restriction. -/
@[stacks 0GPH "the equivalence is induced by the restriction functor"]
public noncomputable def quasicoherentSupportedQuotientEquivalenceFunctorIso (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (Z : Set X) (U : X.Opens)
    (hUZ : (U : Set X) = Zᶜ) (hU : IsCompact (U : Set X)) :
    (quasicoherentSupportedOn X Z).isoModSerre.Q ⋙
        (quasicoherentSupportedQuotientEquivalence X Z U hUZ hU).functor ≅
      quasicoherentRestriction U.ι :=
  have := quasicoherentRestriction_isLocalization X Z U hUZ hU
  Localization.qCompEquivalenceFromModelFunctorIso (quasicoherentRestriction U.ι)
    (quasicoherentSupportedOn X Z).isoModSerre

end AlgebraicGeometry

end
