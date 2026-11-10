module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.CohomologyAffineReduction.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.BoundedBelowComparison
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.Coherence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.BoundedCohomologicalDimension
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.KInjectiveRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived direct image of a complex with right-acyclic terms

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes and let `K` be a
cochain complex of quasi-coherent `𝒪_X`-modules each of whose terms is right acyclic for `f_*`.
Then the termwise direct image `f_* K` computes the derived direct image: the canonical
comparison `f_* K ⟶ Rf_* K` is an isomorphism in `D(𝒪_S)`.

The proof is the one in the source. Invertibility of the comparison is tested on cohomology
sheaves and is local on `S`, so one may restrict to an affine open `V ⊆ S`; after that
restriction the target is quasi-compact, so [Stacks, Tag 08D5] bounds the cohomological
dimension of the restricted direct image by some `N`, and derived direct image commutes with
restriction to an open ([Stacks, Tag 08FE]). Fix a cohomological degree `q` and replace `K` by
its stupid truncation `σ^{≥a}K` with `a < q` and `a + N ≤ q`. The truncation is bounded below
with right-acyclic terms, so the comparison is invertible there by Leray's acyclicity criterion;
and both `f_*` and `Rf_*` see `σ^{≥a}K → K` as an isomorphism on `H^q`, the first because the
map is already a degreewise isomorphism above `a` and the second because the third term of the
stupid truncation triangle lies in `D^{≤a-1}`, which `Rf_*` carries into `D^{≤a+N-2}`.

## Main results

* `AlgebraicGeometry.isIso_to_rightDerived_of_termwise_acyclic`: the canonical comparison from
  the termwise direct image to any right derived direct image is invertible at a complex of
  quasi-coherent modules with right-acyclic terms.

## Implementation notes

The derived direct image is not fixed: the statement quantifies over a functor with the
`CategoryTheory.Functor.IsRightDerivedFunctor` universal property and uses the natural
transformation belonging to that structure, so what is proved is that the *canonical* map is
invertible, rather than the existence of some isomorphism.

The category of `𝒪_X`-modules on a scheme has two definitionally equal but syntactically
distinct spellings, `AlgebraicGeometry.Scheme.Modules X` and
`SheafOfModules (structureSheafRing X.toRingedSpace)`; the derived direct
image of [Stacks, Tag 079W] is stated in the second and quasi-coherence in the first. Instance
search does not cross the two, so the bridge is made explicit once — in
`AlgebraicGeometry.pushforwardToDerivedCategory_scheme_eq` and the instances beside it, each of
them `rfl` — and nothing downstream relies on definitional unfolding at reduced transparency.

`HasDerivedCategory.standard` is installed with a raised priority for the reason recorded in
`StacksFrontier/AlgebraicGeometry/TotalDirectImage/QuasiCoherentDirectImage.lean`: the import
closure of the quasi-coherent weak Serre class carries the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` as a global instance, and with the two in
play at equal priority instance search no longer resolves `HasDerivedCategory.{u + 1} X.Modules`.
[Stacks, Tag 08D5] is stated in the standard model, so that is the model here.

## References

* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.SchemeCohomology (ringedSpace hom)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (pushforwardToDerivedCategory
  derivedPushforward derivedPushforwardUnit)
open StacksDraft.PseudoCoherence (mapDerivedCategoryCompHomologyFunctorIso)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-! ### The two spellings of the module category

The scheme-level and ringed-space-level descriptions of `𝒪_X`-modules and of direct image agree
on the nose. The equations below are what lets the derived-direct-image API, which is stated at
the ringed-space level, be used on goals phrased at the scheme level without any appeal to
definitional unfolding during instance search.
-/

/-- Termwise direct image along a morphism of schemes, followed by localization to the derived
category of the target, is the functor of [Stacks, Tag 079W] for the underlying morphism of
ringed spaces. -/
theorem pushforwardToDerivedCategory_scheme_eq {X S : Scheme.{u}} (f : X ⟶ S) :
    (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh (C := S.Modules) =
      pushforwardToDerivedCategory (hom f) :=
  rfl

/-- Pullback of module sheaves along a morphism of schemes is the pullback of the underlying
morphism of ringed spaces. -/
theorem pullback_scheme_eq {X S : Scheme.{u}} (f : X ⟶ S) :
    Scheme.Modules.pullback f = modulePullback (hom f) :=
  rfl

/-- Termwise direct image along a morphism of schemes, followed by localization, has a right
derived functor: K-injective resolutions compute it. -/
instance pushforwardToDerivedCategory_scheme_hasRightDerivedFunctor
    {X S : Scheme.{u}} (f : X ⟶ S) :
    ((Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh (C := S.Modules)).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pushforward_hasRightDerivedFunctor (hom f)

/-- The derived direct image of [Stacks, Tag 079W], read as a functor `D(𝒪_X) ⥤ D(𝒪_S)` for a
morphism of schemes. -/
abbrev schemeDerivedPushforward {X S : Scheme.{u}} (f : X ⟶ S) :
    DerivedCategory X.Modules ⥤ DerivedCategory S.Modules :=
  derivedPushforward (hom f)

/-- The canonical comparison exhibiting `AlgebraicGeometry.schemeDerivedPushforward` as a right
derived functor of termwise direct image. -/
abbrev schemeDerivedPushforwardUnit {X S : Scheme.{u}} (f : X ⟶ S) :
    (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ schemeDerivedPushforward f :=
  derivedPushforwardUnit (hom f)

/-- `AlgebraicGeometry.schemeDerivedPushforward f`, with the comparison
`AlgebraicGeometry.schemeDerivedPushforwardUnit f`, is a right derived functor of termwise direct
image with respect to quasi-isomorphisms. -/
instance schemeDerivedPushforward_isRightDerivedFunctor {X S : Scheme.{u}} (f : X ⟶ S) :
    (schemeDerivedPushforward f).IsRightDerivedFunctor (schemeDerivedPushforwardUnit f)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  inferInstanceAs ((derivedPushforward (hom f)).IsRightDerivedFunctor
    (derivedPushforwardUnit (hom f))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing (ringedSpace X)))
      (ComplexShape.up ℤ)))

/-! ### Quasi-coherence of cohomology -/

/-- The cohomology sheaves in the derived category of a complex of quasi-coherent
`𝒪_X`-modules are quasi-coherent: quasi-coherent modules are a weak Serre subcategory, hence
closed under the homology of a complex of its members. -/
theorem isQuasicoherent_derived_homology {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
    (hqc : ∀ n, (K.X n).IsQuasicoherent) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      (DerivedCategory.Q.obj K)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctorFactors X.Modules i).app K).symm
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_homology K i hqc)

/-- The terms of a stupid truncation in degrees `≤ a` of a complex of quasi-coherent modules are
quasi-coherent: each is either a term of the complex or zero. -/
theorem isQuasicoherent_stupidTruncLE {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
    (hqc : ∀ n, (K.X n).IsQuasicoherent) (a i : ℤ) :
    ((K.stupidTrunc (ComplexShape.embeddingUpIntLE a)).X i).IsQuasicoherent := by
  by_cases hi : i ≤ a
  · have heq : (ComplexShape.embeddingUpIntLE a).f (a - i).toNat = i := by
      change a - ((a - i).toNat : ℤ) = i
      omega
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (K.stupidTruncXIso (ComplexShape.embeddingUpIntLE a) heq).symm (hqc i)
  · exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isZero
      (K.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntLE a) i
        (by rw [ComplexShape.notMem_range_embeddingUpIntLE_iff]; omega))

/-! ### Exactness of pullback along an open immersion -/

/-- Pullback of module sheaves along an open immersion of schemes is left exact: it is
isomorphic to restriction to the open subscheme, which is computed on underlying presheaves of
abelian groups. -/
theorem pullback_preservesFiniteLimits_of_isOpenImmersion {V S : Scheme.{u}}
    (j : V ⟶ S) [IsOpenImmersion j] :
    PreservesFiniteLimits (Scheme.Modules.pullback j) :=
  preservesFiniteLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback j)

/-- A pullback square of schemes along an open immersion remains a pullback square of the
underlying sheafed spaces: both forgetful functors preserve such a pullback. -/
theorem isPullback_toShHom
    {X Y X' Y' : Scheme.{u}} (i : X' ⟶ X) (g : X' ⟶ Y')
    (f : X ⟶ Y) (j : Y' ⟶ Y) [IsOpenImmersion j]
    (h : IsPullback i g f j) :
    IsPullback i.toLRSHom.toShHom g.toLRSHom.toShHom
      f.toLRSHom.toShHom j.toLRSHom.toShHom :=
  have hL : IsPullback i.toLRSHom g.toLRSHom f.toLRSHom j.toLRSHom :=
    have : PreservesLimit (cospan f j) Scheme.forgetToLocallyRingedSpace := inferInstance
    h.map Scheme.forgetToLocallyRingedSpace
  have : PreservesLimit (cospan f.toLRSHom j.toLRSHom)
      LocallyRingedSpace.forgetToSheafedSpace :=
    LocallyRingedSpace.IsOpenImmersion.forget_preservesPullback_of_right
      j.toLRSHom f.toLRSHom
  hL.map LocallyRingedSpace.forgetToSheafedSpace

/-! ### A bound on the cohomological dimension of a derived direct image -/

/-- **An upper bound on the derived direct image, over a quasi-compact target.** For `f`
quasi-compact and quasi-separated with `S` quasi-compact there is an `N`, depending only on `f`,
such that `Rf_*` carries an object of `D(𝒪_X)` with quasi-coherent cohomology lying in `D^{≤d}`
into `D^{≤d+N-1}`.

This is [Stacks, Tag 08D5] for the chosen derived direct image, transported to an arbitrary one
through the uniqueness of right derived functors, and shifted so that the bound of the source is
not assumed to be zero. -/
theorem isLE_rightDerived_obj_of_isQuasicoherent
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace S]
    (Rf : DerivedCategory X.Modules ⥤ DerivedCategory S.Modules)
    (α : (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))] :
    ∃ N : ℤ, ∀ (E : DerivedCategory X.Modules) (d : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) →
      E.IsLE d → (Rf.obj E).IsLE (d + N - 1) := by
  let W := HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)
  let eRF : Rf ≅ schemeDerivedPushforward f :=
    Functor.rightDerivedUnique Rf (schemeDerivedPushforward f) α
      (schemeDerivedPushforwardUnit f) W
  let : Rf.CommShift ℤ := Functor.IsRightDerivedFunctor.commShift Rf α W ℤ
  obtain ⟨N, hN⟩ := exists_isZero_homology_derivedPushforward_of_isLE_zero f
  refine ⟨N, fun E d hqc hE => ?_⟩
  rw [DerivedCategory.isLE_iff]
  intro j hj
  let E' := (shiftFunctor (DerivedCategory X.Modules) d).obj E
  have hE' : E'.IsLE 0 := by
    have : E.IsLE d := hE
    exact DerivedCategory.TStructure.t.isLE_shift E d d 0 (by omega)
  have hqc' : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor X.Modules i).obj E').IsQuasicoherent :=
    DerivedCategoryB.derivedCategoryB_shift_mem
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X) d hqc
  have hz₂ : IsZero ((DerivedCategory.homologyFunctor S.Modules (j - d)).obj
      ((Rf.obj E)⟦d⟧)) :=
    ((hN E' hqc' hE' (j - d) (by omega)).of_iso
      ((DerivedCategory.homologyFunctor S.Modules (j - d)).mapIso (eRF.app E'))).of_iso
      ((DerivedCategory.homologyFunctor S.Modules (j - d)).mapIso
        ((Rf.commShiftIso d).app E).symm)
  simpa only [show d + (j - d) = j by omega] using
    Stacks.DerivedAcyclic.isZero_homology_shift_of_isZero (Rf.obj E) d (j - d) hz₂

/-- Above the bound of `AlgebraicGeometry.isLE_rightDerived_obj_of_isQuasicoherent` the derived
direct image sees `σ^{≥a}K → K` as an isomorphism on `H^q`: the third term of the stupid
truncation triangle lies in `D^{≤a-1}`, so its image lies in `D^{≤a+N-2}`, which `q` exceeds. -/
theorem isIso_homologyFunctor_map_rightDerived_stupidTrunc
    {X : Scheme.{u}} {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (Rf : DerivedCategory X.Modules ⥤ DerivedCategory B)
    [Rf.CommShift ℤ] [Rf.IsTriangulated]
    (N : ℤ)
    (hUpper : ∀ (E : DerivedCategory X.Modules) (d : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) →
      E.IsLE d → (Rf.obj E).IsLE (d + N - 1))
    (K : CochainComplex X.Modules ℤ)
    (hqc : ∀ n, (K.X n).IsQuasicoherent)
    (a q : ℤ) (ha : a + N ≤ q) :
    IsIso ((DerivedCategory.homologyFunctor B q).map
      (Rf.map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).map
          (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a)))))) := by
  let tail := K.stupidTrunc (ComplexShape.embeddingUpIntLE (a - 1))
  let T := (DerivedCategory.Qh ⋙ Rf).mapTriangle.obj
    (Stacks.DerivedAcyclic.stupidTruncTriangleh K (a - 1))
  have hT : T ∈ distTriang (DerivedCategory B) :=
    (DerivedCategory.Qh ⋙ Rf).map_distinguished _
      (Stacks.DerivedAcyclic.stupidTruncTriangleh_distinguished K (a - 1))
  have hTail' : T.obj₃.IsLE (a - 1 + N - 1) := by
    have : (Rf.obj (DerivedCategory.Q.obj tail)).IsLE (a - 1 + N - 1) :=
      hUpper (DerivedCategory.Q.obj tail) (a - 1)
        (isQuasicoherent_derived_homology tail (isQuasicoherent_stupidTruncLE K hqc (a - 1)))
        (Stacks.DerivedAcyclic.isLE_stupidTruncLE K (a - 1))
    exact DerivedCategory.TStructure.t.isLE_of_iso
      (Rf.mapIso ((DerivedCategory.quotientCompQhIso X.Modules).symm.app tail))
      (a - 1 + N - 1)
  have hepi : Epi ((DerivedCategory.homologyFunctor B q).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor B 0).homologySequence_epi_shift_map_mor₁_iff
      T hT q).2 ((T.obj₃.isZero_of_isLE (a - 1 + N - 1) q (by omega)).eq_of_tgt _ _)
  have hmono : Mono ((DerivedCategory.homologyFunctor B q).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor B 0).homologySequence_mono_shift_map_mor₁_iff
      T hT (q - 1) q (by omega)).2
      ((T.obj₃.isZero_of_isLE (a - 1 + N - 1) (q - 1) (by omega)).eq_of_src _ _)
  have hiso : IsIso ((DerivedCategory.homologyFunctor B q).map T.mor₁) :=
    isIso_of_mono_of_epi _
  change IsIso ((DerivedCategory.homologyFunctor B q).map
    ((DerivedCategory.Qh ⋙ Rf).map
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).map
        (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE (a - 1 + 1)))))) at hiso
  rw [show a - 1 + 1 = a by omega] at hiso
  simpa only [Functor.comp_map] using hiso

/-! ### The comparison after restriction to an open of the target -/

/-- Pullback along an open immersion preserves quasi-coherence of a cohomology sheaf of an
object of the derived category. -/
theorem isQuasicoherent_homology_mapDerivedCategory_pullback
    {X U : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i]
    [PreservesFiniteLimits (Scheme.Modules.pullback i)] (E : DerivedCategory X.Modules) (n : ℤ)
    (hqc : ((DerivedCategory.homologyFunctor X.Modules n).obj E).IsQuasicoherent) :
    ((DerivedCategory.homologyFunctor U.Modules n).obj
      ((Scheme.Modules.pullback i).mapDerivedCategory.obj E)).IsQuasicoherent := by
  have hres : ((Scheme.Modules.restrictFunctor i).obj
    ((DerivedCategory.homologyFunctor X.Modules n).obj E)).IsQuasicoherent := inferInstance
  exact (SheafOfModules.isQuasicoherent U.ringCatSheaf).prop_of_iso
    ((mapDerivedCategoryCompHomologyFunctorIso (Scheme.Modules.pullback i) n).app E).symm
    ((SheafOfModules.isQuasicoherent U.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback i).app _) hres)

/-- **The bound of [Stacks, Tag 08D5], after restriction to a quasi-compact open of the
target.** For `j : V ⟶ S` an open immersion with `V` quasi-compact, the composite of `Rf_*` with
pullback along `j` raises the upper bound of an object with quasi-coherent cohomology by a fixed
amount.

The square cut out by `V` is a pullback, so [Stacks, Tag 08FE] identifies the composite with
the derived direct image along the restricted morphism `f⁻¹V ⟶ V`, whose target is
quasi-compact. -/
theorem isLE_rightDerived_pullback_obj
    {X S V : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (j : V ⟶ S) [IsOpenImmersion j] [CompactSpace V]
    (Rf : DerivedCategory X.Modules ⥤ DerivedCategory S.Modules)
    (α : (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
    [PreservesFiniteLimits (Scheme.Modules.pullback j)] :
    ∃ N : ℤ, ∀ (E : DerivedCategory X.Modules) (d : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) →
      E.IsLE d →
      (((Rf ⋙ (Scheme.Modules.pullback j).mapDerivedCategory).obj E)).IsLE (d + N - 1) := by
  let U := Limits.pullback f j
  let i : U ⟶ X := Limits.pullback.fst f j
  let g : U ⟶ V := Limits.pullback.snd f j
  have : PreservesFiniteLimits (Scheme.Modules.pullback i) :=
    pullback_preservesFiniteLimits_of_isOpenImmersion i
  let Fi := Scheme.Modules.pullback i
  let Fj := Scheme.Modules.pullback j
  let Ri := Fi.mapDerivedCategory
  let Rj := Fj.mapDerivedCategory
  let αi := Fi.mapDerivedCategoryFactorsh.inv
  let αj := Fj.mapDerivedCategoryFactorsh.inv
  have hiR : Ri.IsRightDerivedFunctor αi
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ Ri Fi.mapDerivedCategoryFactorsh
  have hjR : Rj.IsRightDerivedFunctor αj
      (HomotopyCategory.quasiIso S.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ Rj Fj.mapDerivedCategoryFactorsh
  have hfR : Rf.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) := inferInstance
  have hgR : (schemeDerivedPushforward g).IsRightDerivedFunctor
      (schemeDerivedPushforwardUnit g)
      (HomotopyCategory.quasiIso U.Modules (ComplexShape.up ℤ)) := inferInstance
  -- The four right-derived-functor witnesses are supplied explicitly: their statements are
  -- phrased in the scheme spelling of the module categories, which instance search does not
  -- unify with the ringed-space spelling of [Stacks, Tag 08FE].
  let e : Rf ⋙ Rj ≅ Ri ⋙ schemeDerivedPushforward g :=
    @Stacks.Cohomology.derivedPushforwardRestrictIso _ _ _ _
      (hom f) (hom i) (hom j) (hom g) _ _
      (isPullback_toShHom i g f j (IsPullback.of_hasPullback f j)) _ _ _ _
      Rf (schemeDerivedPushforward g) Ri Rj α (schemeDerivedPushforwardUnit g) αi αj
      hfR hgR hiR hjR
  obtain ⟨N, hN⟩ := isLE_rightDerived_obj_of_isQuasicoherent g
    (schemeDerivedPushforward g) (schemeDerivedPushforwardUnit g)
  refine ⟨N, fun E d hqc hE => ?_⟩
  have hqc' : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor U.Modules n).obj (Ri.obj E)).IsQuasicoherent := fun n =>
    isQuasicoherent_homology_mapDerivedCategory_pullback i E n (hqc n)
  have hE' : (Ri.obj E).IsLE d := by
    rw [DerivedCategory.isLE_iff]
    intro n hn
    have : E.IsLE d := hE
    exact (Fi.map_isZero (E.isZero_of_isLE d n hn)).of_iso
      ((mapDerivedCategoryCompHomologyFunctorIso Fi n).app E)
  have : ((Ri ⋙ schemeDerivedPushforward g).obj E).IsLE (d + N - 1) := hN _ d hqc' hE'
  exact DerivedCategory.TStructure.t.isLE_of_iso (e.app E).symm (d + N - 1)

/-- **The comparison is invertible after pullback to a quasi-compact open of the target.**
For each cohomological degree `q`, the stupid truncation `σ^{≥a}K` with `a` small enough is
bounded below with right-acyclic terms, so the comparison is invertible there; and both sides of
the naturality square for `σ^{≥a}K → K` see that map as an isomorphism on `H^q`. -/
theorem isIso_homologyFunctor_map_pullback_app
    {X S V : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (j : V ⟶ S) [IsOpenImmersion j] [CompactSpace V]
    (K : CochainComplex X.Modules ℤ)
    (hqc : ∀ n, (K.X n).IsQuasicoherent)
    (hacyclic : ∀ n, (Scheme.Modules.pushforward f).rightAcyclic (K.X n))
    (Rf : DerivedCategory X.Modules ⥤ DerivedCategory S.Modules)
    (α : (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
    [PreservesFiniteLimits (Scheme.Modules.pullback j)] (q : ℤ) :
    IsIso (((Scheme.Modules.pullback j).mapDerivedCategory ⋙
      DerivedCategory.homologyFunctor V.Modules q).map
        (α.app ((HomotopyCategory.quotient _ _).obj K))) := by
  let F := Scheme.Modules.pushforward f
  let Fj := Scheme.Modules.pullback j
  let Rj := Fj.mapDerivedCategory
  let Φ := Rj ⋙ DerivedCategory.homologyFunctor V.Modules q
  let : Rf.CommShift ℤ := Functor.IsRightDerivedFunctor.commShift Rf α
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) ℤ
  have : Rf.IsTriangulated :=
    Stacks.DerivedAcyclic.isTriangulated_of_isRightDerivedFunctor F Rf α
  obtain ⟨N, hUpper⟩ := isLE_rightDerived_pullback_obj f j Rf α
  obtain ⟨a, ha₁, ha₂⟩ : ∃ a : ℤ, a < q ∧ a + N ≤ q := ⟨min (q - 1) (q - N), by omega, by omega⟩
  let g : _ ⟶ K := K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a)
  let v := (HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).map g
  have hleft : IsIso (Φ.map
      ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map v)) := by
    have := Stacks.DerivedAcyclic.isIso_homologyFunctor_map_termwise_stupidTrunc F K a q ha₁
    exact (NatIso.isIso_map_iff (mapDerivedCategoryCompHomologyFunctorIso Fj q) _).2
      (Fj.map_isIso ((DerivedCategory.homologyFunctor S.Modules q).map
        ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map v)))
  have hright : IsIso (Φ.map (Rf.map (DerivedCategory.Qh.map v))) :=
    isIso_homologyFunctor_map_rightDerived_stupidTrunc (Rf ⋙ Rj) N hUpper K hqc a q ha₂
  have htail : IsIso (α.app ((HomotopyCategory.quotient _ _).obj
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)))) :=
    Stacks.DerivedAcyclic.isIso_app_of_plus_of_rightAcyclic F Rf α _
      (Stacks.DerivedAcyclic.plus_stupidTruncGE K a)
      (Stacks.DerivedAcyclic.rightAcyclic_stupidTruncGE F K hacyclic a)
  have hcomp : IsIso
      (Φ.map ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map v) ≫
        Φ.map (α.app ((HomotopyCategory.quotient _ _).obj K))) := by
    rw [← Functor.map_comp, α.naturality v, Functor.map_comp]
    change IsIso (Φ.map (α.app ((HomotopyCategory.quotient _ _).obj
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)))) ≫
      Φ.map (Rf.map (DerivedCategory.Qh.map v)))
    infer_instance
  exact IsIso.of_isIso_comp_left
    (Φ.map ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map v)) _

/-- **Stacks Project, Tag 0G9N.** Let `f : X ⟶ S` be a quasi-separated and quasi-compact
morphism of schemes and let `K` be a complex of quasi-coherent `𝒪_X`-modules each of which is
right acyclic for `f_*`. Then `f_* K` represents `Rf_* K` in `D(𝒪_S)`: the canonical comparison
from the termwise direct image to any right derived direct image is an isomorphism at `K`. -/
@[stacks 0G9N]
theorem isIso_to_rightDerived_of_termwise_acyclic
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (K : CochainComplex X.Modules ℤ)
    (hqc : ∀ n, (K.X n).IsQuasicoherent)
    (hacyclic : ∀ n, (Scheme.Modules.pushforward f).rightAcyclic (K.X n))
    (Rf : DerivedCategory X.Modules ⥤ DerivedCategory S.Modules)
    (α : (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
    [Rf.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))] :
    IsIso (α.app ((HomotopyCategory.quotient _ _).obj K)) := by
  rw [DerivedCategory.isIso_iff]
  intro q
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict _
    (fun V : S.affineOpens => (V : S.Opens)) (IsOpenCover.mk (iSup_affineOpens_eq_top S))
    fun V => ?_
  let j : (V : S.Opens).toScheme ⟶ S := (V : S.Opens).ι
  have : IsAffine (V : S.Opens).toScheme := V.2
  have : CompactSpace (V : S.Opens).toScheme :=
    Scheme.compactSpace_of_isAffine (V : S.Opens).toScheme
  have : PreservesFiniteLimits (Scheme.Modules.pullback j) :=
    pullback_preservesFiniteLimits_of_isOpenImmersion j
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback j) _).2
    ((NatIso.isIso_map_iff
      (mapDerivedCategoryCompHomologyFunctorIso (Scheme.Modules.pullback j) q)
      (α.app ((HomotopyCategory.quotient _ _).obj K))).1
      (isIso_homologyFunctor_map_pullback_app f j K hqc hacyclic Rf α q))

end AlgebraicGeometry

end
