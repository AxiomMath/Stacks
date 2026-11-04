module

public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsDirectImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TrivialRingSheafModules
public import StacksFrontier.Algebra.Homology.DerivedCategory.StupidTruncationTriangle
public import StacksFrontier.Homology.Perfect.StupidFiltration
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactPushforwardCounit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.VanishingOverOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TriangulatedSubcategory
import StacksCore.Tactic.StacksAttribute

/-!
# Perfectness of the derived direct image of the relative de Rham complex

For a proper smooth morphism `f : X ⟶ S` the derived direct image `Rf_*Ω^•_{X/S}` of the
relative de Rham complex along `(X, f^{-1}𝒪_S) ⟶ S` is a perfect object of `D(𝒪_S)`:
`isPerfect_derivedPushforward_deRhamComplex`, the perfectness assertion of [Stacks, Tag 0FM0]
for the de Rham complex. It is deduced from the perfectness of the `Rf_*Ω^p_{X/S}` along the
stupid filtration.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.DeRhamDirectImage

universe u

namespace AlgebraicGeometry.ProperSmoothDeRham

noncomputable section

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The direct image along `(X, 𝒪_X) ⟶ (X, f^{-1}𝒪_S)` — restriction of scalars along
`f^{-1}𝒪_S ⟶ 𝒪_X` — is right exact. -/
instance preservesFiniteColimits_modulePushforward_toInverseImageBase :
    PreservesFiniteColimits (modulePushforward (toInverseImageBase f)) :=
  inferInstanceAs (PreservesFiniteColimits (pushforward (toInverseImageBase f)))

/-- **`Rπ_*` of a restriction of scalars is `Rf_*`.** For an `𝒪_X`-module `M` placed in
degree `k`, the derived direct image along `π : (X, f^{-1}𝒪_S) ⟶ S` of its restriction of
scalars to `f^{-1}𝒪_S` is the derived direct image along `f` of `M`: restriction of scalars is
exact, hence its own derived functor, and the two direct images compose to that of `f`. -/
def derivedPushforwardSingleRestrictIso (M : X.Modules) (k : ℤ) :
    (derivedPushforward (inverseImageBaseProjection f)).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u}
          (structureSheafRing (inverseImageBase f))) k).obj
            ((modulePushforward (toInverseImageBase f)).obj M)) ≅
      (derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u}
          (structureSheafRing X.toRingedSpace)) k).obj M) :=
  (derivedPushforward (inverseImageBaseProjection f)).mapIso
    ((DerivedCategory.singleFunctorIsoCompQ _ k).app _ ≪≫
      (DerivedCategory.quotientCompQhIso _).symm.app _ ≪≫
      DerivedCategory.Qh.mapIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (modulePushforward
          (toInverseImageBase f)) (ComplexShape.up ℤ) k).app M).symm) ≪≫
      @asIso _ _ _ _ ((derivedPushforwardUnit (toInverseImageBase f)).app _)
        (Stacks.Cohomology.ExactPushforwardAdjunction.isIso_derivedPushforwardUnit_app
          (toInverseImageBase f) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj M))) ≪≫
      (derivedPushforward (toInverseImageBase f)).mapIso
        ((DerivedCategory.quotientCompQhIso _).app _ ≪≫
          ((DerivedCategory.singleFunctorIsoCompQ _ k).app _).symm)) ≪≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso _ _).app _ ≪≫
    eqToIso (congrArg (fun φ => (derivedPushforward φ).obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{u}
          (structureSheafRing X.toRingedSpace)) k).obj M)) (toInverseImageBase_comp f))

/-- **`Rf_*Ω^p_{X/S}` placed in any degree is perfect** for a proper smooth `f`: it is a shift of
`Rf_*Ω^p_{X/S}`, which is perfect by `isPerfect_derivedPushforward_forms`. -/
theorem isPerfect_derivedPushforward_singleFunctor_forms [IsProper f] [Smooth f] (p : ℕ)
    (k : ℤ) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u}
          (structureSheafRing X.toRingedSpace)) k).obj
            (Scheme.Hom.relativeDifferentialForms f (p : ℤ)))) := by
  let := derivedPushforwardCommShift f.toLRSHom.toShHom
  have e₀ : (DerivedCategory.singleFunctor (SheafOfModules.{u}
      (structureSheafRing X.toRingedSpace)) 0).obj
        (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) ≅ formsObj f p :=
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app _ ≪≫
      (DerivedCategory.quotientCompQhIso _).symm.app _
  have e₁ : (DerivedCategory.singleFunctor (SheafOfModules.{u}
      (structureSheafRing X.toRingedSpace)) k).obj
        (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) ≅ (formsObj f p)⟦-k⟧ :=
    ((DerivedCategory.singleFunctors _).shiftIso (-k) k 0 (by omega)).symm.app _ ≪≫
      (shiftFunctor _ (-k)).mapIso e₀
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    (((derivedPushforward f.toLRSHom.toShHom).commShiftIso (-k)).symm.app _ ≪≫
      (derivedPushforward f.toLRSHom.toShHom).mapIso e₁.symm)
    (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift
      (isPerfect_derivedPushforward_forms f p) (-k))

/-- **The graded pieces of the stupid filtration of the de Rham complex have perfect direct
images**: `Rπ_*` of `Ω^p_{X/S}`, read as an `f^{-1}𝒪_S`-module and placed in any degree, is
perfect. -/
theorem isPerfect_derivedPushforward_singleFunctor_restrictForms [IsProper f] [Smooth f]
    (p : ℕ) (k : ℤ) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforward (inverseImageBaseProjection f)).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u}
          (structureSheafRing (inverseImageBase f))) k).obj
            ((modulePushforward (toInverseImageBase f)).obj
              (Scheme.Hom.relativeDifferentialForms f (p : ℤ))))) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    (derivedPushforwardSingleRestrictIso f _ k).symm
    (isPerfect_derivedPushforward_singleFunctor_forms f p k)

/-- The relative de Rham complex `Ω^•_{X/S}`, extended by zero to `ℤ`, as a complex of
`f^{-1}𝒪_S`-modules written over `structureSheafRing (X, f^{-1}𝒪_S)`, the spelling the derived
direct image is taken at. -/
abbrev deRhamComplexInt : CochainComplex (SheafOfModules.{u}
    (structureSheafRing (inverseImageBase f))) ℤ :=
  deRhamCochainComplex f

/-- The degree-`p` term of the extended de Rham complex is `Ω^p_{X/S}` with its scalars
restricted to `f^{-1}𝒪_S`. -/
def deRhamComplexIntXIso (p : ℕ) :
    (deRhamComplexInt f).X (p : ℤ) ≅
      (modulePushforward (toInverseImageBase f)).obj
        (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) :=
  (Scheme.Hom.deRhamComplex f).extendXIso ComplexShape.embeddingUpNat (i := p) rfl

/-- The extended de Rham complex vanishes in negative degrees. -/
theorem isZero_deRhamComplexInt_X_of_neg (n : ℤ) (hn : n < 0) :
    IsZero ((deRhamComplexInt f).X n) :=
  HomologicalComplex.isZero_extend_X _ _ n fun i hi => by
    change (i : ℤ) = n at hi
    omega

/-- **A module whose sections over every open inside `U` are trivial restricts to zero on `U`.**
Pullback along the inclusion of the open subspace `U` is restriction of modules, whose sections
over an open of `U` are the sections over its image. -/
theorem isZero_modulePullback_ofRestrict {Y : RingedSpace.{u, u}} (U : Opens Y.carrier)
    (M : SheafOfModules.{u} (structureSheafRing Y))
    (h : ∀ W : Opens Y.carrier, W ≤ U → Subsingleton (M.val.obj (Opposite.op W))) :
    IsZero ((modulePullback (Y.ofRestrict U.isOpenEmbedding)).obj M) := by
  refine IsZero.of_iso ?_
    ((Stacks.Cohomology.DerivedOpenImmersion.modulePullbackJStarIso Y U).app M)
  refine Stacks.SheafOfModules.isZero_of_forall_subsingleton_sections _ fun W => ?_
  refine h _ ?_
  rintro _ ⟨y, -, rfl⟩
  exact y.2

/-- **The terms of high degree of the de Rham complex restrict to zero over an open of the
base** over which the forms of high degree vanish. -/
theorem isZero_modulePullback_deRhamComplexInt_X (V : S.Opens) {N : ℕ}
    (hN : ∀ p : ℕ, N < p → ∀ W : X.Opens, W ≤ f ⁻¹ᵁ V →
      Subsingleton ((Scheme.Hom.relativeDifferentialForms f (p : ℤ)).val.obj (Opposite.op W)))
    (n : ℤ) (hn : (N : ℤ) < n) :
    IsZero ((modulePullback ((inverseImageBase f).ofRestrict
      (Stacks.Cohomology.DerivedPushforwardOverOpen.preimageOpen
        (inverseImageBaseProjection f) V).isOpenEmbedding)).obj ((deRhamComplexInt f).X n)) := by
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, (p : ℤ) = n := ⟨n.toNat, by omega⟩
  refine IsZero.of_iso ?_ ((modulePullback _).mapIso (deRhamComplexIntXIso f p))
  exact isZero_modulePullback_ofRestrict _ _ fun W hW => hN p (by omega) W hW

/-- **[Stacks, Tag 0FM0], perfectness of `Rf_*Ω^•_{X/S}`.** For a proper smooth morphism of
schemes `f : X ⟶ S`, the derived direct image of the relative de Rham complex along
`π : (X, f^{-1}𝒪_S) ⟶ S` is a perfect object of `D(𝒪_S)`.

Perfectness is local on `S`. Over an affine open `V ⊆ S` the forms `Ω^p_{X/S}` vanish on
`f^{-1}V` for `p` large, so the restriction to `V` of `Rπ_*σ_{≥p}Ω^•_{X/S}` vanishes; descending
along the triangles `σ_{≥p+1} ⟶ σ_{≥p} ⟶ Ω^p[-p]` of the stupid filtration, the outer vertices
have perfect images — the graded pieces by the perfectness of `Rf_*Ω^p_{X/S}` — and perfectness
has the two-out-of-three property (Stacks 08CR). -/
@[stacks 0FM0 "Rf_*Omega^bullet_X/S is a perfect object of D(O_S) for a proper smooth f: the \
derived direct image of the relative de Rham complex along (X, f^{-1}O_S) -> S"]
theorem isPerfect_derivedPushforward_deRhamComplex [IsProper f] [Smooth f] :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforward (inverseImageBaseProjection f)).obj
        (DerivedCategory.Q.obj (deRhamComplexInt f))) := by
  refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_local_isPerfect.{u, u + 1} _
    fun s => ?_
  obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) trivial
  refine ⟨V, hsV, ?_⟩
  refine Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
    ((AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoDerivedPullback S.toRingedSpace
      V).app _).symm ?_
  have hc : IsCompact ((f ⁻¹ᵁ V : X.Opens) : Set X) :=
    QuasiCompact.isCompact_preimage (f := f) _ V.isOpen hV.isCompact
  obtain ⟨N, hN⟩ := exists_forall_subsingleton_relativeDifferentialForms f _ hc
  let := derivedPushforwardCommShift (inverseImageBaseProjection f)
  have := derivedPushforward_isTriangulated (inverseImageBaseProjection f)
  let F := derivedPushforward (inverseImageBaseProjection f) ⋙
    derivedPullback (S.toRingedSpace.ofRestrict V.isOpenEmbedding)
  let P : DerivedCategory (SheafOfModules.{u} (structureSheafRing (inverseImageBase f))) →
      Prop := fun E => Stacks.Cohomology.PerfectComplexes.IsPerfect (F.obj E)
  -- the top of the filtration vanishes over `V`
  have htop : P (DerivedCategory.Q.obj
      ((deRhamComplexInt f).stupidTrunc (ComplexShape.embeddingUpIntGE ((N : ℤ) + 1)))) := by
    let L := (deRhamComplexInt f).stupidTrunc (ComplexShape.embeddingUpIntGE ((N : ℤ) + 1))
    have hL : ∀ n, IsZero ((modulePullback ((inverseImageBase f).ofRestrict
        (Stacks.Cohomology.DerivedPushforwardOverOpen.preimageOpen
          (inverseImageBaseProjection f) V).isOpenEmbedding)).obj (L.X n)) := by
      intro n
      by_cases hn : (N : ℤ) + 1 ≤ n
      · exact IsZero.of_iso
          (isZero_modulePullback_deRhamComplexInt_X f V hN n (by omega))
          ((modulePullback _).mapIso
            (StacksDraft.StupidTruncation.stupidTruncGEXIso _ _ n hn))
      · exact Functor.map_isZero _ (CochainComplex.isZero_of_isStrictlyGE L ((N : ℤ) + 1) n
          (by omega))
    have hz :=
      Stacks.Cohomology.DerivedPushforwardOverOpen.isZero_derivedPullback_derivedPushforward
        (inverseImageBaseProjection f) V L hL
    exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      ((isZero_zero _).iso hz ≪≫ F.mapIso ((DerivedCategory.quotientCompQhIso _).app L))
      Stacks.Cohomology.PerfectTriangulatedSubcategory.isPerfect_zero
  -- the graded pieces
  have hgr : ∀ p : ℕ, P ((DerivedCategory.singleFunctor _ (p : ℤ)).obj
      ((deRhamComplexInt f).X (p : ℤ))) := by
    intro p
    have h₁ := isPerfect_derivedPushforward_singleFunctor_restrictForms f p p
    have h₂ : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := S.toRingedSpace)
        ((derivedPushforward (inverseImageBaseProjection f)).obj
          ((DerivedCategory.singleFunctor _ (p : ℤ)).obj ((deRhamComplexInt f).X (p : ℤ)))) :=
      Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
        ((derivedPushforward _).mapIso ((DerivedCategory.singleFunctor _ (p : ℤ)).mapIso
          (deRhamComplexIntXIso f p).symm)) h₁
    exact AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
      (S.toRingedSpace.ofRestrict V.isOpenEmbedding) _ h₂
  -- the descending induction along the stupid filtration
  have hstep : ∀ p : ℕ, P (DerivedCategory.Q.obj
      ((deRhamComplexInt f).stupidTrunc (ComplexShape.embeddingUpIntGE ((p : ℤ) + 1)))) →
        P (DerivedCategory.Q.obj
          ((deRhamComplexInt f).stupidTrunc (ComplexShape.embeddingUpIntGE (p : ℤ)))) := by
    intro p hp
    have hT := StacksDraft.StupidTruncation.stupidTruncGETriangle_distinguished
      (deRhamComplexInt f) (p : ℤ)
    exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₂_of_distinguished
      (F.mapTriangle.obj _) (F.map_distinguished _ hT) hp (hgr p)
  have hall : ∀ m p : ℕ, p + m = N + 1 → P (DerivedCategory.Q.obj
      ((deRhamComplexInt f).stupidTrunc (ComplexShape.embeddingUpIntGE (p : ℤ)))) := by
    intro m
    induction m with
    | zero =>
      intro p hp
      have : (p : ℤ) = (N : ℤ) + 1 := by omega
      rw [this]
      exact htop
    | succ m ih =>
      intro p hp
      exact hstep p (by exact_mod_cast ih (p + 1) (by omega))
  have h0 := hall (N + 1) 0 (by omega)
  have : (deRhamComplexInt f).IsStrictlyGE 0 :=
    inferInstanceAs ((deRhamCochainComplex f).IsStrictlyGE 0)
  have := StacksDraft.StupidFiltration.isIso_ιStupidTruncGE (deRhamComplexInt f) 0
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    (F.mapIso (DerivedCategory.Q.mapIso
      (asIso ((deRhamComplexInt f).ιStupidTrunc (ComplexShape.embeddingUpIntGE 0))))) h0

end

end AlgebraicGeometry.ProperSmoothDeRham
