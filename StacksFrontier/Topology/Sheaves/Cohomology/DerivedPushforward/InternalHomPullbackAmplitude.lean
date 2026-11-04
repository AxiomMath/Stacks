module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackFlatPseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackStrictlyPerfect
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZeroExact

/-!
# Tag 0GM7 for a derived pullback of bounded cohomological amplitude

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `d` an integer such that
`Lh^*` carries objects of `D(𝒪_Y)` with cohomology vanishing below `a` to objects with cohomology
vanishing below `a - d`.  For `K ∈ D(𝒪_Y)` pseudo-coherent and `M ∈ D(𝒪_Y)` locally bounded
below, the canonical map of Tag 08I3,

`Lh^*R𝓗om(K, M) ⟶ R𝓗om(Lh^*K, Lh^*M)`,

is an isomorphism.  This is the argument of the source for clauses (2) and (3) of Tag 0GM7: the
question is local on `Y`, locally `M` is bounded below and `K` is approximated in each degree by
a strictly perfect complex, at which the map is invertible, and the truncation estimate, now with
the loss `d` of the amplitude of `Lh^*`, carries invertibility in the given degree from the
approximation to `K`.

All declarations live in the namespace `Stacks.Cohomology.DerivedInternalHomPullback`.

## Main definitions

* `HasDerivedPullbackAmplitude`

## Main results

* `HasDerivedPullbackAmplitude.restrictedMorphism`
* `isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent_of_amplitude`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry Stacks.Cohomology.HigherDirectImage

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (h : X ⟶ Y)

section Def

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-- `Lh^*` lowers lower bounds on cohomology by at most `d`: an object of `D(𝒪_Y)` whose
cohomology vanishes below `a` is carried to one whose cohomology vanishes below `a - d`. -/
def HasDerivedPullbackAmplitude (d : ℤ) : Prop :=
  ∀ (N : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) (a : ℤ),
    N.IsGE a → ((derivedPullbackFunctor h).obj N).IsGE (a - d)

end Def

/-- An exact functor read on derived categories preserves lower bounds on cohomology. -/
theorem isGE_mapDerivedCategory_obj {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K : DerivedCategory C) (a : ℤ)
    (hK : K.IsGE a) : (F.mapDerivedCategory.obj K).IsGE a := by
  rw [DerivedCategory.isGE_iff] at hK ⊢
  intro i hi
  exact (F.map_isZero (hK i hi)).of_iso
    ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F i).app K)

/-- **Every object of `D(𝒪_V)` is the restriction of an object of `D(𝒪_Y)` with the same lower
bound**: its extension by zero `j_!`, which is exact and fully faithful. -/
theorem exists_isGE_restriction (V : TopologicalSpace.Opens Y)
    (N' : DerivedCategory (SheafOfModules.{u} (ExtensionByZeroModules.resRing V
      (structureSheafRing Y)))) (a : ℤ) (hN' : N'.IsGE a) :
    ∃ N : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)),
      N.IsGE a ∧ Nonempty (N' ≅ (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Y.ofRestrict V.isOpenEmbedding)).obj N) := by
  have := Stacks.Cohomology.DerivedOpenImmersion.isIso_jShriekDerivedPullbackAdjunction_unit Y V
  have := NatIso.isIso_app_of_isIso
    (Stacks.Cohomology.DerivedOpenImmersion.jShriekDerivedPullbackAdjunction Y V).unit N'
  exact ⟨_, isGE_mapDerivedCategory_obj _ N' a hN',
    ⟨asIso ((Stacks.Cohomology.DerivedOpenImmersion.jShriekDerivedPullbackAdjunction Y V).unit.app
      N')⟩⟩

section Restriction

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-- **The amplitude of `Lh^*` bounds that of its restriction over an open subspace of the
target.**  An object `N'` of `D(𝒪_V)` is the restriction of its extension by zero `j_!N'`, which
has the same lower bound, and `Lh|_{h⁻¹(V)}^* (j_!N')|_V = (Lh^* j_!N')|_{h⁻¹(V)}`. -/
theorem HasDerivedPullbackAmplitude.restrictedMorphism {d : ℤ}
    (hd : HasDerivedPullbackAmplitude h d) (V : TopologicalSpace.Opens Y) :
    HasDerivedPullbackAmplitude (Stacks.Cohomology.HigherDirectImage.restrictedMorphism h V) d := by
  intro N' a hN'
  obtain ⟨N, hN, ⟨eN⟩⟩ := exists_isGE_restriction V N' a hN'
  have hsq := restrictedMorphism_comp_openSubspaceInclusion h V
  let e : (derivedPullbackFunctor (Stacks.Cohomology.HigherDirectImage.restrictedMorphism h V)).obj
      N' ≅ (derivedPullbackFunctor (openSubspaceInclusion X (preimageOpen h V))).obj
        ((derivedPullbackFunctor h).obj N) :=
    (derivedPullbackFunctor (Stacks.Cohomology.HigherDirectImage.restrictedMorphism h V)).mapIso
        eN ≪≫
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        (Stacks.Cohomology.HigherDirectImage.restrictedMorphism h V)
        (openSubspaceInclusion Y V)).app N ≪≫
      eqToIso (congrArg (fun q => (derivedPullbackFunctor q).obj N) hsq.symm) ≪≫
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        (openSubspaceInclusion X (preimageOpen h V)) h).app N).symm
  have := isGE_derivedPullback_obj_of_isFlat _
    (isFlat_openSubspaceInclusion X (preimageOpen h V)) _ (a - d) (hd N a hN)
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm (a - d)

end Restriction

section Truncation

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-- A triangulated functor between derived categories carries the second morphism of a
distinguished triangle to an isomorphism on cohomology in every degree `i` with `i + 1 < n`, when
the image of the first vertex is bounded below by `n`. -/
theorem isIso_homologyMap_map_mor₂_of_isGE₁ {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ] [F.IsTriangulated]
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (i n : ℤ)
    (hGE : (F.obj T.obj₁).IsGE n) (hi : i + 1 < n) :
    IsIso ((DerivedCategory.homologyFunctor D i).map (F.map T.mor₂)) :=
  DerivedCategory.isIso_homologyMap_mor₂_of_isGE₁ (F.mapTriangle.obj T) (F.map_distinguished T hT)
    i n hGE hi

private instance : (derivedPullbackFunctor h).CommShift ℤ :=
  Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift h

private instance : (derivedPullbackFunctor h).IsTriangulated :=
  Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated h

/-- **`Lh^*` of the truncation estimate.**  Let `A ⟶ K ⟶ C ⟶ A[1]` be a distinguished triangle of
`D(𝒪_Y)` with `C` bounded above by `n`, and let `M` be bounded below by `a`.  Then `Lh^*` of the
map `R𝓗om(K, M) ⟶ R𝓗om(A, M)` is invertible on cohomology in every degree `j` with
`j + 1 < a - n - d`. -/
theorem isIso_homologyMap_derivedPullback_map_derivedSheafHom_of_amplitude {d : ℤ}
    (hd : HasDerivedPullbackAmplitude h d)
    (T : Triangle (DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)))
    (hT : T ∈ distTriang _) (n : ℤ) (hC : T.obj₃.IsLE n)
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) (a : ℤ)
    (hM : M.IsGE a) (j : ℤ) (hj : j + 1 < a - n - d) :
    IsIso ((DerivedCategory.homologyFunctor _ j).map ((derivedPullbackFunctor h).map
      (((AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor
        (Stacks.SheafOfModules.ringedSite Y.sheaf)).flip.obj M).map T.mor₁.op))) := by
  obtain ⟨δ, hδ⟩ := AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom
    (Stacks.SheafOfModules.ringedSite Y.sheaf) M T hT
  exact isIso_homologyMap_map_mor₂_of_isGE₁ (derivedPullbackFunctor h) _ hδ j (a - n - d)
    (hd _ (a - n) (AlgebraicGeometry.RingedSite.isGE_derivedSheafHom
      (Stacks.SheafOfModules.ringedSite Y.sheaf) T.obj₃ M n a hC hM)) hj

/-- **The truncation step of Tag 0GM7 at a derived pullback of amplitude `d`.**  Let
`A ⟶ K ⟶ C ⟶ A[1]` be a distinguished triangle of `D(𝒪_Y)` with `C` bounded above by `n`, and
let `M ∈ D(𝒪_Y)` be bounded below by `a`.  If the canonical map of Tag 08I3 is invertible at
`(A, M)`, then at `(K, M)` it is invertible on cohomology in every degree `j` with
`j + 1 < a - n - d`. -/
theorem isIso_homologyMap_derivedPullbackSheafHomMap_of_distTriang_of_amplitude {d : ℤ}
    (hd : HasDerivedPullbackAmplitude h d)
    (T : Triangle (DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)))
    (hT : T ∈ distTriang _) (n : ℤ) (hC : T.obj₃.IsLE n)
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) (a : ℤ)
    (hM : M.IsGE a) (hA : IsIso (derivedPullbackSheafHomMap h T.obj₁ M)) (j : ℤ)
    (hj : j + 1 < a - n - d) :
    IsIso ((DerivedCategory.homologyFunctor _ j).map (derivedPullbackSheafHomMap h T.obj₂ M)) := by
  have sq := Transpose.homComparison_naturality_source (derivedPullbackFunctor h)
    (Stacks.SheafOfModules.derivedSheafHom Y.sheaf) (Stacks.SheafOfModules.derivedSheafHom X.sheaf)
    (internalHomTensorUncurried Y) (internalHomTensorUncurried X)
    (fun A B C => (AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
      (Stacks.SheafOfModules.ringedSite Y.sheaf) A B C).toEquiv)
    (fun A B C => (AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
      (Stacks.SheafOfModules.ringedSite X.sheaf) A B C).toEquiv)
    (pullbackTensorIso h)
    (tensorHomEquivNaturalLeft_ringedSpace Y) (tensorHomEquivDinatural_ringedSpace Y)
    (tensorHomEquivNaturalLeft_ringedSpace X) (tensorHomEquivDinatural_ringedSpace X) T.mor₁ M
  have hX := AlgebraicGeometry.RingedSite.isIso_homologyMap_derivedSheafHom_map_of_isLE₃
    (Stacks.SheafOfModules.ringedSite X.sheaf) ((derivedPullbackFunctor h).mapTriangle.obj T)
    ((derivedPullbackFunctor h).map_distinguished T hT) n
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.isLE_derivedPullback_obj h T.obj₃ n hC)
    ((derivedPullbackFunctor h).obj M) (a - d) (hd M a hM) j (by omega)
  have hPY := isIso_homologyMap_derivedPullback_map_derivedSheafHom_of_amplitude h hd T hT n hC M
    a hM j hj
  have hsq := congrArg (DerivedCategory.homologyFunctor _ j).map sq
  rw [Functor.map_comp, Functor.map_comp] at hsq
  have hrhs : IsIso ((DerivedCategory.homologyFunctor _ j).map
      (derivedPullbackSheafHomMap h T.obj₂ M) ≫ (DerivedCategory.homologyFunctor _ j).map
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map
          ((derivedPullbackFunctor h).map T.mor₁).op).app ((derivedPullbackFunctor h).obj M))) := by
    refine (congrArg IsIso hsq).mp ?_
    have hA' : IsIso ((DerivedCategory.homologyFunctor _ j).map
        (derivedPullbackSheafHomMap h T.obj₁ M)) := Functor.map_isIso _ _
    exact IsIso.comp_isIso' hPY hA'
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hX hrhs

/-- **Tag 0GM7 at an approximation, for a derived pullback of amplitude `d`.**  Let
`α : P ⟶ E` be a morphism of complexes of `𝒪_Y`-modules inducing isomorphisms on cohomology in
degrees `> m` and a surjection in degree `m`, and let `M ∈ D(𝒪_Y)` be bounded below by `a`.  If
the canonical map of Tag 08I3 is invertible at `(P, M)`, then at `(E, M)` it is invertible on
cohomology in every degree `j < a - m - d`. -/
theorem isIso_homologyMap_derivedPullbackSheafHomMap_of_approximation_of_amplitude {d : ℤ}
    (hd : HasDerivedPullbackAmplitude h d)
    {P E : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ}
    (α : P ⟶ E) (m : ℤ) (hiso : ∀ i : ℤ, m < i → IsIso (HomologicalComplex.homologyMap α i))
    (hepi : Epi (HomologicalComplex.homologyMap α m))
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) (a : ℤ)
    (hM : M.IsGE a) (hP : IsIso (derivedPullbackSheafHomMap h (DerivedCategory.Q.obj P) M))
    (j : ℤ) (hj : j < a - m - d) :
    IsIso ((DerivedCategory.homologyFunctor _ j).map
      (derivedPullbackSheafHomMap h (DerivedCategory.Q.obj E) M)) := by
  obtain ⟨Z, g, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle (DerivedCategory.Q.map α)
  have hC := DerivedCategory.isLE_three_of_homologyMap_mor₁ _ hT m
    (fun i hi => (DerivedCategory.isIso_homologyFunctor_map_Q_map_iff α i).2 (hiso i hi))
    ((DerivedCategory.epi_homologyFunctor_map_Q_map_iff α m).2 hepi)
  exact isIso_homologyMap_derivedPullbackSheafHomMap_of_distTriang_of_amplitude h hd _ hT (m - 1)
    hC M a hM hP j (by omega)

/-- **Tag 0GM7 for a derived pullback of amplitude `d`, under a global lower bound, degree by
degree.** -/
theorem isIso_homologyMap_derivedPullbackSheafHomMap_of_isPseudoCoherent_of_amplitude {d : ℤ}
    (hd : HasDerivedPullbackAmplitude h d)
    (K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (hK : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := Y) K)
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) (a : ℤ)
    (hM : M.IsGE a) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor _ n).map (derivedPullbackSheafHomMap h K M)) := by
  obtain ⟨E, hE, ⟨eE⟩⟩ := hK
  refine (isIso_map_derivedPullbackSheafHomMap_iff_of_iso h _ eE M).1 ?_
  refine isIso_homologyMap_derivedPullbackSheafHomMap_of_local h n _ M fun x => ?_
  obtain ⟨U, hyU, P, hP, α, hα₁, hα₂⟩ := hE (a - n - d - 1) (h.hom.base x)
  refine ⟨U, hyU, ?_⟩
  refine (isIso_map_derivedPullbackSheafHomMap_iff_of_iso
    (Stacks.Cohomology.HigherDirectImage.restrictedMorphism h U) _
    (derivedPullbackOpenSubspaceQIso Y U E).symm _).1 ?_
  exact isIso_homologyMap_derivedPullbackSheafHomMap_of_approximation_of_amplitude
    (Stacks.Cohomology.HigherDirectImage.restrictedMorphism h U) (hd.restrictedMorphism h U) α
    (a - n - d - 1) hα₁ hα₂ _ a
    (isGE_derivedPullback_obj_of_isFlat _ (isFlat_openSubspaceInclusion Y U) M a hM)
    (isIso_derivedPullbackSheafHomMap_of_isStrictlyPerfect _ P hP _) n (by omega)

/-- **Tag 0GM7 for a derived pullback of bounded amplitude.**  Let `h : X ⟶ Y` be a morphism of
ringed spaces such that `Lh^*` lowers lower bounds on cohomology by at most `d`.  For a
pseudo-coherent `K ∈ D(𝒪_Y)` and a locally bounded below `M ∈ D(𝒪_Y)`, the canonical map
`Lh^*R𝓗om(K, M) ⟶ R𝓗om(Lh^*K, Lh^*M)` is an isomorphism. -/
theorem isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent_of_amplitude {d : ℤ}
    (hd : HasDerivedPullbackAmplitude h d)
    (K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (hK : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := Y) K)
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (hM : AlgebraicGeometry.RingedSpace.IsLocallyBoundedBelow Y M) :
    IsIso (derivedPullbackSheafHomMap h K M) := by
  -- The criterion is applied rather than rewritten with.  `rw` has to abstract the pattern out
  -- of the target and so typechecks it at `implicit` transparency, where this file's
  -- reducibility list unfolds `X.sheaf` far enough that the two `Abelian` instances on module
  -- sheaves -- `ResolutionByExtensionsByZero.instAbelian X.sheaf`, which `K` carries, and
  -- `SheafOfModules.instAbelian` of the composed ring sheaf, which the derived internal hom
  -- binds -- are confronted as terms, and the target stops being type-correct; the pattern then
  -- matches nothing.  Applying the `iff` only unifies its conclusion with the goal, which needs
  -- no abstraction and no motive.
  refine (DerivedCategory.isIso_iff _ _).2 fun n => ?_
  refine isIso_homologyMap_derivedPullbackSheafHomMap_of_local h n K M fun x => ?_
  obtain ⟨U, hyU, N, hN⟩ := exists_isGE_derivedPullback_openSubspace Y M hM (h.hom.base x)
  exact ⟨U, hyU, isIso_homologyMap_derivedPullbackSheafHomMap_of_isPseudoCoherent_of_amplitude
    (Stacks.Cohomology.HigherDirectImage.restrictedMorphism h U) (hd.restrictedMorphism h U) _
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherent_derivedPullback
      (openSubspaceInclusion Y U) K hK) _ N hN n⟩

end Truncation

end Stacks.Cohomology.DerivedInternalHomPullback

end
