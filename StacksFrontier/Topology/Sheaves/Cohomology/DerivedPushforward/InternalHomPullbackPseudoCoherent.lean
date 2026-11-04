module

public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackDevissage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomBoundedBelow
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatDegreewise
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationComparison
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat

/-!
# The truncation step for derived pullback of the derived internal Hom

Let `h : X ⟶ Y` be a flat morphism of ringed spaces and let `M ∈ D(𝒪_Y)` be bounded below.
Invertibility of the canonical map `Lh^*R𝓗om(K, M) ⟶ R𝓗om(Lh^*K, Lh^*M)` passes from a complex
to a complex it approximates, on cohomology in a range of degrees.

## Main results

* `DerivedCategory.isIso_homologyMap_mor₂_of_isGE₁` and
  `DerivedCategory.isLE_three_of_homologyMap_mor₁`: cohomological estimates for a distinguished
  triangle of a derived category.
* `AlgebraicGeometry.RingedSite.isIso_homologyMap_derivedSheafHom_map_of_isLE₃`: the truncation
  estimate for the derived internal Hom in its contravariant variable.
* `Stacks.Cohomology.DerivedInternalHomPullback.homologyDerivedPullbackIsoOfIsFlat`: derived
  pullback along a flat morphism commutes with cohomology.
* `isIso_homologyMap_derivedPullbackSheafHomMap_of_distTriang` and
  `isIso_homologyMap_derivedPullbackSheafHomMap_of_approximation`, in
  `Stacks.Cohomology.DerivedInternalHomPullback`: this truncation step, for a distinguished
  triangle and for an approximation.
* `Stacks.Cohomology.DerivedInternalHomPullback.isFlat_restrictedMorphism`: the restriction of a
  flat morphism to an open subspace of its target is flat.

## References

* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace DerivedCategory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- In a distinguished triangle whose first vertex is bounded below by `n`, the second morphism
is invertible on cohomology in every degree `i` with `i + 1 < n`. -/
theorem isIso_homologyMap_mor₂_of_isGE₁ (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (i n : ℤ) (hGE : T.obj₁.IsGE n) (hi : i + 1 < n) :
    IsIso ((homologyFunctor C i).map T.mor₂) := by
  have := hGE
  have hepi : Epi ((homologyFunctor C i).map T.mor₂) := by
    rw [HomologySequence.epi_homologyMap_mor₂_iff _ hT i (i + 1) rfl]
    exact (isZero_of_isGE T.obj₁ n (i + 1) hi).eq_zero_of_tgt _
  have hmono : Mono ((homologyFunctor C i).map T.mor₂) := by
    rw [HomologySequence.mono_homologyMap_mor₂_iff _ hT i]
    exact (isZero_of_isGE T.obj₁ n i (by lia)).eq_zero_of_src _
  exact isIso_of_mono_of_epi _

/-- The third vertex of a distinguished triangle whose first morphism is invertible on
cohomology in every degree `> m` and epimorphic in degree `m` is bounded above by `m - 1`. -/
theorem isLE_three_of_homologyMap_mor₁ (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (m : ℤ)
    (hiso : ∀ i : ℤ, m < i → IsIso ((homologyFunctor C i).map T.mor₁))
    (hepi : Epi ((homologyFunctor C m).map T.mor₁)) :
    T.obj₃.IsLE (m - 1) := by
  rw [isLE_iff]
  intro i hi
  have h₁ : Epi ((homologyFunctor C i).map T.mor₁) := by
    rcases eq_or_lt_of_le (show m ≤ i by lia) with h | h
    · subst h; exact hepi
    · have := hiso i h; infer_instance
  have h₂ : Mono ((homologyFunctor C (i + 1)).map T.mor₁) := by
    have := hiso (i + 1) (by lia); infer_instance
  have hβ : (homologyFunctor C i).map T.mor₂ = 0 :=
    (HomologySequence.epi_homologyMap_mor₁_iff _ hT i).1 h₁
  have hδ : HomologySequence.δ T i (i + 1) rfl = 0 :=
    (HomologySequence.mono_homologyMap_mor₁_iff _ hT i (i + 1) rfl).1 h₂
  have : Epi ((homologyFunctor C i).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff _ hT i (i + 1) rfl).2 hδ
  rw [IsZero.iff_id_eq_zero, ← cancel_epi ((homologyFunctor C i).map T.mor₂)]
  simp [hβ]

/-- A morphism of complexes and its image in the derived category induce the same map on
cohomology, up to the identifications `homologyFunctorFactors`: one is invertible exactly when
the other is. -/
theorem isIso_homologyFunctor_map_Q_map_iff {K L : CochainComplex C ℤ} (f : K ⟶ L) (i : ℤ) :
    IsIso ((homologyFunctor C i).map (Q.map f)) ↔ IsIso (HomologicalComplex.homologyMap f i) :=
  NatIso.isIso_map_iff (homologyFunctorFactors C i) f

/-- A morphism of complexes and its image in the derived category: one induces an epimorphism on
cohomology exactly when the other does. -/
theorem epi_homologyFunctor_map_Q_map_iff {K L : CochainComplex C ℤ} (f : K ⟶ L) (i : ℤ) :
    Epi ((homologyFunctor C i).map (Q.map f)) ↔ Epi (HomologicalComplex.homologyMap f i) := by
  have := (homologyFunctorFactors C i).hom.naturality f
  rw [← epi_comp_iff_of_isIso _ ((homologyFunctorFactors C i).hom.app L)]
  erw [this]
  exact epi_comp_iff_of_epi _ _

end DerivedCategory

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Let `A ⟶ K ⟶ C ⟶ A[1]` be a distinguished triangle of `D(O)` with `C` bounded above by `n`,
and let `M` be bounded below by `a`. Then the map `RSheafHom(K, M) ⟶ RSheafHom(A, M)` induced by
`A ⟶ K` is invertible on cohomology in every degree `j` with `j + 1 < a - n`. -/
theorem isIso_homologyMap_derivedSheafHom_map_of_isLE₃
    (T : Triangle
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hT : T ∈ distTriang
      (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) (n : ℤ)
    (hC : T.obj₃.IsLE n)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (a : ℤ)
    (hM : M.IsGE a) (j : ℤ) (hj : j + 1 < a - n) :
    IsIso ((DerivedCategory.homologyFunctor _ j).map
      (((derivedSheafHomBifunctor X).flip.obj M).map T.mor₁.op)) := by
  obtain ⟨δ, hδ⟩ := exists_distinguished_derivedSheafHom X M T hT
  exact DerivedCategory.isIso_homologyMap_mor₂_of_isGE₁ _ hδ j (a - n)
    (isGE_derivedSheafHom X T.obj₃ M n a hC hM) hj

end AlgebraicGeometry.RingedSite

namespace Stacks.Cohomology.DerivedInternalHomPullback

open _root_.Stacks.AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (h : X ⟶ Y)

/-- Derived pullback along a flat morphism commutes with cohomology: `H^j(Lh^*K) ≅ h^*H^j(K)`. -/
def homologyDerivedPullbackIsoOfIsFlat (hh : AlgebraicGeometry.IsFlat h) (j : ℤ) :
    derivedPullbackFunctor h ⋙
        DerivedCategory.homologyFunctor
          (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) j ≅
      DerivedCategory.homologyFunctor
          (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) j ⋙
        modulePullback h :=
  letI : PreservesFiniteLimits (modulePullback h) :=
    preservesFiniteLimits_modulePullback_of_isFlat h hh
  Functor.isoWhiskerRight
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoMapDerivedCategory h hh) _ ≪≫
    StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso (modulePullback h) j

/-- Derived pullback along a flat morphism carries a cohomology isomorphism to one. -/
theorem isIso_homologyMap_derivedPullback_map_of_isFlat (hh : AlgebraicGeometry.IsFlat h)
    {K L : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)}
    (g : K ⟶ L) (j : ℤ) (hg : IsIso ((DerivedCategory.homologyFunctor _ j).map g)) :
    IsIso ((DerivedCategory.homologyFunctor _ j).map ((derivedPullbackFunctor h).map g)) := by
  have hG : IsIso ((DerivedCategory.homologyFunctor
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) j ⋙ modulePullback h).map g) :=
    Iso.isIso_hom ((modulePullback h).mapIso (@asIso _ _ _ _ _ hg))
  exact (NatIso.isIso_map_iff (homologyDerivedPullbackIsoOfIsFlat h hh j) g).2 hG

/-- Derived pullback along a flat morphism preserves a vanishing of cohomology in a given
degree. -/
theorem isZero_homology_derivedPullback_obj_of_isFlat (hh : AlgebraicGeometry.IsFlat h)
    (K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) (j : ℤ)
    (hK : IsZero ((DerivedCategory.homologyFunctor _ j).obj K)) :
    IsZero ((DerivedCategory.homologyFunctor _ j).obj ((derivedPullbackFunctor h).obj K)) :=
  (Functor.map_isZero (modulePullback h) hK).of_iso
    ((homologyDerivedPullbackIsoOfIsFlat h hh j).app K)

/-- Derived pullback along a flat morphism preserves lower bounds on cohomology. -/
theorem isGE_derivedPullback_obj_of_isFlat (hh : AlgebraicGeometry.IsFlat h)
    (K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) (a : ℤ)
    (hK : K.IsGE a) : ((derivedPullbackFunctor h).obj K).IsGE a := by
  rw [DerivedCategory.isGE_iff] at hK ⊢
  exact fun i hi ↦ isZero_homology_derivedPullback_obj_of_isFlat h hh K i (hK i hi)

/-- Derived pullback along a flat morphism preserves upper bounds on cohomology. -/
theorem isLE_derivedPullback_obj_of_isFlat (hh : AlgebraicGeometry.IsFlat h)
    (K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) (n : ℤ)
    (hK : K.IsLE n) : ((derivedPullbackFunctor h).obj K).IsLE n := by
  rw [DerivedCategory.isLE_iff] at hK ⊢
  exact fun i hi ↦ isZero_homology_derivedPullback_obj_of_isFlat h hh K i (hK i hi)

/-- Let `h : X ⟶ Y` be a flat morphism of ringed spaces, let `A ⟶ K ⟶ C ⟶ A[1]` be a
distinguished triangle of `D(𝒪_Y)` with `C` bounded above by `n`, and let `M ∈ D(𝒪_Y)` be bounded
below by `a`. If the canonical map

`Lh^*R𝓗om(A, M) ⟶ R𝓗om(Lh^*A, Lh^*M)`

is invertible, then the canonical map at `K` is invertible on cohomology in every degree `j` with
`j + 1 < a - n`. -/
theorem isIso_homologyMap_derivedPullbackSheafHomMap_of_distTriang
    (hh : AlgebraicGeometry.IsFlat h)
    (T : Triangle (DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)))
    (hT : T ∈ distTriang _) (n : ℤ) (hC : T.obj₃.IsLE n)
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) (a : ℤ)
    (hM : M.IsGE a) (hA : IsIso (derivedPullbackSheafHomMap h T.obj₁ M)) (j : ℤ)
    (hj : j + 1 < a - n) :
    IsIso ((DerivedCategory.homologyFunctor _ j).map (derivedPullbackSheafHomMap h T.obj₂ M)) := by
  have sq := Transpose.homComparison_naturality_source (derivedPullbackFunctor h)
    (Stacks.SheafOfModules.derivedSheafHom Y.sheaf) (Stacks.SheafOfModules.derivedSheafHom X.sheaf)
    (internalHomTensorUncurried Y) (internalHomTensorUncurried X)
    (tensorHomEquiv Y) (tensorHomEquiv X)
    (pullbackTensorIso h)
    (tensorHomEquivNaturalLeft_ringedSpace Y) (tensorHomEquivDinatural_ringedSpace Y)
    (tensorHomEquivNaturalLeft_ringedSpace X) (tensorHomEquivDinatural_ringedSpace X) T.mor₁ M
  have hY := AlgebraicGeometry.RingedSite.isIso_homologyMap_derivedSheafHom_map_of_isLE₃
    (Stacks.SheafOfModules.ringedSite Y.sheaf) T hT n hC M a hM j hj
  let : (derivedPullbackFunctor h).CommShift ℤ :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift h
  have : (derivedPullbackFunctor h).IsTriangulated :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated h
  have hX := AlgebraicGeometry.RingedSite.isIso_homologyMap_derivedSheafHom_map_of_isLE₃
    (Stacks.SheafOfModules.ringedSite X.sheaf) ((derivedPullbackFunctor h).mapTriangle.obj T)
    ((derivedPullbackFunctor h).map_distinguished T hT) n
    (isLE_derivedPullback_obj_of_isFlat h hh T.obj₃ n hC) ((derivedPullbackFunctor h).obj M) a
    (isGE_derivedPullback_obj_of_isFlat h hh M a hM) j hj
  have hPY := isIso_homologyMap_derivedPullback_map_of_isFlat h hh _ j hY
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

/-- Let `h : X ⟶ Y` be a flat morphism of ringed spaces, let `α : P ⟶ E` be a morphism of
complexes of `𝒪_Y`-modules inducing isomorphisms on cohomology in degrees `> m` and a surjection
in degree `m`, and let `M ∈ D(𝒪_Y)` be bounded below by `a`. If the canonical map
`Lh^*R𝓗om(P, M) ⟶ R𝓗om(Lh^*P, Lh^*M)` is invertible, then the one at `E` is invertible on
cohomology in every degree `j < a - m`. -/
theorem isIso_homologyMap_derivedPullbackSheafHomMap_of_approximation
    (hh : AlgebraicGeometry.IsFlat h)
    {P E : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ}
    (α : P ⟶ E) (m : ℤ) (hiso : ∀ i : ℤ, m < i → IsIso (HomologicalComplex.homologyMap α i))
    (hepi : Epi (HomologicalComplex.homologyMap α m))
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) (a : ℤ)
    (hM : M.IsGE a) (hP : IsIso (derivedPullbackSheafHomMap h (DerivedCategory.Q.obj P) M))
    (j : ℤ) (hj : j < a - m) :
    IsIso ((DerivedCategory.homologyFunctor _ j).map
      (derivedPullbackSheafHomMap h (DerivedCategory.Q.obj E) M)) := by
  obtain ⟨Z, g, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle (DerivedCategory.Q.map α)
  have hC := DerivedCategory.isLE_three_of_homologyMap_mor₁ _ hT m
    (fun i hi ↦ (DerivedCategory.isIso_homologyFunctor_map_Q_map_iff α i).2 (hiso i hi))
    ((DerivedCategory.epi_homologyFunctor_map_Q_map_iff α m).2 hepi)
  exact isIso_homologyMap_derivedPullbackSheafHomMap_of_distTriang h hh _ hT (m - 1) hC M a hM hP j
    (by lia)

/-- A ring homomorphism that becomes flat after precomposition with an isomorphism is flat. -/
theorem flat_of_eq_comp {A A' C : CommRingCat.{u}} (w : A ⟶ A') [IsIso w] (g : A' ⟶ C)
    (f : A ⟶ C) (hf : f.hom.Flat) (h : f = w ≫ g) : g.hom.Flat := by
  have hg : g = inv w ≫ f := by rw [h, IsIso.inv_hom_id_assoc]
  rw [hg, CommRingCat.hom_comp]
  exact RingHom.Flat.comp (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)) hf

/-- The restriction of a flat morphism to an open subspace of its target is flat. -/
theorem isFlat_restrictedMorphism (hh : AlgebraicGeometry.IsFlat h) (V : TopologicalSpace.Opens Y) :
    AlgebraicGeometry.IsFlat (Stacks.Cohomology.HigherDirectImage.restrictedMorphism h V) := by
  intro x
  have e : (Stacks.Cohomology.HigherDirectImage.openSubspaceInclusion X
      (Stacks.Cohomology.HigherDirectImage.preimageOpen h V)).hom ≫ h.hom =
      (Stacks.Cohomology.HigherDirectImage.restrictedMorphism h V).hom ≫
        (Stacks.Cohomology.HigherDirectImage.openSubspaceInclusion Y V).hom :=
    congrArg (fun φ ↦ φ.hom)
      (Stacks.Cohomology.HigherDirectImage.restrictedMorphism_comp_openSubspaceInclusion h V)
  have hc := AlgebraicGeometry.PresheafedSpace.stalkMap.congr_hom _ _ e x
  rw [AlgebraicGeometry.PresheafedSpace.stalkMap.comp,
    AlgebraicGeometry.PresheafedSpace.stalkMap.comp] at hc
  have : IsIso ((Stacks.Cohomology.HigherDirectImage.openSubspaceInclusion X
      (Stacks.Cohomology.HigherDirectImage.preimageOpen h V)).hom.stalkMap x) :=
    AlgebraicGeometry.PresheafedSpace.ofRestrict_stalkMap_isIso X.toPresheafedSpace _ x
  have hι : IsIso ((Stacks.Cohomology.HigherDirectImage.openSubspaceInclusion Y V).hom.stalkMap
      (ConcreteCategory.hom (Stacks.Cohomology.HigherDirectImage.restrictedMorphism h V).hom.base
        x)) :=
    AlgebraicGeometry.PresheafedSpace.ofRestrict_stalkMap_isIso Y.toPresheafedSpace _ _
  have hf : ((h.hom.stalkMap _) ≫ (Stacks.Cohomology.HigherDirectImage.openSubspaceInclusion X
      (Stacks.Cohomology.HigherDirectImage.preimageOpen h V)).hom.stalkMap x).hom.Flat := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (hh _)
      (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))
  refine @flat_of_eq_comp _ _ _ _ ?_ _ _ hf (hc.trans (Category.assoc _ _ _).symm)
  have hE : ∀ {A B : CommRingCat.{u}} (p : A = B), IsIso (eqToHom p) :=
    fun p ↦ Iso.isIso_hom (eqToIso p)
  exact IsIso.comp_isIso' (hE _) hι

end Stacks.Cohomology.DerivedInternalHomPullback

end
