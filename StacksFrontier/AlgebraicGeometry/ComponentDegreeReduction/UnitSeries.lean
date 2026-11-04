module

public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksFrontier.AlgebraicGeometry.ComponentDegreeReduction.BiprodFiltration
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel

/-!
# The degree of a vector bundle on a curve as a sum over closed subschemes

Let `X` be proper over a field `k` of dimension at most one, let `iⱼ : Zⱼ ⟶ X` (`j < N`) be closed
immersions, and write `g : X' = ∐_{j < N} Zⱼ ⟶ X`. For a finite locally free `ℰ` on `X`,

`deg(ℰ) = ∑_{j < N} deg(ℰ|_{Zⱼ})`

as soon as the kernel and the cokernel of a map `𝒪_X ⟶ g_*𝒪_{X'}` have zero-dimensional
support. The two short exact sequences

`0 ⟶ 𝒦 ⟶ 𝒪_X ⟶ 𝒥 ⟶ 0`,  `0 ⟶ 𝒥 ⟶ g_*𝒪_{X'} ⟶ 𝒬 ⟶ 0`

of [Stacks, Tag 0AYU] are the kernel-image-cokernel factorisation of that map.

## Main definitions

The elided prefix is `AlgebraicGeometry`.

* `Scheme.Modules.biprodSeriesLift`: the map into the partial biproducts
  `𝒫ⱼ = ⨁_{l < j} 𝒢_l` of `AlgebraicGeometry.Scheme.Modules.biprodSeries` induced by a family of
  maps `𝒜 ⟶ 𝒢_l`.
* `Scheme.Modules.pushforwardUnitSeriesMap`: **the canonical map `𝒪_X ⟶ g_*𝒪_{X'}`**, whose
  components are the adjunction units `𝒪_X ⟶ (iⱼ)_*𝒪_{Zⱼ}`.

## Main results

* `CategoryTheory.ShortComplex.shortExact_kernel_factorThruImage` and
  `CategoryTheory.ShortComplex.shortExact_image_ι_cokernel_π`: in an abelian category, the two
  halves of the kernel-image-cokernel factorisation of a morphism are short exact.
* `Scheme.Modules.exists_shortExact_pair_pushforwardUnitSeries`: **the two short exact
  sequences of [Stacks, Tag 0AYU] exist at `g_*𝒪_{X'}`, with all five terms coherent.**
* `curveDegree_eq_sum_biprodSeries_of_supp_le_zero`: `deg(ℰ) = ∑_{j < N} deg(ℰ|_{Zⱼ})` for any
  map `𝒪_X ⟶ g_*𝒪_{X'}` whose kernel and cokernel have zero-dimensional support.
* `curveDegree_eq_sum_pushforwardUnitSeriesMap`: the same at the canonical map.
* `curveDegree_eq_sum_pushforwardUnitSeriesMap_of_supp_subset`: the same, with the two support
  bounds replaced by one zero-dimensional subset containing both supports.

## References

* [Stacks Project, Tag 0AYW](https://stacks.math.columbia.edu/tag/0AYW)
* [Stacks Project, Tag 0AYU](https://stacks.math.columbia.edu/tag/0AYU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace CategoryTheory.Limits
open scoped ZeroObject

universe u

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category C] [Abelian C] {A B : C}

/-- **The kernel of a morphism annihilates the map to its image.** -/
theorem kernel_ι_comp_factorThruImage (φ : A ⟶ B) :
    kernel.ι φ ≫ Abelian.factorThruImage φ = 0 :=
  (cancel_mono (Abelian.image.ι φ)).1 (by simp)

/-- **The inclusion of the image is annihilated by the projection to the cokernel.** -/
theorem image_ι_comp_cokernel_π (φ : A ⟶ B) :
    Abelian.image.ι φ ≫ cokernel.π φ = 0 :=
  kernel.condition (cokernel.π φ)

/-- **The first half of the kernel-image-cokernel factorisation is short exact**:
`0 ⟶ ker φ ⟶ A ⟶ im φ ⟶ 0`. -/
theorem shortExact_kernel_factorThruImage (φ : A ⟶ B)
    (w : kernel.ι φ ≫ Abelian.factorThruImage φ = 0) :
    (ShortComplex.mk (kernel.ι φ) (Abelian.factorThruImage φ) w).ShortExact where
  exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk (kernel.ι φ) (Abelian.factorThruImage φ) w)
      (S₂ := ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ))
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := Abelian.image.ι φ
        comm₁₂ := by simp
        comm₂₃ := by simp }).2
      (ShortComplex.exact_kernel φ)
  mono_f := inferInstanceAs (Mono (kernel.ι φ))
  epi_g := inferInstanceAs (Epi (Abelian.factorThruImage φ))

/-- **The second half of the kernel-image-cokernel factorisation is short exact**:
`0 ⟶ im φ ⟶ B ⟶ coker φ ⟶ 0`. -/
theorem shortExact_image_ι_cokernel_π (φ : A ⟶ B)
    (w : Abelian.image.ι φ ≫ cokernel.π φ = 0) :
    (ShortComplex.mk (Abelian.image.ι φ) (cokernel.π φ) w).ShortExact where
  exact := ShortComplex.exact_kernel (cokernel.π φ)
  mono_f := inferInstanceAs (Mono (kernel.ι (cokernel.π φ)))
  epi_g := inferInstanceAs (Epi (cokernel.π φ))

end CategoryTheory.ShortComplex

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The universal map into the partial biproducts -/

/-- **The universal map into the partial biproducts
`𝒫ⱼ = ⨁_{l < j} 𝒢_l`** of `AlgebraicGeometry.Scheme.Modules.biprodSeries`, from a family of
maps `uⱼ : 𝒜 ⟶ 𝒢ⱼ`: the zero map at `j = 0` and `biprod.lift` of the previous stage with `uⱼ`
at `j + 1`. -/
noncomputable def Scheme.Modules.biprodSeriesLift (G : ℕ → X.Modules) (A : X.Modules)
    (u : ∀ j, A ⟶ G j) : ∀ j, A ⟶ Scheme.Modules.biprodSeries G j
  | 0 => 0
  | (j + 1) =>
    show A ⟶ Scheme.Modules.biprodSeries G j ⊞ G j from
      biprod.lift (Scheme.Modules.biprodSeriesLift G A u j) (u j)

/-- **The new component of the lift at stage `j + 1` is `uⱼ`.** -/
theorem Scheme.Modules.biprodSeriesLift_comp_biprod_snd (G : ℕ → X.Modules) (A : X.Modules)
    (u : ∀ j, A ⟶ G j) (j : ℕ) :
    (show A ⟶ Scheme.Modules.biprodSeries G j ⊞ G j from
      Scheme.Modules.biprodSeriesLift G A u (j + 1)) ≫ biprod.snd = u j :=
  biprod.lift_snd _ _

/-- **The old components of the lift at stage `j + 1` are the lift at stage `j`.** -/
theorem Scheme.Modules.biprodSeriesLift_comp_biprod_fst (G : ℕ → X.Modules) (A : X.Modules)
    (u : ∀ j, A ⟶ G j) (j : ℕ) :
    (show A ⟶ Scheme.Modules.biprodSeries G j ⊞ G j from
      Scheme.Modules.biprodSeriesLift G A u (j + 1)) ≫ biprod.fst =
      Scheme.Modules.biprodSeriesLift G A u j :=
  biprod.lift_fst _ _

/-! ### The canonical map `𝒪_X ⟶ g_*𝒪_{X'}` -/

/-- **The canonical map `𝒪_X ⟶ g_*𝒪_{X'}` for `X' = ∐_{j < N} Zⱼ ⟶ X`**, whose `j`-th
component is the adjunction unit `𝒪_X ⟶ (iⱼ)_*𝒪_{Zⱼ}` of
`SheafOfModules.unitToPushforwardObjUnit`. -/
noncomputable def Scheme.Modules.pushforwardUnitSeriesMap {Zs : ℕ → Scheme.{u}}
    (i : ∀ j, Zs j ⟶ X) (N : ℕ) :
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      Scheme.Modules.pushforwardUnitSeries i N :=
  Scheme.Modules.biprodSeriesLift _ _
    (fun j => SheafOfModules.unitToPushforwardObjUnit (i j).toRingCatSheafHom) N

/-- **The `j`-th component of the canonical map is the adjunction unit
`𝒪_X ⟶ (iⱼ)_*𝒪_{Zⱼ}`.** -/
theorem Scheme.Modules.pushforwardUnitSeriesMap_comp_biprod_snd {Zs : ℕ → Scheme.{u}}
    (i : ∀ j, Zs j ⟶ X) (j : ℕ) :
    (show (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
        Scheme.Modules.pushforwardUnitSeries i j ⊞
          (Scheme.Modules.pushforward (i j)).obj (SheafOfModules.unit (Zs j).ringCatSheaf) from
      Scheme.Modules.pushforwardUnitSeriesMap i (j + 1)) ≫ biprod.snd =
      SheafOfModules.unitToPushforwardObjUnit (i j).toRingCatSheafHom :=
  biprod.lift_snd _ _

/-! ### The two [Stacks, Tag 0AYU] sequences at `g_*𝒪_{X'}` -/

/-- The kernel and cokernel of a map `𝒪_X ⟶ g_*𝒪_{X'}`, and the kernel of the projection to the
cokernel, are coherent. -/
private theorem isCoherent_kernel_cokernel_of_pushforwardUnitSeries [IsLocallyNoetherian X]
    {Zs : ℕ → Scheme.{u}} (i : ∀ j, Zs j ⟶ X) [∀ j, IsClosedImmersion (i j)] (N : ℕ)
    (φ : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      Scheme.Modules.pushforwardUnitSeries i N) :
    SheafOfModules.IsCoherent (kernel φ) ∧
      SheafOfModules.IsCoherent (kernel (cokernel.π φ)) ∧ SheafOfModules.IsCoherent (cokernel φ) :=
  have hOX : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  have hP : SheafOfModules.IsCoherent (Scheme.Modules.pushforwardUnitSeries i N) :=
    SheafOfModules.isCoherent_biprodSeries _
      (fun j => @isCoherent_pushforward_of_isClosedImmersion _ X (i j) _ _ _
        (@Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent _
          (isLocallyNoetherian_of_isClosedImmersion (i j)))) N
  have hQ : SheafOfModules.IsCoherent (cokernel φ) :=
    @SheafOfModules.cokernel_isCoherent _ _ _ _ _ hOX hP φ
  ⟨@SheafOfModules.kernel_isCoherent _ _ _ _ _ hOX hP φ,
    @SheafOfModules.kernel_isCoherent _ _ _ _ _ hP hQ (cokernel.π φ), hQ⟩

/-- **The two short exact sequences of [Stacks, Tag 0AYU] exist at
`g_*𝒪_{X'} = ` `AlgebraicGeometry.Scheme.Modules.pushforwardUnitSeries i N`, with all five
terms coherent**: there are coherent `𝒦`, `𝒥`, `𝒬` and maps fitting into

`0 ⟶ 𝒦 ⟶ 𝒪_X ⟶ 𝒥 ⟶ 0`,  `0 ⟶ 𝒥 ⟶ g_*𝒪_{X'} ⟶ 𝒬 ⟶ 0`. -/
theorem Scheme.Modules.exists_shortExact_pair_pushforwardUnitSeries [IsLocallyNoetherian X]
    {Zs : ℕ → Scheme.{u}} (i : ∀ j, Zs j ⟶ X) [∀ j, IsClosedImmersion (i j)] (N : ℕ) :
    ∃ (Kr J Q : X.Modules) (_ : SheafOfModules.IsCoherent Kr)
      (_ : SheafOfModules.IsCoherent J) (_ : SheafOfModules.IsCoherent Q)
      (a : Kr ⟶ SheafOfModules.unit X.ringCatSheaf)
      (b : SheafOfModules.unit X.ringCatSheaf ⟶ J) (wab : a ≫ b = 0)
      (_ : (ShortComplex.mk a b wab).ShortExact)
      (c : J ⟶ Scheme.Modules.pushforwardUnitSeries i N)
      (d : Scheme.Modules.pushforwardUnitSeries i N ⟶ Q) (wcd : c ≫ d = 0),
      (ShortComplex.mk c d wcd).ShortExact :=
  have h := isCoherent_kernel_cokernel_of_pushforwardUnitSeries i N
    (Scheme.Modules.pushforwardUnitSeriesMap i N)
  ⟨kernel (Scheme.Modules.pushforwardUnitSeriesMap i N),
    Abelian.image (Scheme.Modules.pushforwardUnitSeriesMap i N),
    cokernel (Scheme.Modules.pushforwardUnitSeriesMap i N), h.1, h.2.1, h.2.2,
    kernel.ι (Scheme.Modules.pushforwardUnitSeriesMap i N),
    Abelian.factorThruImage (Scheme.Modules.pushforwardUnitSeriesMap i N),
    ShortComplex.kernel_ι_comp_factorThruImage _,
    ShortComplex.shortExact_kernel_factorThruImage _
      (ShortComplex.kernel_ι_comp_factorThruImage _),
    Abelian.image.ι (Scheme.Modules.pushforwardUnitSeriesMap i N),
    cokernel.π (Scheme.Modules.pushforwardUnitSeriesMap i N),
    ShortComplex.image_ι_comp_cokernel_π _,
    ShortComplex.shortExact_image_ι_cokernel_π _ (ShortComplex.image_ι_comp_cokernel_π _)⟩

/-! ### The degree as a sum over the closed subschemes -/

/-- **The degree of `ℰ` is the sum of the degrees of its restrictions to the `Zⱼ`**:
`deg(ℰ) = ∑_{j < N} deg(ℰ|_{Zⱼ})`, for `ℰ` finite locally free of rank `n` on `X` proper over `k`
of dimension at most one, closed immersions `iⱼ : Zⱼ ⟶ X`, and a map `φ : 𝒪_X ⟶ g_*𝒪_{X'}`
whose kernel and cokernel have zero-dimensional support, given that coherent modules on `X` have
finite-dimensional cohomology ([Stacks, Tag 02O6]). -/
theorem curveDegree_eq_sum_biprodSeries_of_supp_le_zero
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] {Zs : ℕ → Scheme.{u}}
    (i : ∀ j, Zs j ⟶ X) [∀ j, IsClosedImmersion (i j)]
    (hX : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n] (N : ℕ)
    (φ : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      Scheme.Modules.pushforwardUnitSeries i N)
    (hsuppKernel : topologicalKrullDim (_root_.SheafOfModules.supp (kernel φ)) ≤ 0)
    (hsuppCokernel : topologicalKrullDim (_root_.SheafOfModules.supp (cokernel φ)) ≤ 0)
    (h02O6 : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (cohomologyOverField k f G m)) :
    curveDegree k f hX E n =
      ∑ j ∈ Finset.range N, @curveDegree k _ (Zs j) (i j ≫ f) _
        (le_trans (IsClosedImmersion.isClosedEmbedding
          (i j)).isInducing.topologicalKrullDim_le hX)
        ((Scheme.Modules.pullback (i j)).obj E) n
        (isFiniteLocallyFreeOfRank_pullback (i j) E n) :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have h := isCoherent_kernel_cokernel_of_pushforwardUnitSeries i N φ
  curveDegree_eq_sum_biprodSeries_of_topologicalKrullDim_supp_le_zero k f i hX E n
    (kernel φ) (Abelian.image φ) (cokernel φ) h.1 h.2.1 h.2.2 N
    hsuppKernel hsuppCokernel
    (kernel.ι φ) (Abelian.factorThruImage φ)
    (ShortComplex.kernel_ι_comp_factorThruImage φ)
    (ShortComplex.shortExact_kernel_factorThruImage φ
      (ShortComplex.kernel_ι_comp_factorThruImage φ))
    (Abelian.image.ι φ) (cokernel.π φ) (ShortComplex.image_ι_comp_cokernel_π φ)
    (ShortComplex.shortExact_image_ι_cokernel_π φ (ShortComplex.image_ι_comp_cokernel_π φ))
    h02O6

/-- **The degree of `ℰ` as a sum over the `Zⱼ`, at the canonical map**:
`deg(ℰ) = ∑_{j < N} deg(ℰ|_{Zⱼ})`, for `ℰ` finite locally free of rank `n` on `X` proper over
`k` of dimension at most one and closed immersions `iⱼ : Zⱼ ⟶ X`, as soon as the kernel and the
cokernel of the canonical map `𝒪_X ⟶ g_*𝒪_{X'}` have zero-dimensional support, given that
coherent modules on `X` have finite-dimensional cohomology ([Stacks, Tag 02O6]). -/
theorem curveDegree_eq_sum_pushforwardUnitSeriesMap
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] {Zs : ℕ → Scheme.{u}}
    (i : ∀ j, Zs j ⟶ X) [∀ j, IsClosedImmersion (i j)]
    (hX : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n] (N : ℕ)
    (hsuppKernel : topologicalKrullDim (_root_.SheafOfModules.supp
      (kernel (Scheme.Modules.pushforwardUnitSeriesMap i N))) ≤ 0)
    (hsuppCokernel : topologicalKrullDim (_root_.SheafOfModules.supp
      (cokernel (Scheme.Modules.pushforwardUnitSeriesMap i N))) ≤ 0)
    (h02O6 : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (cohomologyOverField k f G m)) :
    curveDegree k f hX E n =
      ∑ j ∈ Finset.range N, @curveDegree k _ (Zs j) (i j ≫ f) _
        (le_trans (IsClosedImmersion.isClosedEmbedding
          (i j)).isInducing.topologicalKrullDim_le hX)
        ((Scheme.Modules.pullback (i j)).obj E) n
        (isFiniteLocallyFreeOfRank_pullback (i j) E n) :=
  curveDegree_eq_sum_biprodSeries_of_supp_le_zero k f i hX E n N
    (Scheme.Modules.pushforwardUnitSeriesMap i N) hsuppKernel hsuppCokernel h02O6

/-- **The degree of `ℰ` as a sum over the `Zⱼ`, from one zero-dimensional subset containing both
supports**: `deg(ℰ) = ∑_{j < N} deg(ℰ|_{Zⱼ})` as soon as the supports of the kernel and the
cokernel of the canonical map `𝒪_X ⟶ g_*𝒪_{X'}` lie in a subset `Z` of `X` of dimension at most
`0`, given that coherent modules on `X` have finite-dimensional cohomology
([Stacks, Tag 02O6]). -/
theorem curveDegree_eq_sum_pushforwardUnitSeriesMap_of_supp_subset
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] {Zs : ℕ → Scheme.{u}}
    (i : ∀ j, Zs j ⟶ X) [∀ j, IsClosedImmersion (i j)]
    (hX : topologicalKrullDim X ≤ 1)
    (E : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n] (N : ℕ)
    (Z : Set X) (hZ : topologicalKrullDim Z ≤ 0)
    (hsuppKernel : _root_.SheafOfModules.supp
      (kernel (Scheme.Modules.pushforwardUnitSeriesMap i N)) ⊆ Z)
    (hsuppCokernel : _root_.SheafOfModules.supp
      (cokernel (Scheme.Modules.pushforwardUnitSeriesMap i N)) ⊆ Z)
    (h02O6 : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ m, FiniteDimensional k (cohomologyOverField k f G m)) :
    curveDegree k f hX E n =
      ∑ j ∈ Finset.range N, @curveDegree k _ (Zs j) (i j ≫ f) _
        (le_trans (IsClosedImmersion.isClosedEmbedding
          (i j)).isInducing.topologicalKrullDim_le hX)
        ((Scheme.Modules.pullback (i j)).obj E) n
        (isFiniteLocallyFreeOfRank_pullback (i j) E n) :=
  curveDegree_eq_sum_pushforwardUnitSeriesMap k f i hX E n N
    (le_trans (topologicalKrullDim_le_of_subset hsuppKernel) hZ)
    (le_trans (topologicalKrullDim_le_of_subset hsuppCokernel) hZ) h02O6

end AlgebraicGeometry

end
