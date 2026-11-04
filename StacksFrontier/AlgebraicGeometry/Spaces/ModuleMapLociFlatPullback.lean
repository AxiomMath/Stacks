module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSupportBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatReflection
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportProperties
public import StacksCore.Tactic.StacksAttribute

/-!
# The base-change loci of a map of modules under a flat pullback of the source space

In the situation of Stacks 083F — a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
and a map `u : ℱ ⟶ 𝒢` of quasi-coherent `𝒪_X`-modules — let `g : X' ⟶ X` be a morphism of
algebraic spaces and let `u' : ℱ' ⟶ 𝒢'` be the inverse image of `u` on `X'`, a situation of
Stacks 083F for the composite `X' ⟶ X ⟶ Y` and hence with the same test schemes over `Y`.  At a
test scheme `T` the two base-change spaces are compared by `X' ×_Y T ⟶ X ×_Y T`, and the base
change of `u'` to `T` is the inverse image of the base change of `u` along that comparison, up
to the composition comparisons of the inverse image.

**Stacks 083I** compares the four base-change loci of `u` with those of `u'` when `g` is flat:

1. if `𝒢` is of finite type and the image of `|X'| ⟶ |X|` contains the support of `𝒢`, then
   `F_surj = F'_surj` and `F_zero = F'_zero`;
2. if `ℱ` is of finite type and the image of `|X'| ⟶ |X|` contains the support of `ℱ`, then
   `F_inj = F'_inj` and `F_zero = F'_zero`;
3. if `ℱ` and `𝒢` are of finite type and the image of `|X'| ⟶ |X|` contains the supports of
   both, then `F_iso = F'_iso`.

All three rest on one global statement: for a flat morphism `φ : Z' ⟶ Z` of algebraic spaces
and a map `v : M ⟶ N` of `𝒪_Z`-modules, the inverse image `φ^*v` is surjective, injective, zero
or an isomorphism exactly when `v` is, as soon as the image of `|Z'| ⟶ |Z|` contains the support
of the relevant module.  Surjectivity of `v` is emptiness of the support of its cokernel,
injectivity is emptiness of the support of its kernel, and along a flat morphism the support of
an inverse image is the inverse image of the support; the support containment then lets the
emptiness be tested after pulling back.

## Main results

* `AlgebraicGeometry.Space.nontrivial_geometricModuleStalk_iff_mem_supportOfSheaf`: a point lies
  in the support of an `𝒪_Z`-module exactly when the stalk at *any one* geometric point above it
  is nonzero.
* `AlgebraicGeometry.Space.supportOfSheaf_modulePullback_eq_preimage_of_isFlat`: for a flat
  morphism the support of an inverse image of modules is the inverse image of the support.
* `AlgebraicGeometry.Space.epi_modulePullback_map_iff_of_isFlat`,
  `.mono_modulePullback_map_iff_of_isFlat`,
  `.modulePullback_map_eq_zero_iff_of_isFlat`,
  `.modulePullback_map_eq_zero_iff_of_isFlat'` and
  `.isIso_modulePullback_map_iff_of_isFlat`: the global statement, clause by clause.
* `AlgebraicGeometry.Space.epi_of_forall_epi_modulePullback_map_of_isFlat` and its three
  companions: the same conclusions for a jointly surjective family of flat morphisms, where no
  support hypothesis is needed.
* `AlgebraicGeometry.Space.ModuleMapSituation.mono_pullbackBaseChangeMap_map_iff`,
  `.epi_pullbackBaseChangeMap_map_iff`, `.isIso_pullbackBaseChangeMap_map_iff` and
  `.pullbackBaseChangeMap_map_eq_zero_iff`: the four conditions for the inverse image of `u_T`
  along the comparison of base changes agree with those for `u'_T`.
* `AlgebraicGeometry.Space.ModuleMapSituation.mono_baseChangeMap_map_iff`,
  `.epi_baseChangeMap_map_iff`, `.isIso_baseChangeMap_map_iff` and
  `.baseChangeMap_map_eq_zero_iff`: the same four conditions for the inverse image of `u_T`
  along the comparison of base changes over a morphism of test schemes.
* `AlgebraicGeometry.Space.ModuleMapSituation.surjFunctor_and_zeroFunctor_pullbackSituation_eq`,
  `.injFunctor_and_zeroFunctor_pullbackSituation_eq` and `.isoFunctor_pullbackSituation_eq`:
  the three parts of Stacks 083I for `pullbackSituation`; the statements over the situation
  `inverseImageSituation`, whose quasi-coherence comes from Stacks 03GA, are in
  `StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapInverseImageLoci`.

## Implementation notes

Everything is at the module universe of the structure rings, as the library's Stacks 0CVM is,
because that is the universe at which the support of a module, the inverse image of modules and
its exactness along a flat morphism all meet.

The two quasi-coherence hypotheses on the inverse images of `ℱ` and `𝒢` are what
`AlgebraicGeometry.Space.ModuleMapSituation.pullbackSituation` consumes, so they appear on each
of the three parts; they are discharged by Stacks 03GA in
`StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapInverseImageLoci`, which registers Stacks 083I
again over `inverseImageSituation` with exactly the hypotheses of the source.

The comparison of the two base changes is conjugated to the inverse image of the base-changed
map by the composition comparison of the inverse image, so each of the four conditions
transports across an isomorphism of the source and an isomorphism of the target; the four
elementary lemmas doing that are kept private.

## References

* [Stacks Project, Tag 083I](https://stacks.math.columbia.edu/tag/083I)
* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04K4](https://stacks.math.columbia.edu/tag/04K4)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Transport of the four conditions across isomorphisms -/

section Conjugation

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {W X Y Z : C}

/-- Monomorphy is unchanged by composing with an isomorphism on either side. -/
private theorem mono_conj_iff (a : W ⟶ X) (b : Y ⟶ Z) [IsIso a] [IsIso b] (x : X ⟶ Y) :
    Mono (a ≫ x ≫ b) ↔ Mono x := by
  simp

/-- Epimorphy is unchanged by composing with an isomorphism on either side. -/
private theorem epi_conj_iff (a : W ⟶ X) (b : Y ⟶ Z) [IsIso a] [IsIso b] (x : X ⟶ Y) :
    Epi (a ≫ x ≫ b) ↔ Epi x := by
  simp

/-- Being an isomorphism is unchanged by composing with an isomorphism on either side. -/
private theorem isIso_conj_iff (a : W ⟶ X) (b : Y ⟶ Z) [IsIso a] [IsIso b] (x : X ⟶ Y) :
    IsIso (a ≫ x ≫ b) ↔ IsIso x := by
  simp

/-- Vanishing is unchanged by composing with an isomorphism on either side. -/
private theorem eq_zero_conj_iff [HasZeroMorphisms C] (a : W ⟶ X) (b : Y ⟶ Z) [IsIso a]
    [IsIso b] (x : X ⟶ Y) : a ≫ x ≫ b = 0 ↔ x = 0 := by
  rw [comp_eq_zero_iff_of_epi, ← cancel_mono b, zero_comp]

end Conjugation

attribute [local instance 10000] smallEtaleModulesAbelian

/-! ### The support of a module against the stalk at one geometric point -/

section Support

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

universe m

/-- **The support of an `𝒪_Z`-module is detected by every geometric point above a point.**  A
point `z` of an algebraic space `Z` lies in the support of an `𝒪_Z`-module `F` exactly when the
stalk of `F` at one given geometric point above `z` is nonzero.

The support of Stacks 04KA is defined by nonvanishing of the stalk at *some* geometric point
above `z`, and the passage from "some" to "any" is Stacks 04K4: the set-valued stalk functors at
two geometric points above one point are isomorphic. -/
theorem nontrivial_geometricModuleStalk_iff_mem_supportOfSheaf (Z : AlgebraicSpaces B S hS)
    (F : Modules.{u, m} B S hS Z.1 Z.2) (zbar : GeometricPoint B S hS Z.1)
    (z : points B S hS Z.1) (hz : zbar.LiesOver z) :
    Nontrivial (geometricModuleStalk B S hS Z zbar F) ↔
      z ∈ supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj F) := by
  refine ⟨fun h =>
    (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS Z F z).2 ⟨zbar, hz, h⟩,
    fun hmem => ?_⟩
  by_contra hc
  rw [not_nontrivial_iff_subsingleton] at hc
  refine notMem_supportOfSheaf_of_subsingleton_stalkSet B S hS Z _ z zbar hz ?_ hmem
  refine (subsingleton_stalkSet_iff B S hS Z.1 Z.2 _ zbar).2 fun N s => ?_
  exact (geometricModuleStalkGerm_eq_zero_iff_mem_largestOpenZeroLocus B S hS Z F zbar N s).1
    (@Subsingleton.elim _ hc _ _)

variable {Z' Z : AlgebraicSpaces B S hS}

/-- **The support of a flat inverse image of modules is the inverse image of the support.**  For
a flat morphism `φ : Z' ⟶ Z` of algebraic spaces and an `𝒪_Z`-module `W`,

`Supp(φ^* W) = |φ|^{-1}(Supp W)`.

One inclusion holds for every morphism.  For the other, a point of `Z'` is represented by a
geometric point `z̄`, the stalk of `W` at the image geometric point is nonzero because the image
point lies in the support, and the stalk of `φ^* W` at `z̄` is its base change along the
homomorphism of étale local rings of Stacks 03MK, which is faithfully flat. -/
theorem supportOfSheaf_modulePullback_eq_preimage_of_isFlat (φ : Z' ⟶ Z)
    (hφ : IsFlat B S hS φ.hom) (W : Modules.{u, u} B S hS Z.1 Z.2) :
    supportOfSheaf B S hS Z'.1
        ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS φ).obj W)) =
      pointsMap B S hS Z'.1 φ.hom ⁻¹'
        supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj W) := by
  refine Set.Subset.antisymm (supportOfSheaf_modulePullback_subset_preimage B S hS φ W)
    fun z hz => ?_
  obtain ⟨zbar, hzbar⟩ := exists_geometricRepresentative B S hS Z'.1 z
  have hnt : Nontrivial (geometricModuleStalk B S hS Z (geometricPointMap φ.hom zbar) W) :=
    (nontrivial_geometricModuleStalk_iff_mem_supportOfSheaf B S hS Z W
      (geometricPointMap φ.hom zbar) (pointsMap B S hS Z'.1 φ.hom z)
      ((geometricPointMap_image φ.hom zbar).trans (congrArg _ hzbar))).2 hz
  refine (mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS Z' _ z).2
    ⟨zbar, hzbar, ?_⟩
  exact (Equiv.ofBijective _ (ConcreteCategory.bijective_of_isIso
      (geometricModuleStalkPullbackIso B S hS φ zbar W).hom)).nontrivial_congr.2
    (nontrivial_extendScalars_of_faithfullyFlat
      (faithfullyFlat_etaleLocalRingMap B S hS Z'.2 Z.2 φ.hom hφ zbar) _)

end Support

/-! ### The four conditions along a flat morphism

Surjectivity of a map of `𝒪_Z`-modules is emptiness of the support of its cokernel and
injectivity is emptiness of the support of its kernel.  The inverse image of modules preserves
cokernels, being a left adjoint, and preserves kernels along a flat morphism; so each of the two
conditions for the inverse image of a map is emptiness of the inverse image of a support, which
by the support containment is emptiness of the support itself. -/

section FlatReflection

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z' Z : AlgebraicSpaces B S hS}

/-- A set contained in the range of a map is empty exactly when its inverse image is. -/
private theorem preimage_eq_empty_iff_of_subset_range {α β : Type*} (f : α → β) {T : Set β}
    (hT : T ⊆ Set.range f) : f ⁻¹' T = ∅ ↔ T = ∅ :=
  ⟨Set.eq_empty_of_subset_range_of_preimage_eq_empty hT, fun h => by simp [h]⟩

variable {M N : Modules.{u, u} B S hS Z.1 Z.2}

/-- A map of `𝒪_Z`-modules is an epimorphism exactly when the support of its cokernel is
empty. -/
private theorem epi_iff_supportOfSheaf_cokernel_eq_empty (v : M ⟶ N) :
    Epi v ↔ supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj
      (cokernel v : Modules.{u, u} B S hS Z.1 Z.2)) = ∅ := by
  rw [supportOfSheaf_eq_empty_iff_isZero, Preadditive.epi_iff_isZero_cokernel]

/-- A map of `𝒪_Z`-modules is a monomorphism exactly when the support of its kernel is empty. -/
private theorem mono_iff_supportOfSheaf_kernel_eq_empty (v : M ⟶ N) :
    Mono v ↔ supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj
      (kernel v : Modules.{u, u} B S hS Z.1 Z.2)) = ∅ := by
  rw [supportOfSheaf_eq_empty_iff_isZero, Preadditive.mono_iff_isZero_kernel]

/-- A map of `𝒪_Z`-modules vanishes exactly when the inclusion of its kernel is an
epimorphism. -/
private theorem eq_zero_iff_epi_kernel_ι (v : M ⟶ N) : v = 0 ↔ Epi (kernel.ι v) :=
  ⟨by rintro rfl; exact IsIso.epi_of_iso _, fun _ => eq_zero_of_epi_kernel v⟩

/-- A map of `𝒪_Z`-modules vanishes exactly when the projection to its cokernel is a
monomorphism. -/
private theorem eq_zero_iff_mono_cokernel_π (v : M ⟶ N) : v = 0 ↔ Mono (cokernel.π v) :=
  ⟨by rintro rfl; exact IsIso.mono_of_iso _, fun _ => eq_zero_of_mono_cokernel v⟩

/-- The inverse image of modules carries the cokernel of a map to the cokernel of its inverse
image, being a left adjoint, so the two supports agree. -/
private theorem supportOfSheaf_cokernel_modulePullback_map (φ : Z' ⟶ Z) (v : M ⟶ N) :
    supportOfSheaf B S hS Z'.1 ((SheafOfModules.toSheaf _).obj
        (cokernel ((modulePullback B S hS φ).map v) :
          Modules.{u, u} B S hS Z'.1 Z'.2)) =
      supportOfSheaf B S hS Z'.1 ((SheafOfModules.toSheaf _).obj
        ((modulePullback B S hS φ).obj (cokernel v : Modules.{u, u} B S hS Z.1 Z.2))) := by
  have hadj := modulePullbackAdjunction B S hS φ
  have := hadj.isLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS φ) :=
    hadj.leftAdjoint_preservesColimits
  exact supportOfSheaf_eq_of_iso B S hS Z'
    (PreservesCokernel.iso (modulePullback B S hS φ) v).symm

/-- The inverse image of modules along a flat morphism carries the kernel of a map to the kernel
of its inverse image, so the two supports agree. -/
private theorem supportOfSheaf_kernel_modulePullback_map (φ : Z' ⟶ Z)
    (hφ : IsFlat B S hS φ.hom) (v : M ⟶ N) :
    supportOfSheaf B S hS Z'.1 ((SheafOfModules.toSheaf _).obj
        (kernel ((modulePullback B S hS φ).map v) : Modules.{u, u} B S hS Z'.1 Z'.2)) =
      supportOfSheaf B S hS Z'.1 ((SheafOfModules.toSheaf _).obj
        ((modulePullback B S hS φ).obj (kernel v : Modules.{u, u} B S hS Z.1 Z.2))) := by
  have := (modulePullbackAdjunction B S hS φ).isLeftAdjoint
  have := preservesKernel_modulePullback_of_isFlat B S hS φ hφ v
  exact supportOfSheaf_eq_of_iso B S hS Z'
    (PreservesKernel.iso (modulePullback B S hS φ) v).symm

/-- **Surjectivity descends along a flat morphism whose image contains the support of the
target.**  For a flat morphism `φ : Z' ⟶ Z` of algebraic spaces and a map `v : M ⟶ N` of
`𝒪_Z`-modules with the support of `N` contained in the image of `|Z'| ⟶ |Z|`, the inverse image
`φ^*v` is an epimorphism exactly when `v` is.

Surjectivity of `v` is emptiness of the support of its cokernel, which lies in the support of
`N`; the inverse image preserves cokernels and turns that support into its inverse image under
`|φ|`, which is empty exactly when the support itself is. -/
theorem epi_modulePullback_map_iff_of_isFlat (φ : Z' ⟶ Z) (hφ : IsFlat B S hS φ.hom)
    (v : M ⟶ N)
    (hsupp : supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj N) ⊆
      Set.range (pointsMap B S hS Z'.1 φ.hom)) :
    Epi ((modulePullback B S hS φ).map v) ↔ Epi v := by
  rw [epi_iff_supportOfSheaf_cokernel_eq_empty, epi_iff_supportOfSheaf_cokernel_eq_empty,
    supportOfSheaf_cokernel_modulePullback_map B S hS φ v,
    supportOfSheaf_modulePullback_eq_preimage_of_isFlat B S hS φ hφ]
  exact preimage_eq_empty_iff_of_subset_range _
    ((supportOfSheaf_cokernel_subset B S hS Z v).trans hsupp)

/-- **Injectivity descends along a flat morphism whose image contains the support of the
source.**  For a flat morphism `φ : Z' ⟶ Z` of algebraic spaces and a map `v : M ⟶ N` of
`𝒪_Z`-modules with the support of `M` contained in the image of `|Z'| ⟶ |Z|`, the inverse image
`φ^*v` is a monomorphism exactly when `v` is.

Injectivity of `v` is emptiness of the support of its kernel, which lies in the support of `M`;
the inverse image along a flat morphism preserves kernels and turns that support into its
inverse image under `|φ|`, which is empty exactly when the support itself is. -/
theorem mono_modulePullback_map_iff_of_isFlat (φ : Z' ⟶ Z) (hφ : IsFlat B S hS φ.hom)
    (v : M ⟶ N)
    (hsupp : supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj M) ⊆
      Set.range (pointsMap B S hS Z'.1 φ.hom)) :
    Mono ((modulePullback B S hS φ).map v) ↔ Mono v := by
  rw [mono_iff_supportOfSheaf_kernel_eq_empty, mono_iff_supportOfSheaf_kernel_eq_empty,
    supportOfSheaf_kernel_modulePullback_map B S hS φ hφ v,
    supportOfSheaf_modulePullback_eq_preimage_of_isFlat B S hS φ hφ]
  exact preimage_eq_empty_iff_of_subset_range _
    ((supportOfSheaf_kernel_subset B S hS Z v).trans hsupp)

/-- For a flat morphism `φ : Z' ⟶ Z` of algebraic spaces and a map `v : M ⟶ N` of `𝒪_Z`-modules,
the inverse image `φ^*v` is zero exactly when the inverse image of the inclusion of the kernel of
`v` is an epimorphism. -/
private theorem modulePullback_map_eq_zero_iff_epi_modulePullback_map_kernel_ι (φ : Z' ⟶ Z)
    (hφ : IsFlat B S hS φ.hom) (v : M ⟶ N) :
    (modulePullback B S hS φ).map v = 0 ↔
      Epi ((modulePullback B S hS φ).map (kernel.ι v)) := by
  have := (modulePullbackAdjunction B S hS φ).isLeftAdjoint
  have := preservesKernel_modulePullback_of_isFlat B S hS φ hφ v
  have hι : (modulePullback B S hS φ).map (kernel.ι v) =
      (PreservesKernel.iso (modulePullback B S hS φ) v).hom ≫
        kernel.ι ((modulePullback B S hS φ).map v) :=
    (kernelComparison_comp_ι v (modulePullback B S hS φ)).symm
  rw [eq_zero_iff_epi_kernel_ι, hι]
  exact (@epi_comp_iff_of_epi _ _ _ _ _ _ (IsIso.epi_of_iso _) _).symm

/-- **Vanishing descends along a flat morphism whose image contains the support of the source.**
For a flat morphism `φ : Z' ⟶ Z` of algebraic spaces and a map `v : M ⟶ N` of `𝒪_Z`-modules with
the support of `M` contained in the image of `|Z'| ⟶ |Z|`, the inverse image `φ^*v` is zero
exactly when `v` is.

A map vanishes exactly when the inclusion of its kernel is an epimorphism, and the inverse image
along a flat morphism carries the inclusion of the kernel of `v` to that of the kernel of
`φ^*v`; surjectivity of the former descends because its target is `M`. -/
theorem modulePullback_map_eq_zero_iff_of_isFlat (φ : Z' ⟶ Z) (hφ : IsFlat B S hS φ.hom)
    (v : M ⟶ N)
    (hsupp : supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj M) ⊆
      Set.range (pointsMap B S hS Z'.1 φ.hom)) :
    (modulePullback B S hS φ).map v = 0 ↔ v = 0 := by
  rw [modulePullback_map_eq_zero_iff_epi_modulePullback_map_kernel_ι B S hS φ hφ v,
    epi_modulePullback_map_iff_of_isFlat B S hS φ hφ (kernel.ι v) hsupp,
    eq_zero_iff_epi_kernel_ι]

/-- **Vanishing descends along a flat morphism whose image contains the support of the target.**
For a flat morphism `φ : Z' ⟶ Z` of algebraic spaces and a map `v : M ⟶ N` of `𝒪_Z`-modules with
the support of `N` contained in the image of `|Z'| ⟶ |Z|`, the inverse image `φ^*v` is zero
exactly when `v` is.

A map vanishes exactly when the projection to its cokernel is a monomorphism, and the inverse
image carries the projection to the cokernel of `v` to that of the cokernel of `φ^*v`;
injectivity of the former descends because its source is `N`. -/
theorem modulePullback_map_eq_zero_iff_of_isFlat' (φ : Z' ⟶ Z) (hφ : IsFlat B S hS φ.hom)
    (v : M ⟶ N)
    (hsupp : supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj N) ⊆
      Set.range (pointsMap B S hS Z'.1 φ.hom)) :
    (modulePullback B S hS φ).map v = 0 ↔ v = 0 := by
  have hadj := modulePullbackAdjunction B S hS φ
  have := hadj.isLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS φ) :=
    hadj.leftAdjoint_preservesColimits
  have hπ : (modulePullback B S hS φ).map (cokernel.π v) =
      cokernel.π ((modulePullback B S hS φ).map v) ≫
        (PreservesCokernel.iso (modulePullback B S hS φ) v).inv :=
    (π_comp_cokernelComparison v (modulePullback B S hS φ)).symm
  rw [eq_zero_iff_mono_cokernel_π, eq_zero_iff_mono_cokernel_π,
    ← mono_modulePullback_map_iff_of_isFlat B S hS φ hφ (cokernel.π v) hsupp, hπ]
  exact (@mono_comp_iff_of_mono _ _ _ _ _ _ _ (IsIso.mono_of_iso _)).symm

/-- **Being an isomorphism descends along a flat morphism whose image contains both supports.**
For a flat morphism `φ : Z' ⟶ Z` of algebraic spaces and a map `v : M ⟶ N` of `𝒪_Z`-modules with
the supports of `M` and of `N` contained in the image of `|Z'| ⟶ |Z|`, the inverse image `φ^*v`
is an isomorphism exactly when `v` is.

The category of `𝒪_Z`-modules is abelian, hence balanced, so being an isomorphism is being both
a monomorphism and an epimorphism. -/
theorem isIso_modulePullback_map_iff_of_isFlat (φ : Z' ⟶ Z) (hφ : IsFlat B S hS φ.hom)
    (v : M ⟶ N)
    (hM : supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj M) ⊆
      Set.range (pointsMap B S hS Z'.1 φ.hom))
    (hN : supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj N) ⊆
      Set.range (pointsMap B S hS Z'.1 φ.hom)) :
    IsIso ((modulePullback B S hS φ).map v) ↔ IsIso v := by
  rw [isIso_iff_mono_and_epi_modules, isIso_iff_mono_and_epi_modules,
    mono_modulePullback_map_iff_of_isFlat B S hS φ hφ v hM,
    epi_modulePullback_map_iff_of_isFlat B S hS φ hφ v hN]

end FlatReflection

/-! ### The four conditions along a jointly surjective family of flat morphisms

A jointly surjective family of flat morphisms needs no support hypothesis: the ranges of the
induced maps on points cover the target, so a support which becomes empty after every member of
the family is empty. -/

section FlatCovering

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z : AlgebraicSpaces B S hS} {I : Type*} {Z' : I → AlgebraicSpaces B S hS}
    {M N : Modules.{u, u} B S hS Z.1 Z.2}

/-- A set whose inverse image under every member of a jointly surjective family is empty is
empty. -/
private theorem eq_empty_of_forall_preimage_eq_empty (φ : ∀ i, Z' i ⟶ Z)
    (hsurj : IsJointlySurjective B S hS (fun i => (Z' i).1) fun i => (φ i).hom)
    {T : Set (points B S hS Z.1)}
    (h : ∀ i, pointsMap B S hS (Z' i).1 (φ i).hom ⁻¹' T = ∅) : T = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun z hz => ?_
  obtain ⟨i, y, hy⟩ := (isJointlySurjective_iff B S hS _ _).1 hsurj z
  exact Set.eq_empty_iff_forall_notMem.mp (h i) y (by rwa [Set.mem_preimage, hy])

/-- **Surjectivity descends along a jointly surjective family of flat morphisms.**  A map of
`𝒪_Z`-modules whose inverse image along every member of a jointly surjective family of flat
morphisms is an epimorphism is itself an epimorphism. -/
theorem epi_of_forall_epi_modulePullback_map_of_isFlat (φ : ∀ i, Z' i ⟶ Z)
    (hφ : ∀ i, IsFlat B S hS (φ i).hom)
    (hsurj : IsJointlySurjective B S hS (fun i => (Z' i).1) fun i => (φ i).hom)
    (v : M ⟶ N) (h : ∀ i, Epi ((modulePullback B S hS (φ i)).map v)) : Epi v := by
  refine (epi_iff_supportOfSheaf_cokernel_eq_empty B S hS v).2
    (eq_empty_of_forall_preimage_eq_empty B S hS φ hsurj fun i => ?_)
  rw [← supportOfSheaf_modulePullback_eq_preimage_of_isFlat B S hS (φ i) (hφ i),
    ← supportOfSheaf_cokernel_modulePullback_map B S hS (φ i) v]
  exact (epi_iff_supportOfSheaf_cokernel_eq_empty B S hS _).1 (h i)

/-- **Injectivity descends along a jointly surjective family of flat morphisms.**  A map of
`𝒪_Z`-modules whose inverse image along every member of a jointly surjective family of flat
morphisms is a monomorphism is itself a monomorphism. -/
theorem mono_of_forall_mono_modulePullback_map_of_isFlat (φ : ∀ i, Z' i ⟶ Z)
    (hφ : ∀ i, IsFlat B S hS (φ i).hom)
    (hsurj : IsJointlySurjective B S hS (fun i => (Z' i).1) fun i => (φ i).hom)
    (v : M ⟶ N) (h : ∀ i, Mono ((modulePullback B S hS (φ i)).map v)) : Mono v := by
  refine (mono_iff_supportOfSheaf_kernel_eq_empty B S hS v).2
    (eq_empty_of_forall_preimage_eq_empty B S hS φ hsurj fun i => ?_)
  rw [← supportOfSheaf_modulePullback_eq_preimage_of_isFlat B S hS (φ i) (hφ i),
    ← supportOfSheaf_kernel_modulePullback_map B S hS (φ i) (hφ i) v]
  exact (mono_iff_supportOfSheaf_kernel_eq_empty B S hS _).1 (h i)

/-- **Vanishing descends along a jointly surjective family of flat morphisms.**  A map of
`𝒪_Z`-modules whose inverse image along every member of a jointly surjective family of flat
morphisms is zero is itself zero. -/
theorem eq_zero_of_forall_modulePullback_map_eq_zero_of_isFlat (φ : ∀ i, Z' i ⟶ Z)
    (hφ : ∀ i, IsFlat B S hS (φ i).hom)
    (hsurj : IsJointlySurjective B S hS (fun i => (Z' i).1) fun i => (φ i).hom)
    (v : M ⟶ N) (h : ∀ i, (modulePullback B S hS (φ i)).map v = 0) : v = 0 :=
  (eq_zero_iff_epi_kernel_ι B S hS v).2
    (epi_of_forall_epi_modulePullback_map_of_isFlat B S hS φ hφ hsurj (kernel.ι v) fun i =>
      (modulePullback_map_eq_zero_iff_epi_modulePullback_map_kernel_ι B S hS (φ i) (hφ i) v).1
        (h i))

/-- **Being an isomorphism descends along a jointly surjective family of flat morphisms.**  A map
of `𝒪_Z`-modules whose inverse image along every member of a jointly surjective family of flat
morphisms is an isomorphism is itself an isomorphism. -/
theorem isIso_of_forall_isIso_modulePullback_map_of_isFlat (φ : ∀ i, Z' i ⟶ Z)
    (hφ : ∀ i, IsFlat B S hS (φ i).hom)
    (hsurj : IsJointlySurjective B S hS (fun i => (Z' i).1) fun i => (φ i).hom)
    (v : M ⟶ N) (h : ∀ i, IsIso ((modulePullback B S hS (φ i)).map v)) : IsIso v := by
  refine (isIso_iff_mono_and_epi_modules B S hS Z v).2
    ⟨mono_of_forall_mono_modulePullback_map_of_isFlat B S hS φ hφ hsurj v fun i =>
      ((isIso_iff_mono_and_epi_modules B S hS (Z' i) _).1 (h i)).1,
    epi_of_forall_epi_modulePullback_map_of_isFlat B S hS φ hφ hsurj v fun i =>
      ((isIso_iff_mono_and_epi_modules B S hS (Z' i) _).1 (h i)).2⟩

end FlatCovering

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ModuleMapSituation

variable (D : ModuleMapSituation.{u, u} B S hS) {X' : AlgebraicSpaces B S hS} (g : X' ⟶ D.X)
    (hF : ((modulePullback B S hS g).obj D.F).IsQuasicoherentOnSite)
    (hG : ((modulePullback B S hS g).obj D.G).IsQuasicoherentOnSite)

/-! ### The two base-changed maps are conjugate

The base change of `u'` to a test scheme `T` is the inverse image along `X' ×_Y T ⟶ X'` of
`g^*u`, while the inverse image along the comparison `X' ×_Y T ⟶ X ×_Y T` of the base change of
`u` is the inverse image along `X' ×_Y T ⟶ X ×_Y T ⟶ X` of `u`.  The two composites
`X' ×_Y T ⟶ X` agree, so the two maps are conjugate by the composition comparisons of the
inverse image. -/

section Comparison

/-- A condition on maps of modules unchanged by composing with isomorphisms holds for the
pullback along a composite exactly when it holds for the iterated pullback. -/
private theorem map_comp_iff (P : ModulePullbackSystem.{u, u} B S hS)
    (p : ∀ {Z : AlgebraicSpaces B S hS} {M N : Modules.{u, u} B S hS Z.1 Z.2}, (M ⟶ N) → Prop)
    (hp : ∀ {Z : AlgebraicSpaces B S hS} {M M' N N' : Modules.{u, u} B S hS Z.1 Z.2}
      (a : M' ⟶ M) (b : N ⟶ N') [IsIso a] [IsIso b] (x : M ⟶ N), p (a ≫ x ≫ b) ↔ p x)
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (a : M ⟶ N) :
    p ((P.functor (f ≫ g)).map a) ↔ p ((P.functor f).map ((P.functor g).map a)) := by
  rw [P.map_comp_eq_conj f g a, hp]

variable (P : ModulePullbackSystem.{u, u} B S hS) (T : D.SchemesOver)

/-- The inverse image along the comparison of base changes of the base change of `u` is a
monomorphism exactly when the base change of `u'` is. -/
theorem mono_pullbackBaseChangeMap_map_iff :
    Mono ((P.functor (D.pullbackBaseChangeMap g hF hG T)).map
        ((P.functor (D.baseChangeProjection T)).map D.u)) ↔
      Mono ((P.functor ((D.pullbackSituation g hF hG).baseChangeProjection T)).map
        ((P.functor g).map D.u)) := by
  rw [← map_comp_iff P (fun x => Mono x) mono_conj_iff,
    D.pullbackBaseChangeMap_comp_baseChangeProjection g hF hG T,
    map_comp_iff P (fun x => Mono x) mono_conj_iff]

/-- The inverse image along the comparison of base changes of the base change of `u` is an
epimorphism exactly when the base change of `u'` is. -/
theorem epi_pullbackBaseChangeMap_map_iff :
    Epi ((P.functor (D.pullbackBaseChangeMap g hF hG T)).map
        ((P.functor (D.baseChangeProjection T)).map D.u)) ↔
      Epi ((P.functor ((D.pullbackSituation g hF hG).baseChangeProjection T)).map
        ((P.functor g).map D.u)) := by
  rw [← map_comp_iff P (fun x => Epi x) epi_conj_iff,
    D.pullbackBaseChangeMap_comp_baseChangeProjection g hF hG T,
    map_comp_iff P (fun x => Epi x) epi_conj_iff]

/-- The inverse image along the comparison of base changes of the base change of `u` is an
isomorphism exactly when the base change of `u'` is. -/
theorem isIso_pullbackBaseChangeMap_map_iff :
    IsIso ((P.functor (D.pullbackBaseChangeMap g hF hG T)).map
        ((P.functor (D.baseChangeProjection T)).map D.u)) ↔
      IsIso ((P.functor ((D.pullbackSituation g hF hG).baseChangeProjection T)).map
        ((P.functor g).map D.u)) := by
  rw [← map_comp_iff P (fun x => IsIso x) isIso_conj_iff,
    D.pullbackBaseChangeMap_comp_baseChangeProjection g hF hG T,
    map_comp_iff P (fun x => IsIso x) isIso_conj_iff]

/-- The inverse image along the comparison of base changes of the base change of `u` vanishes
exactly when the base change of `u'` does. -/
theorem pullbackBaseChangeMap_map_eq_zero_iff :
    (P.functor (D.pullbackBaseChangeMap g hF hG T)).map
        ((P.functor (D.baseChangeProjection T)).map D.u) = 0 ↔
      (P.functor ((D.pullbackSituation g hF hG).baseChangeProjection T)).map
        ((P.functor g).map D.u) = 0 := by
  rw [← map_comp_iff P (fun x => x = 0) eq_zero_conj_iff,
    D.pullbackBaseChangeMap_comp_baseChangeProjection g hF hG T,
    map_comp_iff P (fun x => x = 0) eq_zero_conj_iff]

end Comparison

/-! ### The base-changed maps over a morphism of test schemes are conjugate -/

section BaseChangeComparison

variable (P : ModulePullbackSystem.{u, u} B S hS) {T T' : D.SchemesOver} (k : T' ⟶ T)

/-- The inverse image along the comparison of base-change spaces of the base change of `u` at
`T` is a monomorphism exactly when the base change of `u` at `T'` is. -/
theorem mono_baseChangeMap_map_iff :
    Mono ((P.functor (D.baseChangeMap k)).map (D.baseChangeHom P T)) ↔
      Mono (D.baseChangeHom P T') := by
  have key := map_comp_iff P (fun x => Mono x) mono_conj_iff (D.baseChangeMap k)
    (D.baseChangeProjection T) D.u
  rw [D.baseChangeMap_comp_baseChangeProjection k] at key
  exact key.symm

/-- The inverse image along the comparison of base-change spaces of the base change of `u` at
`T` is an epimorphism exactly when the base change of `u` at `T'` is. -/
theorem epi_baseChangeMap_map_iff :
    Epi ((P.functor (D.baseChangeMap k)).map (D.baseChangeHom P T)) ↔
      Epi (D.baseChangeHom P T') := by
  have key := map_comp_iff P (fun x => Epi x) epi_conj_iff (D.baseChangeMap k)
    (D.baseChangeProjection T) D.u
  rw [D.baseChangeMap_comp_baseChangeProjection k] at key
  exact key.symm

/-- The inverse image along the comparison of base-change spaces of the base change of `u` at
`T` is an isomorphism exactly when the base change of `u` at `T'` is. -/
theorem isIso_baseChangeMap_map_iff :
    IsIso ((P.functor (D.baseChangeMap k)).map (D.baseChangeHom P T)) ↔
      IsIso (D.baseChangeHom P T') := by
  have key := map_comp_iff P (fun x => IsIso x) isIso_conj_iff (D.baseChangeMap k)
    (D.baseChangeProjection T) D.u
  rw [D.baseChangeMap_comp_baseChangeProjection k] at key
  exact key.symm

/-- The inverse image along the comparison of base-change spaces of the base change of `u` at
`T` vanishes exactly when the base change of `u` at `T'` does. -/
theorem baseChangeMap_map_eq_zero_iff :
    (P.functor (D.baseChangeMap k)).map (D.baseChangeHom P T) = 0 ↔
      D.baseChangeHom P T' = 0 := by
  have key := map_comp_iff P (fun x => x = 0) eq_zero_conj_iff (D.baseChangeMap k)
    (D.baseChangeProjection T) D.u
  rw [D.baseChangeMap_comp_baseChangeProjection k] at key
  exact key.symm

end BaseChangeComparison

/-! ### From the conditions at every test scheme to equality of loci

The four loci are subterminal presheaves on the test schemes, so two of them attached to
conditions that agree at every test scheme are equal. -/

section Loci

variable (P : ModulePullbackSystem.{u, u} B S hS)

/-- If the base-changed maps are surjective at the same test schemes, the two surjectivity loci
agree. -/
theorem surjFunctor_pullbackSituation_eq_of
    (h : ∀ T : D.SchemesOver,
      D.IsSurjectiveAt P T ↔ (D.pullbackSituation g hF hG).IsSurjectiveAt P T) :
    D.surjFunctor P = (D.pullbackSituation g hF hG).surjFunctor P :=
  subterminalFunctor_congr D (fun k hT => D.isSurjectiveAt_of_hom P k hT)
    (fun k hT => (D.pullbackSituation g hF hG).isSurjectiveAt_of_hom P k hT)
    (funext fun T => propext (h T))

/-- If the base-changed maps vanish at the same test schemes, the two vanishing loci agree. -/
theorem zeroFunctor_pullbackSituation_eq_of
    (h : ∀ T : D.SchemesOver, D.IsZeroAt P T ↔ (D.pullbackSituation g hF hG).IsZeroAt P T) :
    D.zeroFunctor P = (D.pullbackSituation g hF hG).zeroFunctor P :=
  subterminalFunctor_congr D (fun k hT => D.isZeroAt_of_hom P k hT)
    (fun k hT => (D.pullbackSituation g hF hG).isZeroAt_of_hom P k hT)
    (funext fun T => propext (h T))

/-- If the base-changed maps are universally injective at the same test schemes, the two
universal injectivity loci agree. -/
theorem injFunctor_pullbackSituation_eq_of
    (h : ∀ T : D.SchemesOver,
      D.IsUniversallyInjectiveAt P T ↔ (D.pullbackSituation g hF hG).IsUniversallyInjectiveAt P T) :
    D.injFunctor P = (D.pullbackSituation g hF hG).injFunctor P :=
  subterminalFunctor_congr D (fun k hT => D.isUniversallyInjectiveAt_of_hom P k hT)
    (fun k hT => (D.pullbackSituation g hF hG).isUniversallyInjectiveAt_of_hom P k hT)
    (funext fun T => propext (h T))

/-- If the base-changed maps are isomorphisms at the same test schemes, the two isomorphism loci
agree. -/
theorem isoFunctor_pullbackSituation_eq_of
    (h : ∀ T : D.SchemesOver, D.IsIsoAt P T ↔ (D.pullbackSituation g hF hG).IsIsoAt P T) :
    D.isoFunctor P = (D.pullbackSituation g hF hG).isoFunctor P :=
  subterminalFunctor_congr D (fun k hT => D.isIsoAt_of_hom P k hT)
    (fun k hT => (D.pullbackSituation g hF hG).isIsoAt_of_hom P k hT)
    (funext fun T => propext (h T))

end Loci

/-! ### Stacks 083I -/

section Flat

/-- At a test scheme the base change of `u` is surjective exactly when the base change of `u'`
is, when `𝒢` is of finite type and its support lies in the image of `|X'| ⟶ |X|`. -/
private theorem isSurjectiveAt_pullbackSituation_iff (hgflat : IsFlat B S hS g.hom)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hGsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.G) ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) (T : D.SchemesOver) :
    D.IsSurjectiveAt (modulePullbackSystem B S hS) T ↔
      (D.pullbackSituation g hF hG).IsSurjectiveAt (modulePullbackSystem B S hS) T :=
  Iff.trans
    (epi_modulePullback_map_iff_of_isFlat B S hS (D.pullbackBaseChangeMap g hF hG T)
        (D.isFlat_pullbackBaseChangeMap g hF hG hgflat T)
        (D.baseChangeHom (modulePullbackSystem B S hS) T)
        (D.supportOfSheaf_baseChange_subset_range g hF hG D.G D.quasicoherent_G hGft
          hGsupp T)).symm
    (D.epi_pullbackBaseChangeMap_map_iff g hF hG (modulePullbackSystem B S hS) T)

/-- At a test scheme the base change of `u` is a monomorphism exactly when the base change of
`u'` is, when `ℱ` is of finite type and its support lies in the image of `|X'| ⟶ |X|`. -/
private theorem mono_baseChangeHom_pullbackSituation_iff (hgflat : IsFlat B S hS g.hom)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hFsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F) ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) (T : D.SchemesOver) :
    Mono (D.baseChangeHom (modulePullbackSystem B S hS) T) ↔
      Mono ((D.pullbackSituation g hF hG).baseChangeHom (modulePullbackSystem B S hS) T) :=
  Iff.trans
    (mono_modulePullback_map_iff_of_isFlat B S hS (D.pullbackBaseChangeMap g hF hG T)
        (D.isFlat_pullbackBaseChangeMap g hF hG hgflat T)
        (D.baseChangeHom (modulePullbackSystem B S hS) T)
        (D.supportOfSheaf_baseChange_subset_range g hF hG D.F D.quasicoherent_F hFft
          hFsupp T)).symm
    (D.mono_pullbackBaseChangeMap_map_iff g hF hG (modulePullbackSystem B S hS) T)

/-- At a test scheme the base change of `u` vanishes exactly when the base change of `u'` does,
when `𝒢` is of finite type and its support lies in the image of `|X'| ⟶ |X|`. -/
private theorem isZeroAt_pullbackSituation_iff_of_target (hgflat : IsFlat B S hS g.hom)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hGsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.G) ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) (T : D.SchemesOver) :
    D.IsZeroAt (modulePullbackSystem B S hS) T ↔
      (D.pullbackSituation g hF hG).IsZeroAt (modulePullbackSystem B S hS) T :=
  Iff.trans
    (modulePullback_map_eq_zero_iff_of_isFlat' B S hS (D.pullbackBaseChangeMap g hF hG T)
        (D.isFlat_pullbackBaseChangeMap g hF hG hgflat T)
        (D.baseChangeHom (modulePullbackSystem B S hS) T)
        (D.supportOfSheaf_baseChange_subset_range g hF hG D.G D.quasicoherent_G hGft
          hGsupp T)).symm
    (D.pullbackBaseChangeMap_map_eq_zero_iff g hF hG (modulePullbackSystem B S hS) T)

/-- At a test scheme the base change of `u` vanishes exactly when the base change of `u'` does,
when `ℱ` is of finite type and its support lies in the image of `|X'| ⟶ |X|`. -/
private theorem isZeroAt_pullbackSituation_iff_of_source (hgflat : IsFlat B S hS g.hom)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hFsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F) ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) (T : D.SchemesOver) :
    D.IsZeroAt (modulePullbackSystem B S hS) T ↔
      (D.pullbackSituation g hF hG).IsZeroAt (modulePullbackSystem B S hS) T :=
  Iff.trans
    (modulePullback_map_eq_zero_iff_of_isFlat B S hS (D.pullbackBaseChangeMap g hF hG T)
        (D.isFlat_pullbackBaseChangeMap g hF hG hgflat T)
        (D.baseChangeHom (modulePullbackSystem B S hS) T)
        (D.supportOfSheaf_baseChange_subset_range g hF hG D.F D.quasicoherent_F hFft
          hFsupp T)).symm
    (D.pullbackBaseChangeMap_map_eq_zero_iff g hF hG (modulePullbackSystem B S hS) T)

/-- At a test scheme the base change of `u` is an isomorphism exactly when the base change of
`u'` is, when `ℱ` and `𝒢` are of finite type and their supports lie in the image of
`|X'| ⟶ |X|`. -/
private theorem isIsoAt_pullbackSituation_iff (hgflat : IsFlat B S hS g.hom)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hFsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F) ⊆
      Set.range (pointsMap B S hS X'.1 g.hom))
    (hGsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.G) ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) (T : D.SchemesOver) :
    D.IsIsoAt (modulePullbackSystem B S hS) T ↔
      (D.pullbackSituation g hF hG).IsIsoAt (modulePullbackSystem B S hS) T :=
  Iff.trans
    (isIso_modulePullback_map_iff_of_isFlat B S hS (D.pullbackBaseChangeMap g hF hG T)
        (D.isFlat_pullbackBaseChangeMap g hF hG hgflat T)
        (D.baseChangeHom (modulePullbackSystem B S hS) T)
        (D.supportOfSheaf_baseChange_subset_range g hF hG D.F D.quasicoherent_F hFft hFsupp T)
        (D.supportOfSheaf_baseChange_subset_range g hF hG D.G D.quasicoherent_G hGft
          hGsupp T)).symm
    (D.isIso_pullbackBaseChangeMap_map_iff g hF hG (modulePullbackSystem B S hS) T)

/-- **Stacks 083I part (1).**  In the situation of Stacks 083F let `g : X' ⟶ X` be a flat
morphism of algebraic spaces and let `u'` be the inverse image of `u` on `X'`.  If `𝒢` is of
finite type and the image of `|X'| ⟶ |X|` contains the support of `𝒢`, then the surjectivity
loci of `u` and `u'` agree and so do their vanishing loci.

Both equalities come from the corresponding conditions at a single test scheme: the comparison
`X' ×_Y T ⟶ X ×_Y T` of the two base changes is flat and its image contains the support of the
base change of `𝒢`, so surjectivity and vanishing descend along it, and the loci, being
subterminal, are determined by the conditions.

The form with the quasi-coherence of `g^*ℱ` and `g^*𝒢` discharged by Stacks 03GA is
`AlgebraicGeometry.Space.ModuleMapSituation.surjFunctor_and_zeroFunctor_inverseImageSituation_eq`.
-/
@[stacks 083I "part (1) over `pullbackSituation`; see `inverseImageSituation`"]
theorem surjFunctor_and_zeroFunctor_pullbackSituation_eq (hgflat : IsFlat B S hS g.hom)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hGsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.G) ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) :
    D.surjFunctor (modulePullbackSystem B S hS) =
        (D.pullbackSituation g hF hG).surjFunctor (modulePullbackSystem B S hS) ∧
      D.zeroFunctor (modulePullbackSystem B S hS) =
        (D.pullbackSituation g hF hG).zeroFunctor (modulePullbackSystem B S hS) :=
  ⟨D.surjFunctor_pullbackSituation_eq_of g hF hG (modulePullbackSystem B S hS)
      (D.isSurjectiveAt_pullbackSituation_iff g hF hG hgflat hGft hGsupp),
    D.zeroFunctor_pullbackSituation_eq_of g hF hG (modulePullbackSystem B S hS)
      (D.isZeroAt_pullbackSituation_iff_of_target g hF hG hgflat hGft hGsupp)⟩

/-- **Stacks 083I part (2).**  In the situation of Stacks 083F let `g : X' ⟶ X` be a flat
morphism of algebraic spaces and let `u'` be the inverse image of `u` on `X'`.  If `ℱ` is of
finite type and the image of `|X'| ⟶ |X|` contains the support of `ℱ`, then the universal
injectivity loci of `u` and `u'` agree and so do their vanishing loci.

Universal injectivity at a test scheme is injectivity of the base change over every further test
scheme, and the two situations have the same test schemes, so the equality of the two universal
injectivity loci follows from injectivity agreeing at every single test scheme, which is the
descent of injectivity along the comparison of the two base changes.

The form with the quasi-coherence of `g^*ℱ` and `g^*𝒢` discharged by Stacks 03GA is
`AlgebraicGeometry.Space.ModuleMapSituation.injFunctor_and_zeroFunctor_inverseImageSituation_eq`.
-/
@[stacks 083I "part (2) over `pullbackSituation`; see `inverseImageSituation`"]
theorem injFunctor_and_zeroFunctor_pullbackSituation_eq (hgflat : IsFlat B S hS g.hom)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hFsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F) ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) :
    D.injFunctor (modulePullbackSystem B S hS) =
        (D.pullbackSituation g hF hG).injFunctor (modulePullbackSystem B S hS) ∧
      D.zeroFunctor (modulePullbackSystem B S hS) =
        (D.pullbackSituation g hF hG).zeroFunctor (modulePullbackSystem B S hS) := by
  refine ⟨D.injFunctor_pullbackSituation_eq_of g hF hG (modulePullbackSystem B S hS)
      fun T => ⟨fun h T' k => ?_, fun h T' k => ?_⟩,
    D.zeroFunctor_pullbackSituation_eq_of g hF hG (modulePullbackSystem B S hS)
      (D.isZeroAt_pullbackSituation_iff_of_source g hF hG hgflat hFft hFsupp)⟩
  · exact (D.mono_baseChangeHom_pullbackSituation_iff g hF hG hgflat hFft hFsupp T').1 (h T' k)
  · exact (D.mono_baseChangeHom_pullbackSituation_iff g hF hG hgflat hFft hFsupp T').2 (h T' k)

/-- **Stacks 083I part (3).**  In the situation of Stacks 083F let `g : X' ⟶ X` be a flat
morphism of algebraic spaces and let `u'` be the inverse image of `u` on `X'`.  If `ℱ` and `𝒢`
are of finite type and the image of `|X'| ⟶ |X|` contains the supports of both, then the
isomorphism loci of `u` and `u'` agree.

The comparison `X' ×_Y T ⟶ X ×_Y T` of the two base changes is flat and its image contains the
supports of the base changes of `ℱ` and of `𝒢`, so being an isomorphism descends along it at
every test scheme, and the loci, being subterminal, are determined by the conditions.

The form with the quasi-coherence of `g^*ℱ` and `g^*𝒢` discharged by Stacks 03GA is
`AlgebraicGeometry.Space.ModuleMapSituation.isoFunctor_inverseImageSituation_eq`. -/
@[stacks 083I "part (3) over `pullbackSituation`; see `inverseImageSituation`"]
theorem isoFunctor_pullbackSituation_eq (hgflat : IsFlat B S hS g.hom)
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F)
    (hGft : SheafOfModules.IsFiniteTypeOnSite D.G)
    (hFsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.F) ⊆
      Set.range (pointsMap B S hS X'.1 g.hom))
    (hGsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.G) ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) :
    D.isoFunctor (modulePullbackSystem B S hS) =
      (D.pullbackSituation g hF hG).isoFunctor (modulePullbackSystem B S hS) :=
  D.isoFunctor_pullbackSituation_eq_of g hF hG (modulePullbackSystem B S hS)
    (D.isIsoAt_pullbackSituation_iff g hF hG hgflat hFft hGft hFsupp hGsupp)

end Flat

end ModuleMapSituation

end AlgebraicGeometry.Space

end
