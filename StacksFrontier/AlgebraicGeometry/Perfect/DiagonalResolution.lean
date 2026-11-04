module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ExternalTensorProduct
public import StacksFrontier.AlgebraicGeometry.PushforwardCoherent
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Resolutions of the diagonal by external tensor products

Let `R` be a Noetherian ring and `f : X ⟶ Spec R` a separated morphism of finite type. This
file constructs, from a supply of surjections onto coherent modules on `X ×_R X` by external
tensor products of finite locally free modules, a resolution

`… → ℰ₁ ⊠ 𝒢₁ → ℰ₀ ⊠ 𝒢₀ → 𝒪_Δ → 0`

of the structure sheaf of the diagonal with finite locally free factors `ℰᵢ`, `𝒢ᵢ`.

## Main definitions

* `AlgebraicGeometry.ExternalTensorCover`: a surjection onto a module on `X ×_R X` from an
  external tensor product of two finite locally free modules on `X`.
* `AlgebraicGeometry.DiagonalResolution`: a resolution of `𝒪_Δ` of the displayed shape.
* `AlgebraicGeometry.DiagonalResolution.ofExternalTensorCovers`: the construction of such a
  resolution from a supply of external tensor covers.
* `AlgebraicGeometry.DiagonalResolution.originalComplex`: the complex
  `… → ℰ₂ ⊠ 𝒢₂ → ℰ₁ ⊠ 𝒢₁ → ℰ₀ ⊠ 𝒢₀` of external tensor products obtained by discarding the
  augmentation term of the resolution, which is [Stacks, Tag 0G09].
* `AlgebraicGeometry.DiagonalResolution.augmentation`: the map from the degree-zero term of that
  complex onto `𝒪_Δ`.

## Main results

* `AlgebraicGeometry.isCoherent_externalTensorProduct`: the external tensor product of two
  finite locally free modules on a scheme of finite type over a Noetherian ring is coherent.
* `AlgebraicGeometry.isCoherent_diagonalUnit`: the structure sheaf of the diagonal of a
  separated morphism of finite type over a Noetherian ring is coherent.
* `AlgebraicGeometry.nonempty_diagonalResolution_of_externalTensorCovers`: the existence
  statement.

The resolution constructed here is deliberately **untagged**. The resolution of the diagonal is
[Stacks, Tag 0FZ2], whose only content beyond what is constructed here is the unconditional
existence of the external tensor covers used as a hypothesis; that is [Stacks, Tag 0FZ0]. Tag
0FZ2 is carried elsewhere in this development, by
`AlgebraicGeometry.exists_diagonalResolution`, which combines the two.

## Implementation notes

The augmented resolution is a nonnegative chain complex which is exact in every degree: its
degree-zero term is the direct image `Δ_*𝒪_X` and its degree `i + 1` term is the external
tensor product indexed by `i`, so the differential into degree zero is the augmentation
displayed in the source. The complex is built by repeatedly covering the kernel of the previous
covering map, which stays coherent by [Stacks, Tag 01BY]; exactness at each spot is the
factorization of a covering map through the kernel of its successor.

Coherence of the covering modules is obtained through coherence rather than through finite local
freeness: `ℰ ⊠ 𝒢` is a tensor product of two pullbacks of coherent modules, so
[Stacks, Tag 01CE] applies. The route through finite local freeness would need the equivalence
of `IsFiniteLocallyFree` with `IsLocallyFree ∧ IsFiniteType` ([Stacks, Tag 05P2]) and the
stability of local freeness and finite type under tensor products, none of which is available
here.

The complex `originalComplex` of [Stacks, Tag 0G09] is the resolution with its degree-zero term
`𝒪_Δ` discarded and the remaining terms reindexed, so that its term in degree `i` is `ℰᵢ ⊠ 𝒢ᵢ`.
It is exact in every positive degree, and its degree-zero term maps onto `𝒪_Δ`; these two
properties together are exactly the exactness of the augmented resolution.

## References

* [Stacks Project, Tag 0FZ0](https://stacks.math.columbia.edu/tag/0FZ0)
* [Stacks Project, Tag 0FZ2](https://stacks.math.columbia.edu/tag/0FZ2)
* [Stacks Project, Tag 0G09](https://stacks.math.columbia.edu/tag/0G09)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- A surjection onto a module on `X ×_R X` from an external tensor product of two finite
locally free modules on `X`. This is the data produced by [Stacks, Tag 0FZ0]. -/
structure ExternalTensorCover (f : X ⟶ Spec (.of R)) (M : (pullback f f).Modules) where
  /-- The first factor of the covering external tensor product. -/
  left : X.Modules
  /-- The second factor of the covering external tensor product. -/
  right : X.Modules
  /-- The first factor is finite locally free. -/
  left_finiteLocallyFree :
    SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) left
  /-- The second factor is finite locally free. -/
  right_finiteLocallyFree :
    SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) right
  /-- The covering map. -/
  map : externalTensorProduct f f left right ⟶ M
  /-- The covering map is surjective. -/
  epi : Epi map

/-- A scheme locally of finite type over a Noetherian ring is locally Noetherian. -/
private theorem isLocallyNoetherian_of_locallyOfFiniteType [IsNoetherianRing R]
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] : IsLocallyNoetherian X :=
  have : IsLocallyNoetherian (Spec (.of R)) := isLocallyNoetherian_Spec.mpr inferInstance
  LocallyOfFiniteType.isLocallyNoetherian f

/-- **The external tensor product of two finite locally free modules is coherent.** Both factors
are coherent, hence so are their pullbacks to the fibre product, and the tensor product of two
coherent modules is coherent by [Stacks, Tag 01CE]. -/
theorem isCoherent_externalTensorProduct [IsNoetherianRing R] (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] (E G : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
    (hG : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) G) :
    (externalTensorProduct f f E G).IsCoherent := by
  have := isLocallyNoetherian_of_locallyOfFiniteType f
  have key : ∀ (g : pullback f f ⟶ X) (F : X.Modules),
      SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) F →
        ((Scheme.Modules.pullback g).obj F).IsCoherent := fun g F hF => by
    have := hF
    have := Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_isFiniteLocallyFree X F
    exact isCoherent_pullback g F
  have hEp := key (pullback.fst f f) E hE
  have hGp := key (pullback.snd f f) G hG
  exact @AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent (pullback f f).toRingedSpace
    ((Scheme.Modules.pullback (pullback.fst f f)).obj E)
    ((Scheme.Modules.pullback (pullback.snd f f)).obj G) hEp hGp

/-- **The structure sheaf of the diagonal is coherent.** The diagonal of a separated morphism is
a closed immersion, hence finite, and the direct image of a coherent module along a finite
morphism is coherent by [Stacks, Tag 01Y6]. -/
theorem isCoherent_diagonalUnit [IsNoetherianRing R] (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] :
    ((Scheme.Modules.pushforward (pullback.diagonal f)).obj
      (SheafOfModules.unit X.ringCatSheaf)).IsCoherent := by
  have := isLocallyNoetherian_of_locallyOfFiniteType f
  have : IsLocallyNoetherian (pullback f f) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f f)
  have hUnit : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  have hUnitQC : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent ∧
      (SheafOfModules.unit X.ringCatSheaf).IsFiniteType :=
    ((Stacks.AlgebraicGeometry.CoherentTFAE.coherent_tfae X
      (SheafOfModules.unit X.ringCatSheaf)).out 1 2).mp hUnit
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent := hUnitQC.1
  have : (SheafOfModules.unit X.ringCatSheaf).IsCoherent := hUnit
  have : IsFinite (pullback.diagonal f) := inferInstance
  exact Stacks.AlgebraicGeometry.PushforwardCoherent.pushforward_isCoherent_of_isFinite
    (pullback.diagonal f) (SheafOfModules.unit X.ringCatSheaf)

/-- A morphism into a kernel, followed by the inclusion and then the map whose kernel it is,
vanishes. Stated in an abstract category so that it can be applied by `exact`: rewriting with
`CategoryTheory.Category.assoc` inside `Scheme.Modules` does not fire, the category instance
there being hidden behind a definition. -/
private lemma kernel_comp_eq_zero {C : Type*} [Category C] [HasZeroMorphisms C] [HasKernels C]
    {A B T : C} (q : A ⟶ B) (g : T ⟶ kernel q) : (g ≫ kernel.ι q) ≫ q = 0 := by
  rw [Category.assoc, kernel.condition, comp_zero]

/-- The two-step form of `kernel_comp_eq_zero`, in the bracketing in which the differentials of
the resolution compose. -/
private lemma kernel_comp_comp_eq_zero {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasKernels C] {A B D T : C} (q : A ⟶ B) (g : T ⟶ kernel q) (h : B ⟶ D) :
    (g ≫ kernel.ι q) ≫ (q ≫ h) = 0 := by
  rw [← Category.assoc, kernel_comp_eq_zero, zero_comp]

/-- A resolution of the structure sheaf of the relative diagonal whose positive-degree terms are
external tensor products of finite locally free modules. -/
structure DiagonalResolution (f : X ⟶ Spec (.of R)) where
  /-- The chain complex underlying the augmented resolution. -/
  complex : ChainComplex (pullback f f).Modules ℕ
  /-- The complex is exact in every degree. -/
  acyclic : complex.Acyclic
  /-- The first factors in the external tensor products. -/
  left : ℕ → X.Modules
  /-- The second factors in the external tensor products. -/
  right : ℕ → X.Modules
  /-- Every first factor is finite locally free. -/
  left_finiteLocallyFree (i : ℕ) :
    SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (left i)
  /-- Every second factor is finite locally free. -/
  right_finiteLocallyFree (i : ℕ) :
    SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (right i)
  /-- The degree-zero term is the direct image of the structure sheaf along the diagonal. -/
  zeroIso : complex.X 0 ≅
    (Scheme.Modules.pushforward (pullback.diagonal f)).obj (SheafOfModules.unit _)
  /-- The term in degree `i + 1` is the external tensor product of the corresponding finite
  locally free modules. -/
  termIso (i : ℕ) :
    complex.X (i + 1) ≅ externalTensorProduct f f (left i) (right i)

namespace DiagonalResolution

section OriginalComplex

variable {f : X ⟶ Spec (.of R)} (r : DiagonalResolution f)

/-- **The complex `… → ℰ₂ ⊠ 𝒢₂ → ℰ₁ ⊠ 𝒢₁ → ℰ₀ ⊠ 𝒢₀` of external tensor products underlying a
resolution of the diagonal.** It is the augmented resolution with its degree-zero term `𝒪_Δ`
discarded, so its term in degree `i` is the external tensor product indexed by `i`. -/
@[stacks 0G09]
def originalComplex : ChainComplex (pullback f f).Modules ℕ where
  X i := r.complex.X (i + 1)
  d i j := r.complex.d (i + 1) (j + 1)
  shape i j h := r.complex.shape _ _ (by
    simp only [ComplexShape.down_Rel] at h ⊢
    omega)
  d_comp_d' _ _ _ _ _ := r.complex.d_comp_d _ _ _

/-- The term of degree `i` of `originalComplex` is the term of degree `i + 1` of the resolution. -/
@[simp]
theorem originalComplex_X (i : ℕ) : r.originalComplex.X i = r.complex.X (i + 1) := rfl

/-- The differential of `originalComplex` from degree `i` to degree `j` is the differential of the
resolution from degree `i + 1` to degree `j + 1`. -/
@[simp]
theorem originalComplex_d (i j : ℕ) :
    r.originalComplex.d i j = r.complex.d (i + 1) (j + 1) := rfl

/-- The term of degree `i` of the complex of external tensor products is `ℰᵢ ⊠ 𝒢ᵢ`. -/
def originalComplexTermIso (i : ℕ) :
    r.originalComplex.X i ≅ externalTensorProduct f f (r.left i) (r.right i) :=
  r.termIso i

/-- **The complex of external tensor products is exact in every positive degree.** Exactness at
degree `i + 1` is exactness of the augmented resolution at degree `i + 2`. -/
theorem originalComplex_exactAt_succ (i : ℕ) : r.originalComplex.ExactAt (i + 1) :=
  (r.originalComplex.exactAt_iff' (i + 1 + 1) (i + 1) i (by simp) (by simp)).2
    ((r.complex.exactAt_iff' (i + 1 + 1 + 1) (i + 1 + 1) (i + 1) (by simp) (by simp)).1
      (r.acyclic (i + 1 + 1)))

/-- The augmentation of the complex of external tensor products: the differential of the
resolution out of degree one, followed by the identification of its degree-zero term with
`𝒪_Δ`. -/
def augmentation : r.originalComplex.X 0 ⟶
    (Scheme.Modules.pushforward (pullback.diagonal f)).obj (SheafOfModules.unit _) :=
  r.complex.d 1 0 ≫ r.zeroIso.hom

/-- **The degree-zero term of the complex of external tensor products maps onto `𝒪_Δ`.** This is
exactness of the augmented resolution at degree zero. -/
theorem epi_augmentation : Epi r.augmentation := by
  have hexact : (ShortComplex.mk (r.complex.d 1 0) (r.complex.d 0 0)
      (r.complex.d_comp_d 1 0 0)).Exact :=
    (r.complex.exactAt_iff' 1 0 0 (by simp) (by simp)).1 (r.acyclic 0)
  have hepi : Epi (r.complex.d 1 0) := (ShortComplex.exact_iff_epi _ (by simp)).1 hexact
  exact epi_comp' hepi inferInstance

end OriginalComplex

variable [IsNoetherianRing R] (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f]
  (cover : ∀ M : (pullback f f).Modules, M.IsCoherent → ExternalTensorCover f M)
  (M₀ : (pullback f f).Modules) (hM₀ : M₀.IsCoherent)

/-- The modules whose covers make up the resolution: `M₀` in degree zero and the kernel of the
previous covering map thereafter. -/
def state : ℕ → {M : (pullback f f).Modules // M.IsCoherent}
  | 0 => ⟨M₀, hM₀⟩
  | n + 1 =>
      let C := cover (state n).1 (state n).2
      haveI : (externalTensorProduct f f C.left C.right).IsCoherent :=
        isCoherent_externalTensorProduct f C.left C.right
          C.left_finiteLocallyFree C.right_finiteLocallyFree
      haveI : (state n).1.IsCoherent := (state n).2
      ⟨kernel C.map, SheafOfModules.kernel_isCoherent C.map⟩

/-- The cover chosen at stage `n`. -/
def coverAt (n : ℕ) : ExternalTensorCover f (state f cover M₀ hM₀ n).1 :=
  cover (state f cover M₀ hM₀ n).1 (state f cover M₀ hM₀ n).2

/-- The term of the augmented resolution in degree `n`. -/
def obj : ℕ → (pullback f f).Modules
  | 0 => M₀
  | n + 1 =>
      externalTensorProduct f f (coverAt f cover M₀ hM₀ n).left (coverAt f cover M₀ hM₀ n).right

/-- The differential of the augmented resolution out of degree `n + 1`. -/
def differential (n : ℕ) :
    obj f cover M₀ hM₀ (n + 1) ⟶ obj f cover M₀ hM₀ n :=
  match n with
  | 0 => (coverAt f cover M₀ hM₀ 0).map
  | n + 1 =>
      (coverAt f cover M₀ hM₀ (n + 1)).map ≫ kernel.ι (coverAt f cover M₀ hM₀ n).map

/-- The differential out of degree one is the covering map of the cover at stage zero. -/
theorem differential_zero :
    differential f cover M₀ hM₀ 0 = (coverAt f cover M₀ hM₀ 0).map := rfl

/-- The differential out of degree `n + 2` is the covering map at stage `n + 1` followed by the
inclusion of the kernel of the covering map at stage `n`. -/
theorem differential_succ (n : ℕ) :
    differential f cover M₀ hM₀ (n + 1) =
      (coverAt f cover M₀ hM₀ (n + 1)).map ≫ kernel.ι (coverAt f cover M₀ hM₀ n).map := rfl

/-- Two consecutive differentials compose to zero. -/
theorem differential_comp (n : ℕ) :
    differential f cover M₀ hM₀ (n + 1) ≫ differential f cover M₀ hM₀ n = 0 := by
  cases n with
  | zero =>
      rw [differential_succ, differential_zero]
      exact kernel_comp_eq_zero _ _
  | succ n =>
      rw [differential_succ, differential_succ]
      exact kernel_comp_comp_eq_zero _ _ _

/-- The augmented resolution as a chain complex. -/
def complexOf : ChainComplex (pullback f f).Modules ℕ :=
  ChainComplex.of (obj f cover M₀ hM₀) (differential f cover M₀ hM₀)
    (differential_comp f cover M₀ hM₀)

/-- A short complex `T ⟶ B ⟶ D` whose first map is an epimorphism onto the kernel of the second
is exact. -/
theorem shortComplex_exact_of_epi_to_kernel {C : Type*} [Category C] [Abelian C]
    {A B D T : C} (q : A ⟶ B) (m : B ⟶ D) (hm : Mono m) (e : T ⟶ kernel q) (he : Epi e) :
    (ShortComplex.mk (e ≫ kernel.ι q) (q ≫ m) (by simp)).Exact := by
  have := hm
  have := he
  refine (ShortComplex.exact_iff_epi_kernel_lift _).2 ?_
  have heq : kernel.lift (q ≫ m) (e ≫ kernel.ι q) (by simp) = e ≫ (kernelCompMono q m).inv := by
    apply (cancel_mono (kernel.ι (q ≫ m))).mp
    simp [Category.assoc]
  rw [heq]
  infer_instance

/-- The complex `complexOf` is exact in every degree; in degree zero this says that the
differential out of degree one is an epimorphism onto `M₀`. -/
theorem complexOf_acyclic : (complexOf f cover M₀ hM₀).Acyclic := by
  intro n
  cases n with
  | zero =>
      refine ((complexOf f cover M₀ hM₀).exactAt_iff' (i := 1) (j := 0) 0
        (by simp) (by simp)).2 ?_
      refine (ShortComplex.exact_iff_epi (ShortComplex.mk
        (differential f cover M₀ hM₀ 0) 0 (by simp)) (by simp)).2 ?_
      exact (coverAt f cover M₀ hM₀ 0).epi
  | succ n =>
      refine ((complexOf f cover M₀ hM₀).exactAt_iff' (i := n + 1 + 1) (j := n + 1) n
        (by simp) (by simp)).2 ?_
      simp only [complexOf, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
        ChainComplex.of_X, ChainComplex.of_d]
      change (ShortComplex.mk (differential f cover M₀ hM₀ (n + 1))
        (differential f cover M₀ hM₀ n) (differential_comp f cover M₀ hM₀ n)).Exact
      cases n with
      | zero =>
          change (ShortComplex.mk
            ((coverAt f cover M₀ hM₀ 1).map ≫ kernel.ι (coverAt f cover M₀ hM₀ 0).map)
            ((coverAt f cover M₀ hM₀ 0).map ≫ 𝟙 ((state f cover M₀ hM₀ 0).1))
            (differential_comp f cover M₀ hM₀ 0)).Exact
          exact shortComplex_exact_of_epi_to_kernel (coverAt f cover M₀ hM₀ 0).map _
            (by infer_instance) _ (coverAt f cover M₀ hM₀ 1).epi
      | succ n =>
          change (ShortComplex.mk
            ((coverAt f cover M₀ hM₀ (n + 2)).map ≫
              kernel.ι (coverAt f cover M₀ hM₀ (n + 1)).map)
            ((coverAt f cover M₀ hM₀ (n + 1)).map ≫
              kernel.ι (coverAt f cover M₀ hM₀ n).map)
            (differential_comp f cover M₀ hM₀ (n + 1))).Exact
          exact shortComplex_exact_of_epi_to_kernel (coverAt f cover M₀ hM₀ (n + 1)).map _
            (by change Mono (equalizer.ι _ _); infer_instance) _
            (coverAt f cover M₀ hM₀ (n + 2)).epi

/-- **A resolution of the diagonal built from a supply of external tensor covers.** Covering
`𝒪_Δ`, then the kernel of that cover, and so on, gives an acyclic complex whose degree-zero term
is `𝒪_Δ` and whose positive-degree terms are external tensor products of finite locally free
modules.

Together with [Stacks, Tag 0FZ0], which supplies the covers unconditionally, this is
[Stacks, Tag 0FZ2]. -/
def ofExternalTensorCovers [QuasiCompact f] [IsSeparated f] : DiagonalResolution f :=
  let M₀ : (pullback f f).Modules :=
    (Scheme.Modules.pushforward (pullback.diagonal f)).obj (SheafOfModules.unit _)
  let hM₀ : M₀.IsCoherent := isCoherent_diagonalUnit f
  { complex := complexOf f cover M₀ hM₀
    acyclic := complexOf_acyclic f cover M₀ hM₀
    left := fun i => (coverAt f cover M₀ hM₀ i).left
    right := fun i => (coverAt f cover M₀ hM₀ i).right
    left_finiteLocallyFree := fun i => (coverAt f cover M₀ hM₀ i).left_finiteLocallyFree
    right_finiteLocallyFree := fun i => (coverAt f cover M₀ hM₀ i).right_finiteLocallyFree
    zeroIso := Iso.refl _
    termIso := fun _ => Iso.refl _ }

end DiagonalResolution

/-- **The existence of a resolution of the diagonal, from a supply of external tensor covers.**
Together with [Stacks, Tag 0FZ0] this is [Stacks, Tag 0FZ2]. -/
theorem nonempty_diagonalResolution_of_externalTensorCovers [IsNoetherianRing R]
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (cover : ∀ M : (pullback f f).Modules, M.IsCoherent → ExternalTensorCover f M) :
    Nonempty (DiagonalResolution f) :=
  ⟨DiagonalResolution.ofExternalTensorCovers f cover⟩

end AlgebraicGeometry

end
