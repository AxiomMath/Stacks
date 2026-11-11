module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.AffineMorphismEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.StructureDirectImage
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison
public import StacksFrontier.RingTheory.LocalCohomology.DimensionVanishing.HgroupOfSheafCohomology
public import StacksCore.Tactic.StacksAttribute

/-!
# The genus does not increase along a generically closed finite morphism

Let `k` be a field and let `X` be a proper scheme of dimension at most one over `k`.
[Stacks, Tag 0CE3] asserts that if `f : Y ⟶ X` is a finite morphism which is a closed immersion
over a dense open of `X`, then `dim_k H¹(X, 𝒪_X) ≥ dim_k H¹(Y, 𝒪_Y)`.

The source argues from the four-term exact sequence

`0 ⟶ 𝒢 ⟶ 𝒪_X ⟶ f_*𝒪_Y ⟶ ℱ ⟶ 0`

of modules on `X`, where `𝒢` is the kernel and `ℱ` the cokernel of the comparison map
`𝒪_X ⟶ f_*𝒪_Y`. The sheaf `ℱ` is supported in finitely many closed points, because the
comparison map is an isomorphism over the dense open where `f` is a closed immersion and the
complement of a dense open in a scheme of dimension at most one is a finite set of closed
points; so `H¹(X, ℱ) = 0` by [Stacks, Tag 0AYT] (3). Also `H²(X, 𝒢) = 0` by
[Stacks, Tag 02UZ], the dimension of `X` being at most one. Splitting the four-term sequence at
the coimage of the comparison map into

`0 ⟶ 𝒢 ⟶ 𝒪_X ⟶ coim ⟶ 0`  and  `0 ⟶ coim ⟶ f_*𝒪_Y ⟶ ℱ ⟶ 0`,

the two long exact sequences of cohomology then make `H¹(X, 𝒪_X) ⟶ H¹(X, coim)` and
`H¹(X, coim) ⟶ H¹(X, f_*𝒪_Y)` surjective, hence `H¹(X, 𝒪_X) ⟶ H¹(X, f_*𝒪_Y)` surjective; and
`H¹(X, f_*𝒪_Y) = H¹(Y, 𝒪_Y)` because `f` is affine ([Stacks, Tag 089W]).

This file proves that argument for an affine morphism, with the two vanishing statements and the
finite dimensionality of `H¹(X, 𝒪_X)`, which turns a surjection into an inequality of
dimensions, as inputs. Those three inputs are discharged from the source's hypotheses in
`StacksFrontier/AlgebraicGeometry/Curves/GenusCurve/GenusGoesDownUnconditional.lean`, whose
`AlgebraicGeometry.genus_le_of_isFinite_of_isClosedImmersion_over_dense_open` is
[Stacks, Tag 0CE3] itself.

## Main definitions

* `CategoryTheory.Abelian.cokernelFactorThruCoimageIso`: the cokernel of the monomorphism
  `coim φ ⟶ B` is the cokernel of `φ`.

## Main results

* `CategoryTheory.Abelian.shortExact_cokernelSequence_kernel_ι` and
  `CategoryTheory.Abelian.shortExact_cokernelSequence_factorThruCoimage`: **the four-term exact
  sequence** `0 ⟶ ker φ ⟶ A ⟶ B ⟶ coker φ ⟶ 0` of a morphism `φ : A ⟶ B` in an abelian
  category, split at the coimage of `φ` into two short exact sequences.
* `AlgebraicGeometry.surjective_cohomologyOverFieldMap_f_of_isZero_X₃` and
  `AlgebraicGeometry.surjective_cohomologyOverFieldMap_g_of_isZero_succ_X₁`: the two surjectivity
  statements read off the long exact sequence of cohomology of a short exact sequence of modules.
* `AlgebraicGeometry.surjective_cohomologyOverFieldMap_of_isZero`: **the surjectivity of
  `Hⁿ(X, ℱ) ⟶ Hⁿ(X, 𝒢)` for a morphism `ℱ ⟶ 𝒢` of modules whose cokernel has vanishing `Hⁿ`
  and whose kernel has vanishing `Hⁿ⁺¹`.** This is the step the source calls formal.
* `AlgebraicGeometry.surjective_cohomologyOverFieldMap_structureSheafToPushforward`: the same at
  the comparison map `𝒪_X ⟶ f_*𝒪_Y` in degree one, that is **the surjectivity of
  `H¹(X, 𝒪_X) ⟶ H¹(X, f_*𝒪_Y)`.**
* `AlgebraicGeometry.finrank_cohomologyOverField_le_of_isZero`: the inequality of dimensions that
  surjectivity gives.
* `AlgebraicGeometry.genus_le_of_isAffineHom_of_isZero`: **the inequality
  `dim_k H¹(Y, 𝒪_Y) ≤ dim_k H¹(X, 𝒪_X)`** for an affine `f`, from the two vanishing
  statements and the finite dimensionality of `H¹(X, 𝒪_X)`.
* `AlgebraicGeometry.genus_le_of_isAffineHom_of_isZero_hgroup` and
  `AlgebraicGeometry.genus_le_of_isAffineHom_of_subsingleton_sheafCohomology`: the same with the
  two vanishing hypotheses in the two abelian-group spellings of cohomology, which are the
  spellings in which the vanishing theorems of the library are stated.

## Implementation notes

**What is proved here and where the inputs come from.** Three inputs of the source's proof are
hypotheses of `AlgebraicGeometry.genus_le_of_isAffineHom_of_isZero`, so that the cohomological
step stands on its own for any affine `f`. The library proves each of them under the source's
hypotheses, and `AlgebraicGeometry.genus_le_of_isFinite_of_isClosedImmersion_over_dense_open`
(`StacksFrontier/AlgebraicGeometry/Curves/GenusCurve/GenusGoesDownUnconditional.lean`) assembles
them into [Stacks, Tag 0CE3]:

* `H¹(X, ℱ) = 0` for the cokernel `ℱ` of `𝒪_X ⟶ f_*𝒪_Y`. In the source this is clause (3) of
  [Stacks, Tag 0AYT], applied to a coherent module whose support has dimension at most zero;
  the library has that clause as
  `AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero`. The bound
  on the support is where the hypotheses that `f` is a closed immersion over a dense open and
  that `X` has dimension at most one enter.
* `H²(X, 𝒢) = 0` for the kernel `𝒢`. In the source this is [Stacks, Tag 02UZ]; the library has
  the vanishing by dimension as
  `AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_le`. The variants
  `AlgebraicGeometry.genus_le_of_isAffineHom_of_isZero_hgroup` and
  `AlgebraicGeometry.genus_le_of_isAffineHom_of_subsingleton_sheafCohomology` carry the two
  vanishing hypotheses in the `Hgroup` and in the `CategoryTheory.Sheaf.H` spellings.
* finite dimensionality of `H¹(X, 𝒪_X)` over `k`, which is [Stacks, Tag 02O6] at the base
  `Spec k`; the library has it for a proper morphism as
  `AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper`.

Properness of `X` over `k` and the bound on its dimension are therefore absent from the
statements below: they are used by the source only to produce those three inputs. The
hypothesis that `f` is finite is relaxed to `AlgebraicGeometry.IsAffineHom`, which is all the
comparison [Stacks, Tag 089W] needs, and which `AlgebraicGeometry.IsFinite` extends.

**Splitting the four-term sequence.** The middle object is the coimage
`CategoryTheory.Abelian.coimage φ = cokernel (kernel.ι φ)` rather than the categorical image,
because then both halves are instances of `CategoryTheory.ShortComplex.cokernelSequence` and
their exactness is `CategoryTheory.ShortComplex.cokernelSequence_exact` with nothing added. The
price is that the third term of the second half is `cokernel (factorThruCoimage φ)` rather than
`cokernel φ`; the two are identified by `CategoryTheory.Abelian.cokernelFactorThruCoimageIso`,
which is `CategoryTheory.Limits.cokernelEpiComp` at the factorisation of `φ` through its
coimage, and the identification is applied to the vanishing hypothesis rather than to the short
exact sequence.

**The long exact sequence.** `AlgebraicGeometry.exists_cohomologyOverField_longExactSequence`
states exactness as `Function.Exact` on the underlying maps and quantifies the connecting maps
existentially, so the two surjectivity statements are proved by element chasing: a map whose
target is a zero object is zero, so exactness at that spot says the previous map is onto.

**The two presentations of `H¹(X, 𝒪_X)`.** The genus of [Stacks, Tag 0BY7] is defined from
`AlgebraicGeometry.structureSheafCohomology`, while the long exact sequence and the comparison
along an affine morphism are stated for `AlgebraicGeometry.cohomologyOverField`. The two are
identified by `AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverField`, which is used
once at each end of the inequality.

## References

* [Stacks Project, Tag 0CE3](https://stacks.math.columbia.edu/tag/0CE3)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Abelian

variable {C : Type*} [Category C] [Abelian C] {A B : C}

/-- **The first half of the four-term exact sequence of a morphism**: for `φ : A ⟶ B` in an
abelian category the sequence `0 ⟶ ker φ ⟶ A ⟶ coim φ ⟶ 0` is short exact, the coimage being
the cokernel of the kernel. -/
theorem shortExact_cokernelSequence_kernel_ι (φ : A ⟶ B) :
    (ShortComplex.cokernelSequence (kernel.ι φ)).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := by change Mono (kernel.ι φ); infer_instance

/-- **The second half of the four-term exact sequence of a morphism**: for `φ : A ⟶ B` in an
abelian category the sequence `0 ⟶ coim φ ⟶ B ⟶ coker φ ⟶ 0` is short exact, the third term
being written as the cokernel of the monomorphism `coim φ ⟶ B`. It is the cokernel of `φ` by
`CategoryTheory.Abelian.cokernelFactorThruCoimageIso`. -/
theorem shortExact_cokernelSequence_factorThruCoimage (φ : A ⟶ B) :
    (ShortComplex.cokernelSequence (Abelian.factorThruCoimage φ)).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := by change Mono (Abelian.factorThruCoimage φ); infer_instance

/-- The cokernel of the monomorphism `coim φ ⟶ B` is the cokernel of `φ`: the two agree because
`φ` is that monomorphism precomposed with the epimorphism `A ⟶ coim φ`. -/
def cokernelFactorThruCoimageIso (φ : A ⟶ B) :
    cokernel (Abelian.factorThruCoimage φ) ≅ cokernel φ :=
  (cokernelEpiComp (Abelian.coimage.π φ) (Abelian.factorThruCoimage φ)).symm ≪≫
    cokernelIsoOfEq (Abelian.coimage.fac φ)

end CategoryTheory.Abelian

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))

/-- If the cohomology groups `M ⟶ N ⟶ P` are exact at `N` and `P` is a zero object, then
`M ⟶ N` is onto. -/
private theorem surjective_of_exact_of_isZero {M N P : ModuleCat k} {a : M ⟶ N} {b : N ⟶ P}
    (hab : Function.Exact a b) (h : IsZero P) : Function.Surjective a := by
  have := ModuleCat.subsingleton_of_isZero h
  exact fun y => (hab y).mp (Subsingleton.elim _ _)

/-- **Vanishing of the cohomology of the third term of a short exact sequence makes the map
induced by the first one surjective.** For a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of
modules on a scheme over `k` with `Hⁿ(X, ℱ₃) = 0`, the map `Hⁿ(X, ℱ₁) ⟶ Hⁿ(X, ℱ₂)` is onto. -/
theorem surjective_cohomologyOverFieldMap_f_of_isZero_X₃
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (n : ℕ)
    (h : IsZero (cohomologyOverField k g S.X₃ n)) :
    Function.Surjective (cohomologyOverFieldMap k g S.f n) := by
  obtain ⟨_, _, hfg, _, _⟩ := exists_cohomologyOverField_longExactSequence k g hS
  exact surjective_of_exact_of_isZero k (hfg n) h

/-- **Vanishing of the cohomology of the first term of a short exact sequence one degree up
makes the map induced by the second one surjective.** For a short exact sequence
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of modules on a scheme over `k` with `Hⁿ⁺¹(X, ℱ₁) = 0`, the map
`Hⁿ(X, ℱ₂) ⟶ Hⁿ(X, ℱ₃)` is onto: the next map in the long exact sequence lands in a zero
object. -/
theorem surjective_cohomologyOverFieldMap_g_of_isZero_succ_X₁
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (n : ℕ)
    (h : IsZero (cohomologyOverField k g S.X₁ (n + 1))) :
    Function.Surjective (cohomologyOverFieldMap k g S.g n) := by
  obtain ⟨_, _, _, hgd, _⟩ := exists_cohomologyOverField_longExactSequence k g hS
  exact surjective_of_exact_of_isZero k (hgd n) h

/-- **The formal step of [Stacks, Tag 0CE3].** Let `φ : ℱ ⟶ 𝒢` be a morphism of modules on a
scheme over `k`. If `Hⁿ(X, coker φ) = 0` and `Hⁿ⁺¹(X, ker φ) = 0`, then
`Hⁿ(X, ℱ) ⟶ Hⁿ(X, 𝒢)` is surjective.

The four-term exact sequence `0 ⟶ ker φ ⟶ ℱ ⟶ 𝒢 ⟶ coker φ ⟶ 0` is split at the coimage of `φ`
into two short exact sequences, and each of the two vanishing hypotheses makes one of the two
factors of `Hⁿ(X, φ)` surjective. -/
theorem surjective_cohomologyOverFieldMap_of_isZero {F G : X.Modules} (φ : F ⟶ G) (n : ℕ)
    (hcoker : IsZero (cohomologyOverField k g (cokernel φ) n))
    (hker : IsZero (cohomologyOverField k g (kernel φ) (n + 1))) :
    Function.Surjective (cohomologyOverFieldMap k g φ n) := by
  have h₁ : Function.Surjective (cohomologyOverFieldMap k g (Abelian.coimage.π φ) n) :=
    surjective_cohomologyOverFieldMap_g_of_isZero_succ_X₁ k g
      (Abelian.shortExact_cokernelSequence_kernel_ι φ) n hker
  have hcoker' : IsZero (cohomologyOverField k g (cokernel (Abelian.factorThruCoimage φ)) n) :=
    hcoker.of_iso (cohomologyOverFieldIso k g (Abelian.cokernelFactorThruCoimageIso φ) n)
  have h₂ : Function.Surjective (cohomologyOverFieldMap k g (Abelian.factorThruCoimage φ) n) :=
    surjective_cohomologyOverFieldMap_f_of_isZero_X₃ k g
      (Abelian.shortExact_cokernelSequence_factorThruCoimage φ) n hcoker'
  intro y
  obtain ⟨x, hx⟩ := h₂ y
  obtain ⟨z, hz⟩ := h₁ x
  refine ⟨z, ?_⟩
  rw [← Abelian.coimage.fac φ, cohomologyOverFieldMap_comp]
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rw [hz, hx]

/-- **A surjection of cohomology groups does not increase the dimension.** If
`Hⁿ(X, coker φ) = 0`, `Hⁿ⁺¹(X, ker φ) = 0` and `Hⁿ(X, ℱ)` is finite dimensional over `k`, then
`dim_k Hⁿ(X, 𝒢) ≤ dim_k Hⁿ(X, ℱ)`. -/
theorem finrank_cohomologyOverField_le_of_isZero {F G : X.Modules} (φ : F ⟶ G) (n : ℕ)
    (hfin : FiniteDimensional k (cohomologyOverField k g F n))
    (hcoker : IsZero (cohomologyOverField k g (cokernel φ) n))
    (hker : IsZero (cohomologyOverField k g (kernel φ) (n + 1))) :
    Module.finrank k (cohomologyOverField k g G n) ≤
      Module.finrank k (cohomologyOverField k g F n) :=
  haveI := hfin
  LinearMap.finrank_le_finrank_of_surjective (f := (cohomologyOverFieldMap k g φ n).hom)
    (surjective_cohomologyOverFieldMap_of_isZero k g φ n hcoker hker)

variable {Y : Scheme.{u}}

/-- **The surjectivity of `H¹(X, 𝒪_X) ⟶ H¹(X, f_*𝒪_Y)`**, for the canonical comparison map of a
morphism `f : Y ⟶ X`, given that the cokernel of that map has vanishing `H¹` and its kernel
vanishing `H²`. This is the conclusion the source of [Stacks, Tag 0CE3] draws from the
four-term exact sequence. -/
theorem surjective_cohomologyOverFieldMap_structureSheafToPushforward (f : Y ⟶ X)
    (hcoker : IsZero (cohomologyOverField k g (cokernel (structureSheafToPushforward f)) 1))
    (hker : IsZero (cohomologyOverField k g (kernel (structureSheafToPushforward f)) 2)) :
    Function.Surjective (cohomologyOverFieldMap k g (structureSheafToPushforward f) 1) :=
  surjective_cohomologyOverFieldMap_of_isZero k g (structureSheafToPushforward f) 1 hcoker hker

/-- The genus is the dimension of `H¹(X, 𝒪_X)` in the `cohomologyOverField` spelling. -/
private theorem genus_eq_finrank_cohomologyOverField_structureSheafModule :
    genus g = Module.finrank k (cohomologyOverField k g (structureSheafModule X) 1) := by
  rw [genus_eq_finrank_structureSheafCohomology,
    (structureSheafCohomologyIsoCohomologyOverField k g 1).toLinearEquiv.finrank_eq]

/-- **The cohomological step of [Stacks, Tag 0CE3].** Let `f : Y ⟶ X` be an affine morphism of
schemes over a field `k`, and let `φ : 𝒪_X ⟶ f_*𝒪_Y` be the canonical comparison map. If
`H¹(X, coker φ) = 0`, if `H²(X, ker φ) = 0` and if `H¹(X, 𝒪_X)` is finite dimensional over `k`,
then the genus of `Y` is at most the genus of `X`, that is
`dim_k H¹(Y, 𝒪_Y) ≤ dim_k H¹(X, 𝒪_X)`.

The three hypotheses replace the properness of `X` over `k`, the bound on its dimension and the
hypothesis that `f` is a closed immersion over a dense open, which the source uses only to
produce them. The tag itself, under exactly the source's hypotheses, is
`AlgebraicGeometry.genus_le_of_isFinite_of_isClosedImmersion_over_dense_open`, which discharges
all three. -/
theorem genus_le_of_isAffineHom_of_isZero (f : Y ⟶ X) [IsAffineHom f]
    (hcoker : IsZero (cohomologyOverField k g (cokernel (structureSheafToPushforward f)) 1))
    (hker : IsZero (cohomologyOverField k g (kernel (structureSheafToPushforward f)) 2))
    (hfin : FiniteDimensional k (cohomologyOverField k g (structureSheafModule X) 1)) :
    genus (f ≫ g) ≤ genus g := by
  have hY : genus (f ≫ g) =
      Module.finrank k (cohomologyOverField k g (pushedForwardStructureSheaf f) 1) := by
    rw [genus_eq_finrank_cohomologyOverField_structureSheafModule k (f ≫ g),
      finrank_cohomologyOverField_pushforward_of_isAffineHom k f g (structureSheafModule Y) 1]
  rw [genus_eq_finrank_cohomologyOverField_structureSheafModule k g, hY]
  exact finrank_cohomologyOverField_le_of_isZero k g (structureSheafToPushforward f) 1 hfin
    hcoker hker

/-- **The cohomological step of [Stacks, Tag 0CE3], with its two vanishing inputs in the
abelian-group spelling of cohomology.** This is
`AlgebraicGeometry.genus_le_of_isAffineHom_of_isZero` with the two vanishing hypotheses stated
for `Hgroup`, the right derived functor of the abelian-group-valued sections, which is the
spelling in which the vanishing theorems of the library are stated. -/
theorem genus_le_of_isAffineHom_of_isZero_hgroup (f : Y ⟶ X) [IsAffineHom f]
    (hcoker : IsZero
      (Hgroup X.ringCatSheaf ⊤ 1 (cokernel (structureSheafToPushforward f))))
    (hker : IsZero
      (Hgroup X.ringCatSheaf ⊤ 2 (kernel (structureSheafToPushforward f))))
    (hfin : FiniteDimensional k (cohomologyOverField k g (structureSheafModule X) 1)) :
    genus (f ≫ g) ≤ genus g :=
  genus_le_of_isAffineHom_of_isZero k g f
    ((isZero_cohomologyOverField_iff_isZero_hgroup k g _ 1).2 hcoker)
    ((isZero_cohomologyOverField_iff_isZero_hgroup k g _ 2).2 hker) hfin

/-- **The cohomological step of [Stacks, Tag 0CE3], with its two vanishing inputs in the
`Ext`-theoretic spelling of cohomology.** This is
`AlgebraicGeometry.genus_le_of_isAffineHom_of_isZero` with the two vanishing hypotheses stated
for `CategoryTheory.Sheaf.H` of the underlying abelian sheaf, which is the spelling of
[Stacks, Tag 02UZ] and of the vanishing theorems for abelian sheaves on a space of bounded
dimension. The transport is
`Stacks.LocalCohomology.isZero_Hgroup_of_subsingleton_sheafCohomology`, which is why both
degrees are required to be positive and the two hypotheses are stated in degrees one and two. -/
theorem genus_le_of_isAffineHom_of_subsingleton_sheafCohomology (f : Y ⟶ X)
    [IsAffineHom f]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (hcoker : Subsingleton (Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (cokernel (structureSheafToPushforward f))) 1))
    (hker : Subsingleton (Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (kernel (structureSheafToPushforward f))) 2))
    (hfin : FiniteDimensional k (cohomologyOverField k g (structureSheafModule X) 1)) :
    genus (f ≫ g) ≤ genus g :=
  genus_le_of_isAffineHom_of_isZero_hgroup k g f
    (Stacks.LocalCohomology.isZero_Hgroup_of_subsingleton_sheafCohomology _ 1 one_pos hcoker)
    (Stacks.LocalCohomology.isZero_Hgroup_of_subsingleton_sheafCohomology _ 2 two_pos hker) hfin

end AlgebraicGeometry

end
