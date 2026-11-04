module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraModule
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafUnitSections
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorSections
public import StacksFrontier.AlgebraicGeometry.SubmodulePrimitives.Image
public import StacksFrontier.AlgebraicGeometry.Modules.SubobjectSubmodule
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.TensorOfGeneratorTorsors

/-!
# The ideal-power multiple subsheaf commutes with twisting

Let `X` be a scheme, `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals, `F` an `𝒪_X`-module and
`ℐⁿF ⊆ F` the subsheaf `Stacks.Blowup.reesMultiple` of ideal-power multiples. For a second
`𝒪_X`-module `G` the inclusion `ℐⁿF ⟶ F` tensors to a morphism

`(ℐⁿF) ⊗ G ⟶ F ⊗ G`,

and this file identifies its image: it is the subsheaf `ℐⁿ(F ⊗ G)` of `F ⊗ G`, for an
*arbitrary* `G`. When `G` is invertible — in particular when `G = L^{⊗ d}` is a tensor power of
an invertible module, so that `F ⊗ G` is the twist `F(d)` — the morphism is a monomorphism, so
its source is identified with its image and the identification

`(ℐⁿF)(d) ≅ ℐⁿ(F(d))`

is an isomorphism, compatible with the two inclusions into `F(d)`.

## Main definitions

* `Stacks.Blowup.reesMultipleTensorHom`: the morphism `(ℐⁿF) ⊗ G ⟶ F ⊗ G` obtained by tensoring
  the inclusion of `ℐⁿF` with the identity of `G`.
* `Stacks.Blowup.reesMultipleTensorIso`: for `G` invertible, the comparison
  `(ℐⁿF) ⊗ G ≅ ℐⁿ(F ⊗ G)`.
* `Stacks.Blowup.reesMultipleTwistIso`: the same at `G = L^{⊗ d}`, i.e. the commutation of `ℐⁿ·`
  with the `d`-th twist by an invertible module `L`.

## Main results

* `Stacks.Blowup.toTensorSheafSection_mem_reesMultiple`: a product of sections whose left factor
  lies in `ℐⁿF` lies in `ℐⁿ(F ⊗ G)`.
* `Stacks.Blowup.ofHom_reesMultipleTensorHom`: **the image of `(ℐⁿF) ⊗ G` in `F ⊗ G` is
  `ℐⁿ(F ⊗ G)`**, an equality of subsheaves of `F ⊗ G`, with no hypothesis on `G` at all. This is
  the real content; both the isomorphism and its compatibility are read off it.
* `Stacks.Blowup.reesMultipleTensorIso_hom_ι` and
  `Stacks.Blowup.reesMultipleTwistIso_hom_ι`: the comparison commutes with the two inclusions
  into `F ⊗ G`, resp. into `F(d)`. Without this the isomorphism says nothing a consumer can use:
  what is needed downstream is the identification *inside* `F(d)`, not an abstract isomorphism
  class.
* `Stacks.Blowup.reesMultipleTensorIso_hom_comp` and
  `Stacks.Blowup.reesMultipleTwistIso_hom_comp`: the comparison forms a commuting square with
  the inclusions `ℐᵐ ⊆ ℐⁿ` on the two sides. This is what carries the comparison to the
  ideal-power layers `ℐⁿ/ℐⁿ⁺¹`.

## Implementation notes

**Why the twist cannot be absorbed into the construction.** One is tempted to skip this
commutation entirely: instantiate the ideal-power filtration at `F := F(d)` from the start, and
the ideal-power layers of the twisted module come out on the nose. That does not work, and the
obstruction is a quantifier order, not a convenience. Part (2) of [Stacks, Tag 0897] quantifies
its exponent `d₀` *after* the whole graded module has been fixed; a graded module whose
definition already mentions `d` would therefore make the choice of `d` depend on a `d₀` that is
only produced once `d` has been chosen — the choice of `d` would precede itself. The same quantifier order
is what makes Serre vanishing in the form of [Stacks, Tag 0B5T] clause (4) useless here: there
the `∃ d₀` stands after the coherent module, so applying it to each graded piece separately
yields a `d₀(n)` for every `n` rather than one `d₀` serving all `n` at once. This is the
reason the commutation has to be proved as a statement about subsheaves of `F(d)`, and not an accident
of how the filtration happens to be spelled.

**The second, sharper reason: the twist sits on the wrong side of the layer.** The consumer of
[Stacks, Tag 0D2M] has a hypothesis about the ideal-power layer of the *twisted* module,
`𝔪ⁿ(ℱ(d))/𝔪ⁿ⁺¹(ℱ(d))`. Every vanishing theorem available to feed it concludes instead about the
*twist of the layer*: Tag 0884 as formalized here
(`Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule`) and part (2) of Tag
0897 both produce `Ker(𝓕_{n+1} ⟶ 𝓕_n) ⊗ L^{⊗ d}`, that is `(𝔪ⁿℱ/𝔪ⁿ⁺¹ℱ)(d)`, the layer of the
untwisted system twisted afterwards. Converting the one into the other *is* the present
statement, in its layer form `𝓘ⁿ(ℱ(d))/𝓘ⁿ⁺¹(ℱ(d)) ≅ (𝓘ⁿℱ/𝓘ⁿ⁺¹ℱ)(d)`, which is the degreewise
consequence of the subsheaf comparison at `n` and at `n + 1`. So the commutation is not a
convenience: with the twist on the outside of the layer, no available vanishing theorem reaches the
hypothesis at all. The input a consumer needs to pass to the layer is
`reesMultipleTensorIso_hom_comp` below, which says the comparison intertwines the two inclusions
`𝓘ⁿ⁺¹ ⊆ 𝓘ⁿ` on the two sides; the cokernel comparison is then the exactness of tensoring by an
invertible module.

**Why an equality of subsheaves, and not just an isomorphism.** Both inclusions of the two
subsheaves `ofHom (reesMultipleTensorHom)` and `reesMultiple` into `F ⊗ G` are available, so the
strongest statement is their equality in the lattice of subsheaves; the isomorphism is then the
comparison of a monomorphism with its image (`imageIso`) followed by the reindexing along that
equality, and the compatibility with the inclusions is `imageIso_hom_imageModuleι` together with
`submoduleEqToIso_hom_ι`. Stating the equality first is also what keeps the two containments
free of hypotheses: neither needs `G` invertible, and neither needs quasi-coherence of `F` or of
`G`.

**No quasi-coherence hypothesis.** The local description of the sections of a tensor product
used here is that a local section is, on a covering sieve, a finite sum of pure tensors
(`Stacks.SheafOfModules.TensorUnit.exists_sieve_sum_toTensorSheafSection`), which holds for
arbitrary sheaves of modules. The affine section formula
`Stacks.SectionTensorFormula.bijective_tensorSectionLinear` would have forced
`[F.IsQuasicoherent]` and `[G.IsQuasicoherent]` and is not used.

**Degrees.** Nothing has to be said about negative `n`: there every generator of `ℐⁿF` is zero,
so both subsheaves are the bottom one and the statements above are vacuously the equality of
two zero subsheaves. The proofs never split on the sign of `n`.

**Spellings.** The tensor product of `𝒪_X`-modules has two definitionally equal spellings in
this development: `Stacks.RelativeVeryAmple.tensorModules`, which is what the twists
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.twistModule` and the functor
`tensorRightModules` are written with, and
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, which is what the section-level API
(`toTensorSheafSection` and its bilinearity and restriction laws) is written with. They agree by
`rfl`, and the statements below use the first while the proofs use the second; the crossing
happens only at `exact`, never inside a rewrite. For the same reason the two additivity lemmas
at the head of the file are stated over a ringed space: with `X.toRingedSpace` substituted for
the ringed space, instance search is never asked to recognise `X.toRingedSpace.presheaf` as
`X.presheaf`, which it cannot do.

**No Stacks attribute.** This commutation is a step inside the proof of [Stacks, Tag 0D2M]
rather than a numbered result of the Stacks project, so no `@[stacks ...]` attribute is
attached.

## References

* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 02O7](https://stacks.math.columbia.edu/tag/02O7)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.Blowup

open Stacks.Ample (IsInvertibleModule tensorPowModule)
open Stacks.RelativeVeryAmple (tensorModules)
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence (tensorRightModules twistModule)
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection toTensorSheafSection_add
  tensorSheafMap_app_toTensorSheafSection)
open Stacks.SheafOfModules.TensorUnit (exists_sieve_sum_toTensorSheafSection)
open Stacks.Cohomology.Generators (toTensorSheafSection_smul_left toTensorSheafSection_restrict)
open Stacks.AlgebraicGeometry.SubmodulePrimitives (ofHom mem_ofHom_iff imageModule imageModuleι
  imageIso)

variable {X : Scheme.{u}}

attribute [local instance] Stacks.Algebraization.sectionsModuleΓSheaf
  Stacks.Algebraization.sectionsModuleΓ Stacks.Algebraization.monoSubmoduleι

/-! ### Bilinearity of the comparison into the tensor product sheaf -/

/-- Additivity of `toTensorSheafSection` in the left factor of a pure tensor, stated over a
ringed space so that the two spellings of the structure sheaf of a scheme do not have to meet
during instance search. -/
private theorem toTensorSheafSection_add_tmul (Y : RingedSpace.{u, u})
    (A B : SheafOfModules.{u} (structureSheafRing Y)) (V : Opens Y.carrier)
    (x y : A.val.obj (op V)) (t : B.val.obj (op V)) :
    toTensorSheafSection Y A B (op V) ((x + y) ⊗ₜ[Y.presheaf.obj (op V)] t) =
      toTensorSheafSection Y A B (op V) (x ⊗ₜ[Y.presheaf.obj (op V)] t) +
        toTensorSheafSection Y A B (op V) (y ⊗ₜ[Y.presheaf.obj (op V)] t) :=
  (congrArg (toTensorSheafSection Y A B (op V)) (TensorProduct.add_tmul x y t)).trans
    (toTensorSheafSection_add Y A B (op V) _ _)

/-- The comparison into the tensor product sheaf kills a pure tensor with zero left factor.

Stated and proved in term mode.  The comparison is the component of
`Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit`, so it sends `0` to `0` by
`map_zero`;  a goal naming the sections of a `sheafTensor` is not type-correct under `implicit`
transparency — the structure sheaf of the ringed space reaches the topology `sheafTensor` is taken
over only after both spellings unfold — so `rw` cannot build a motive on it, and would discard the
rewrite rather than fail. -/
private theorem toTensorSheafSection_zero_tmul (Y : RingedSpace.{u, u})
    (A B : SheafOfModules.{u} (structureSheafRing Y)) (V : Opens Y.carrier)
    (t : B.val.obj (op V)) :
    toTensorSheafSection Y A B (op V)
      ((0 : A.val.obj (op V)) ⊗ₜ[Y.presheaf.obj (op V)] t) = 0 :=
  (congrArg (toTensorSheafSection Y A B (op V)) (TensorProduct.zero_tmul _ t)).trans
    (map_zero ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit Y
      (PresheafOfModules.tensorObj (O := Y.presheaf) A.val B.val)).app (op V)).hom)

/-! ### A pure tensor whose left factor is an ideal multiple -/

/-- Membership transfers backwards along an equality. -/
private theorem mem_of_eq_of_mem {α γ : Type*} [Membership α γ] {S : γ} {z w : α} (h : w = z)
    (hw : w ∈ S) : z ∈ S :=
  h ▸ hw

/-- A product of sections whose left factor lies in the span of the degree-`n` generators of
`ℐⁿF` over `V` lies in the span of the degree-`n` generators of `ℐⁿ(F ⊗ G)` over `V`: the
generators are carried to generators because a scalar passes across the tensor sign. -/
public theorem toTensorSheafSection_mem_reesMultipleSpan (I : X.IdealSheafData) (n : ℤ)
    (F G : X.Modules) (V : X.Opens) (t : G.val.obj (op V))
    {m : F.val.obj (op V)} (hm : m ∈ reesMultipleSpan I n F V) :
    toTensorSheafSection X.toRingedSpace F G (op V)
        (m ⊗ₜ[X.presheaf.obj (op V)] t) ∈ reesMultipleSpan I n (tensorModules X F G) V := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨r, m₀, rfl⟩ := hx
      exact mem_of_eq_of_mem
        (toTensorSheafSection_smul_left X.toRingedSpace F G V (reesPieceAmbient I n V r) m₀ t).symm
        (smul_mem_reesMultipleSpan I n (tensorModules X F G) V r _)
  | zero =>
      exact mem_of_eq_of_mem
        (toTensorSheafSection_zero_tmul X.toRingedSpace F G V t).symm (Submodule.zero_mem _)
  | add x y _ _ hx hy =>
      exact mem_of_eq_of_mem
        (toTensorSheafSection_add_tmul X.toRingedSpace F G V x y t).symm
        (Submodule.add_mem _ hx hy)
  | smul a x _ hx =>
      exact mem_of_eq_of_mem
        (toTensorSheafSection_smul_left X.toRingedSpace F G V a x t).symm
        (Submodule.smul_mem _ a hx)

/-- **A product of sections whose left factor lies in `ℐⁿF` lies in `ℐⁿ(F ⊗ G)`.** Membership
in `ℐⁿF` is local, and locally the left factor is in the span of the generators, where
`toTensorSheafSection_mem_reesMultipleSpan` applies. -/
public theorem toTensorSheafSection_mem_reesMultiple (I : X.IdealSheafData) (n : ℤ)
    (F G : X.Modules) (U : X.Opens) (t : G.val.obj (op U))
    {m : F.val.obj (op U)} (hm : m ∈ (reesMultiple I n F).toSubmodule.obj (op U)) :
    toTensorSheafSection X.toRingedSpace F G (op U)
        (m ⊗ₜ[X.presheaf.obj (op U)] t) ∈
      (reesMultiple I n (tensorModules X F G)).toSubmodule.obj (op U) := by
  intro x hx
  obtain ⟨V, hV, hxV, hmV⟩ := hm x hx
  refine ⟨V, hV, hxV, ?_⟩
  refine mem_of_eq_of_mem (toTensorSheafSection_restrict X.toRingedSpace F G hV m t).symm ?_
  exact toTensorSheafSection_mem_reesMultipleSpan I n F G V _ hmV

/-! ### The image of `(ℐⁿF) ⊗ G` in `F ⊗ G` is `ℐⁿ(F ⊗ G)` -/

/-- The morphism `(ℐⁿF) ⊗ G ⟶ F ⊗ G` obtained by tensoring the inclusion of `ℐⁿF` with the
identity of `G`. -/
public abbrev reesMultipleTensorHom (I : X.IdealSheafData) (n : ℤ) (F G : X.Modules) :
    (tensorRightModules X G).obj ((reesMultiple I n F).toSheafOfModules : X.Modules) ⟶
      tensorModules X F G :=
  (tensorRightModules X G).map ((reesMultiple I n F).ι : _ ⟶ F)

/-- **`(ℐⁿF) ⊗ G ⟶ F ⊗ G` on the section of a pure tensor** is the section of the pure tensor of
the images. `Stacks.Blowup.reesMultipleTensorHom` is the right-tensor endofunctor applied to the
inclusion, which `Stacks.Algebraization.tensorRightModules_map` identifies with the tensor product
of the inclusion and the identity; on that one the value is
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection`. -/
private theorem reesMultipleTensorHom_app_toTensorSheafSection (I : X.IdealSheafData) (n : ℤ)
    (F G : X.Modules) (V : X.Opens)
    (a : ((reesMultiple I n F).toSheafOfModules : X.Modules).val.obj (op V))
    (b : G.val.obj (op V)) :
    (ConcreteCategory.hom (Scheme.Modules.Hom.app (reesMultipleTensorHom I n F G) V))
        (toTensorSheafSection X.toRingedSpace ((reesMultiple I n F).toSheafOfModules) G (op V)
          (a ⊗ₜ[X.presheaf.obj (op V)] b)) =
      toTensorSheafSection X.toRingedSpace F G (op V)
        ((ConcreteCategory.hom ((reesMultiple I n F).ι.val.app (op V))) a
          ⊗ₜ[X.presheaf.obj (op V)]
          (ConcreteCategory.hom ((𝟙 G : G ⟶ G).val.app (op V))) b) :=
  (congrArg (fun φ : (tensorRightModules X G).obj
        ((reesMultiple I n F).toSheafOfModules : X.Modules) ⟶ tensorModules X F G =>
      (ConcreteCategory.hom (Scheme.Modules.Hom.app φ V))
        (toTensorSheafSection X.toRingedSpace ((reesMultiple I n F).toSheafOfModules) G (op V)
          (a ⊗ₜ[X.presheaf.obj (op V)] b)))
    (Stacks.Algebraization.tensorRightModules_map X G (reesMultiple I n F).ι)).trans
  (tensorSheafMap_app_toTensorSheafSection X.toRingedSpace
    ((reesMultiple I n F).toSheafOfModules) G F G (reesMultiple I n F).ι (𝟙 G) V a b)

/-- Every value of `(ℐⁿF) ⊗ G ⟶ F ⊗ G` on local sections lies in `ℐⁿ(F ⊗ G)`: a local section
of `(ℐⁿF) ⊗ G` is locally a finite sum of pure tensors whose left factors are sections of
`ℐⁿF`, and those are carried to sections of `ℐⁿ(F ⊗ G)` by
`toTensorSheafSection_mem_reesMultiple`. -/
public theorem ofHom_reesMultipleTensorHom_le (I : X.IdealSheafData) (n : ℤ) (F G : X.Modules) :
    ofHom (reesMultipleTensorHom I n F G) ≤ reesMultiple I n (tensorModules X F G) := by
  intro U s hs
  obtain ⟨W, rfl⟩ : ∃ W : X.Opens, op W = U := ⟨U.unop, rfl⟩
  refine mem_submodule_of_cover (reesMultiple I n (tensorModules X F G)) W s ?_
  intro x hx
  obtain ⟨V, hVW, hxV, t, ht⟩ := (mem_ofHom_iff (reesMultipleTensorHom I n F G) s).1 hs x hx
  obtain ⟨S, hS, hsum⟩ := exists_sieve_sum_toTensorSheafSection X.toRingedSpace
    ((reesMultiple I n F).toSheafOfModules) G V t
  obtain ⟨V', k, hk, hxV'⟩ := (Opens.mem_grothendieckTopology _).1 hS x hxV
  obtain ⟨p, a, b, heq⟩ := hsum k hk
  refine ⟨V', (leOfHom k).trans hVW, hxV', ?_⟩
  have hres : (reesMultipleTensorHom I n F G).app V'
        (Stacks.restr ((tensorRightModules X G).obj
          ((reesMultiple I n F).toSheafOfModules : X.Modules)).val
            (homOfLE (leOfHom k)).op t) =
      Stacks.restr (tensorModules X F G).val (homOfLE ((leOfHom k).trans hVW)).op s := by
    refine Eq.trans (PresheafOfModules.naturality_apply
      (reesMultipleTensorHom I n F G).val (homOfLE (leOfHom k)).op t) ?_
    refine Eq.trans (congrArg
      (fun z ↦ Stacks.restr (tensorModules X F G).val (homOfLE (leOfHom k)).op z) ht) ?_
    exact restr_restr_opens (tensorModules X F G) hVW (leOfHom k) s
  have hrest : Stacks.restr ((tensorRightModules X G).obj
      ((reesMultiple I n F).toSheafOfModules : X.Modules)).val (homOfLE (leOfHom k)).op t =
      ∑ j, toTensorSheafSection X.toRingedSpace ((reesMultiple I n F).toSheafOfModules) G (op V')
        (a j ⊗ₜ[X.presheaf.obj (op V')] b j) := by
    refine Eq.trans ?_ heq
    exact congrArg (fun g ↦ Stacks.restr ((tensorRightModules X G).obj
      ((reesMultiple I n F).toSheafOfModules : X.Modules)).val g t) (Subsingleton.elim _ _)
  rw [← hres, hrest]
  refine mem_of_eq_of_mem
    (map_sum (ConcreteCategory.hom ((reesMultipleTensorHom I n F G).app V')) _ Finset.univ).symm ?_
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  refine mem_of_eq_of_mem
    (reesMultipleTensorHom_app_toTensorSheafSection I n F G V' (a j) (b j)).symm ?_
  exact toTensorSheafSection_mem_reesMultiple I n F G V' _ (a j).2

/-- **`ℐⁿ(F ⊗ G)` is contained in the image of `(ℐⁿF) ⊗ G`.** By the universal property of
`ℐⁿ(F ⊗ G)` it is enough to treat a product `r · m` of a section `r` of `ℐⁿ` with a section `m`
of `F ⊗ G`; locally `m` is a finite sum of pure tensors `a ⊗ b`, and `r · m` is then the image
of the corresponding sum of pure tensors `(r · a) ⊗ b` of `(ℐⁿF) ⊗ G`. -/
public theorem reesMultiple_le_ofHom_reesMultipleTensorHom (I : X.IdealSheafData) (n : ℤ)
    (F G : X.Modules) :
    reesMultiple I n (tensorModules X F G) ≤ ofHom (reesMultipleTensorHom I n F G) := by
  refine (reesMultiple_le_iff I n (tensorModules X F G)
    (ofHom (reesMultipleTensorHom I n F G))).2 ?_
  intro U r m
  refine (mem_ofHom_iff (reesMultipleTensorHom I n F G) _).2 ?_
  intro x hx
  obtain ⟨S, hS, hsum⟩ := exists_sieve_sum_toTensorSheafSection X.toRingedSpace F G U m
  obtain ⟨V, k, hk, hxV⟩ := (Opens.mem_grothendieckTopology _).1 hS x hx
  obtain ⟨p, a, b, heq⟩ := hsum k hk
  have hrV : Stacks.restr (tensorModules X F G).val (homOfLE (leOfHom k)).op m =
      ∑ j, toTensorSheafSection X.toRingedSpace F G (op V)
        (a j ⊗ₜ[X.presheaf.obj (op V)] b j) := by
    refine Eq.trans ?_ heq
    exact congrArg (fun g ↦ Stacks.restr (tensorModules X F G).val g m)
      (Subsingleton.elim _ _)
  refine ⟨V, leOfHom k, hxV, ∑ j, toTensorSheafSection X.toRingedSpace
    ((reesMultiple I n F).toSheafOfModules) G (op V)
      ((⟨reesPieceAmbient I n V (Stacks.restr (reesPiece I n).val (homOfLE (leOfHom k)).op r) •
        a j, smul_mem_reesMultiple I n F V _ (a j)⟩ :
          ((reesMultiple I n F).toSheafOfModules).val.obj (op V)) ⊗ₜ[X.presheaf.obj (op V)]
        b j), ?_⟩
  have hterm : ∀ j : Fin p, (reesMultipleTensorHom I n F G).app V
      (toTensorSheafSection X.toRingedSpace ((reesMultiple I n F).toSheafOfModules) G (op V)
        ((⟨reesPieceAmbient I n V (Stacks.restr (reesPiece I n).val (homOfLE (leOfHom k)).op r) •
          a j, smul_mem_reesMultiple I n F V _ (a j)⟩ :
            ((reesMultiple I n F).toSheafOfModules).val.obj (op V)) ⊗ₜ[X.presheaf.obj (op V)]
          b j)) =
      reesPieceAmbient I n V (Stacks.restr (reesPiece I n).val (homOfLE (leOfHom k)).op r) •
        @id ((tensorModules X F G).val.obj (op V)) (toTensorSheafSection X.toRingedSpace F G
          (op V) (a j ⊗ₜ[X.presheaf.obj (op V)] b j)) := by
    intro j
    refine Eq.trans (reesMultipleTensorHom_app_toTensorSheafSection I n F G V _ (b j)) ?_
    exact toTensorSheafSection_smul_left X.toRingedSpace F G V _ (a j) (b j)
  refine Eq.trans (map_sum (ConcreteCategory.hom
    ((reesMultipleTensorHom I n F G).app V)) _ Finset.univ) ?_
  refine Eq.trans (Finset.sum_congr rfl fun j _ ↦ hterm j) ?_
  refine Eq.trans (Finset.smul_sum).symm ?_
  refine Eq.trans (congrArg (fun z ↦ reesPieceAmbient I n V
    (Stacks.restr (reesPiece I n).val (homOfLE (leOfHom k)).op r) • z) hrV.symm) ?_
  refine Eq.trans (congrArg (fun c ↦ c •
    Stacks.restr (tensorModules X F G).val (homOfLE (leOfHom k)).op m)
    (reesPieceAmbient_restr I n (leOfHom k) r)) ?_
  exact (restr_smul_gamma (tensorModules X F G) (leOfHom k) (reesPieceAmbient I n U r) m).symm

/-- **The image of `(ℐⁿF) ⊗ G` in `F ⊗ G` is exactly `ℐⁿ(F ⊗ G)`**, for an arbitrary
`𝒪_X`-module `G`.  This is the equality of subsheaves of `F ⊗ G` from which the comparison
isomorphism below is read off. -/
public theorem ofHom_reesMultipleTensorHom (I : X.IdealSheafData) (n : ℤ) (F G : X.Modules) :
    ofHom (reesMultipleTensorHom I n F G) = reesMultiple I n (tensorModules X F G) :=
  le_antisymm (ofHom_reesMultipleTensorHom_le I n F G)
    (reesMultiple_le_ofHom_reesMultipleTensorHom I n F G)

/-! ### The comparison isomorphism -/

/-- The isomorphism of the modules of two equal subsheaves carries one inclusion to the other. -/
private theorem submoduleEqToIso_hom_ι {M : X.Modules} {N₁ N₂ : M.Submodule} (h : N₁ = N₂) :
    (eqToIso (congrArg (fun N : M.Submodule ↦ (N.toSheafOfModules : X.Modules)) h)).hom ≫ N₂.ι
      = N₁.ι := by
  subst h
  exact Category.id_comp _

/-- **Tensoring the inclusion `ℐⁿF ⟶ F` on the right by an invertible module is a
monomorphism**: tensoring by an invertible module is an equivalence, hence a right adjoint,
hence preserves monomorphisms. -/
public instance mono_reesMultipleTensorHom (I : X.IdealSheafData) (n : ℤ) (F G : X.Modules)
    [IsInvertibleModule X G] : Mono (reesMultipleTensorHom I n F G) := by
  have : (tensorRightModules X G).IsEquivalence :=
    Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule X G
  have : (tensorRightModules X G).IsRightAdjoint :=
    ((tensorRightModules X G).asEquivalence.symm.toAdjunction).isRightAdjoint
  have : Mono ((reesMultiple I n F).ι : _ ⟶ F) := Stacks.Algebraization.monoSubmoduleι _
  exact Functor.map_mono (tensorRightModules X G) ((reesMultiple I n F).ι : _ ⟶ F)

/-- **The ideal-power multiple subsheaf commutes with tensoring by an invertible module:**
`(ℐⁿF) ⊗ G ≅ ℐⁿ(F ⊗ G)` for `G` invertible.  The underlying fact is the equality of subsheaves
`ofHom_reesMultipleTensorHom`; invertibility of `G` enters only to make `(ℐⁿF) ⊗ G ⟶ F ⊗ G` a
monomorphism, so that its source is identified with its image. -/
public def reesMultipleTensorIso (I : X.IdealSheafData) (n : ℤ) (F G : X.Modules)
    [IsInvertibleModule X G] :
    (tensorRightModules X G).obj ((reesMultiple I n F).toSheafOfModules : X.Modules) ≅
      ((reesMultiple I n (tensorModules X F G)).toSheafOfModules : X.Modules) :=
  imageIso (reesMultipleTensorHom I n F G) ≪≫
    eqToIso (congrArg (fun N : (tensorModules X F G).Submodule ↦
      (N.toSheafOfModules : X.Modules)) (ofHom_reesMultipleTensorHom I n F G))

/-- **The comparison isomorphism commutes with the two inclusions into `F ⊗ G`**: this is what
identifies it, and what makes it a statement about the subsheaf `ℐⁿ(F ⊗ G)` rather than about an
abstract isomorphism class. -/
@[reassoc]
public theorem reesMultipleTensorIso_hom_ι (I : X.IdealSheafData) (n : ℤ) (F G : X.Modules)
    [IsInvertibleModule X G] :
    (reesMultipleTensorIso I n F G).hom ≫ (reesMultiple I n (tensorModules X F G)).ι =
      (tensorRightModules X G).map ((reesMultiple I n F).ι : _ ⟶ F) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ (imageIso (reesMultipleTensorHom I n F G)).hom ≫ z)
        (submoduleEqToIso_hom_ι (ofHom_reesMultipleTensorHom I n F G))).trans
      (Stacks.AlgebraicGeometry.SubmodulePrimitives.imageIso_hom_imageModuleι
        (reesMultipleTensorHom I n F G)))

/-- **The comparison intertwines the inclusions of one ideal-power subsheaf into another.** If
`u` realises `ℐᵐF ⊆ ℐⁿF` inside `F` and `v` realises `ℐᵐ(F ⊗ G) ⊆ ℐⁿ(F ⊗ G)` inside `F ⊗ G`,
then the two comparisons form a commuting square with `u ⊗ G` and `v`. The two inclusions are
taken as data together with the equations identifying them, so that the lemma applies to any
spelling of the inclusion of subsheaves (for the degrees `n ≤ m` of
`Stacks.Blowup.reesMultiple_le_reesMultiple_of_le` both are the morphism of the containment).

This is the input for passing the comparison to the layers `ℐⁿ(F ⊗ G)/ℐⁿ⁺¹(F ⊗ G)`: having the
square, the comparison of the cokernels is the exactness of tensoring by an invertible module. -/
public theorem reesMultipleTensorIso_hom_comp (I : X.IdealSheafData) (n m : ℤ)
    (F G : X.Modules) [IsInvertibleModule X G]
    (u : (((reesMultiple I m F).toSheafOfModules : X.Modules)) ⟶
      ((reesMultiple I n F).toSheafOfModules : X.Modules))
    (hu : u ≫ ((reesMultiple I n F).ι : _ ⟶ F) = (reesMultiple I m F).ι)
    (v : (((reesMultiple I m (tensorModules X F G)).toSheafOfModules : X.Modules)) ⟶
      ((reesMultiple I n (tensorModules X F G)).toSheafOfModules : X.Modules))
    (hv : v ≫ ((reesMultiple I n (tensorModules X F G)).ι : _ ⟶ tensorModules X F G) =
      (reesMultiple I m (tensorModules X F G)).ι) :
    (reesMultipleTensorIso I m F G).hom ≫ v =
      (tensorRightModules X G).map u ≫ (reesMultipleTensorIso I n F G).hom :=
  (cancel_mono ((reesMultiple I n (tensorModules X F G)).ι :
      _ ⟶ tensorModules X F G)).1
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ (reesMultipleTensorIso I m F G).hom ≫ z) hv).trans
        ((reesMultipleTensorIso_hom_ι I m F G).trans
          ((congrArg (fun w : (((reesMultiple I m F).toSheafOfModules : X.Modules)) ⟶ F ↦
              (tensorRightModules X G).map w) hu).symm.trans
            ((Functor.map_comp (tensorRightModules X G) u
                ((reesMultiple I n F).ι : _ ⟶ F)).trans
              (((congrArg (fun z ↦ (tensorRightModules X G).map u ≫ z)
                  (reesMultipleTensorIso_hom_ι I n F G)).symm).trans
                (Category.assoc _ _ _).symm))))))

/-! ### The twist -/

/-- **Forming the ideal-power multiple subsheaf commutes with twisting by an invertible
module:** `(ℐⁿF)(d) ≅ ℐⁿ(F(d))` for every integer `d` and every `n`.  This is
`reesMultipleTensorIso` at `G = L^{⊗ d}`, which is invertible. -/
public def reesMultipleTwistIso (J : X.IdealSheafData) (L : X.Modules)
    [IsInvertibleModule X L] (n d : ℤ) (F : X.Modules) :
    twistModule X L ((reesMultiple J n F).toSheafOfModules : X.Modules) d ≅
      ((reesMultiple J n (twistModule X L F d)).toSheafOfModules : X.Modules) :=
  reesMultipleTensorIso J n F (tensorPowModule X L d)

/-- **The twisting comparison commutes with the two inclusions into `F(d)`.** -/
@[reassoc]
public theorem reesMultipleTwistIso_hom_ι (J : X.IdealSheafData) (L : X.Modules)
    [IsInvertibleModule X L] (n d : ℤ) (F : X.Modules) :
    (reesMultipleTwistIso J L n d F).hom ≫ (reesMultiple J n (twistModule X L F d)).ι =
      (tensorRightModules X (tensorPowModule X L d)).map ((reesMultiple J n F).ι : _ ⟶ F) :=
  reesMultipleTensorIso_hom_ι J n F (tensorPowModule X L d)

/-- **The twisting comparison intertwines the inclusions of one ideal-power subsheaf into
another**, `reesMultipleTensorIso_hom_comp` at `G = L^{⊗ d}`. This is the square whose cokernels
give `ℐⁿ(F(d))/ℐⁿ⁺¹(F(d)) ≅ (ℐⁿF/ℐⁿ⁺¹F)(d)`. -/
public theorem reesMultipleTwistIso_hom_comp (J : X.IdealSheafData) (L : X.Modules)
    [IsInvertibleModule X L] (n m d : ℤ) (F : X.Modules)
    (u : (((reesMultiple J m F).toSheafOfModules : X.Modules)) ⟶
      ((reesMultiple J n F).toSheafOfModules : X.Modules))
    (hu : u ≫ ((reesMultiple J n F).ι : _ ⟶ F) = (reesMultiple J m F).ι)
    (v : (((reesMultiple J m (twistModule X L F d)).toSheafOfModules : X.Modules)) ⟶
      ((reesMultiple J n (twistModule X L F d)).toSheafOfModules : X.Modules))
    (hv : v ≫ ((reesMultiple J n (twistModule X L F d)).ι : _ ⟶ twistModule X L F d) =
      (reesMultiple J m (twistModule X L F d)).ι) :
    (reesMultipleTwistIso J L m d F).hom ≫ v =
      (tensorRightModules X (tensorPowModule X L d)).map u ≫
        (reesMultipleTwistIso J L n d F).hom :=
  reesMultipleTensorIso_hom_comp J n m F (tensorPowModule X L d) u hu v hv

end Stacks.Blowup

end
