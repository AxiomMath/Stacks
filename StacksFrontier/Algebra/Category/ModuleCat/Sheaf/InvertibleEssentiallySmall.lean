module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.WellPowered
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandSheafify

/-!
# The two smallness inputs to the essential smallness of the invertible modules

[Stacks, Tag 040B](https://stacks.math.columbia.edu/tag/040B) asserts that on a ringed site the
isomorphism classes of invertible sheaves of modules form a set. Its proof (which the Stacks
Project omits, referring to [Tag 01CW](https://stacks.math.columbia.edu/tag/01CW)) runs on two
inputs, and this file supplies both of them. **Tag 040B is not proved *here*, and nothing in this
file carries the `@[stacks 040B]` attribute.**

It is proved elsewhere:
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSmallEncoding` carries `@[stacks 040B]`
on `Stacks.SheafOfModules.essentiallySmall_isInvertible`, as a restatement adding the
three sheafification hypotheses Stacks assumes throughout its modules-on-sites chapter.

And it does **not** go through this file's well-poweredness. The implementation notes below
describe the categorical route — invertibles as quotients of a coproduct of `j_{U!}`, bounded by
well-poweredness — which **cannot run at the universes of the statement**: coverings are indexed in
`Type (max u v)` and coproducts in `PresheafOfModules.{w}` over such an index need `Small.{w}` of
it. The route that works encodes each invertible by its family of ranges inside one big presheaf
of modules and uses `ObjectProperty.essentiallySmall_of_invariant`, needing no `j_{U!}`, no
gluing, no abelian structure and no `Subobject`. `SheafOfModules.wellPowered` below is correct and
optimal and is worth having; it is simply not what 040B consumes.

The first input is *well-poweredness*: the subobjects of a fixed sheaf of modules form a set,
at a universe independent of the ring and of the morphisms of the site. This is the sheaf-level
form of `PresheafOfModules.wellPowered'`
(`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/WellPowered.lean`), obtained by transporting
subobjects to families of submodules of the underlying presheaf of modules.

The second input is a *uniform local bound* on an invertible module: every object of the site
has a covering on whose members an invertible sheaf of modules has an injective linear map
into a finite free module of sections of the structure sheaf. This sharpens
`Stacks.SheafOfModules.exists_cover_isDirectSummand_finiteFree`
(Tag 0B8N (b), proved in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleSummandNoSliceSheafify.lean`, which is
where that tag's clause (b) is carried) from a split
monomorphism of sheaves of modules on a slice site to a concrete injective map on sections over
a single object, which is the form a cardinality argument can consume. No declaration here
carries a second `@[stacks 0B8N]` or `@[stacks 0B8K]` attribute: what is added is a
reformulation of clause (b), not a new clause of either tag.

## Main definitions

* `SheafOfModules.rangeSubmodule`: the family of pointwise `LinearMap.range`s of a representing
  monomorphism of a subobject of a sheaf of modules, as a `PresheafOfModules.Submodule` of the
  underlying presheaf of modules.
* `SheafOfModules.subobjectSubmodule`: the resulting order embedding
  `Subobject M ↪o M.val.Submodule`.
* `Stacks.SheafOfModules.pairingTuple`: pairing a section of `Lp` against finitely many sections
  of `Np` through a pairing `ψ : Lp ⊗ Np ⟶ O`, as a linear map into a finite free module.

## Main results

* `SheafOfModules.mono_val`: a monomorphism of sheaves of modules is a monomorphism of the
  underlying presheaves of modules.
* `SheafOfModules.mk_le_mk_iff_range_le`: two subobjects presented by monomorphisms are
  comparable exactly when the pointwise ranges of the underlying morphisms of presheaves of
  modules are.
* `SheafOfModules.wellPowered`: `WellPowered.{max u₁ v} (SheafOfModules.{v} R)`.
* `Stacks.SheafOfModules.exists_leftInverse_of_dualBasis`: a dual basis for a locally bijective
  pairing produces a family of morphisms out of the structure sheaf which, summed, invert
  `pairingTuple` on sections over every object. This is the element-level content of the
  splitting in Tag 0B8N (b).
* `Stacks.SheafOfModules.exists_injective_linearMap_of_dualBasis`: consequently, a dual basis
  over an object `V` makes the sections of `Lp` over `V` embed linearly in a finite free module.
* `Stacks.SheafOfModules.exists_cover_injective_finFree`: every object of the site has a
  covering on whose members an invertible sheaf of modules embeds linearly in a finite free
  module of sections of the structure sheaf.

## Implementation notes

Universes. For the well-poweredness half the names are Mathlib's: `C : Type u₁` with morphisms
in `Type v₁`, `R : Sheaf J RingCat.{u}`, modules in `Type v`. For the invertibility half they
are those of Stacks Tag 05NA: `C : Type u` with morphisms in `Type v`, and
the sections of the ring and of the modules share the universe `w`, as Mathlib's monoidal
structure on presheaves of modules requires. Nothing is specialized: the bound `max u₁ v` on
subobjects is forced and optimal, since the morphisms of `SheafOfModules.{v} R` are those of
`PresheafOfModules.{v} R.obj` and live in `Type (max u₁ v)`, so `LocallySmall.{max u₁ v}` —
needed even to state `WellPowered.{max u₁ v}` — is the sharpest available.

`mono_val` goes through `SheafOfModules.forget`, which preserves finite limits
(`SheafOfModules.Finite.forgetPreservesFiniteLimits`) and hence pullbacks, hence monomorphisms.
It is *not* a consequence of full faithfulness alone: a fully faithful functor need not preserve
monomorphisms, since the test object in the target category need not lie in its image.

The converse direction of `mk_le_mk_iff_range_le` factors `f` through `g` at the level of
presheaves of modules with `PresheafOfModules.factorThru` and lifts the factorization back along
`SheafOfModules.fullyFaithfulForget`. The `show M₁.val ⟶ M₂.val from` ascription on the call to
`factorThru` is load-bearing: without it the expected type reaching `factorThru` still contains
the metavariables of `FullyFaithful.preimage`, the instance argument `[Mono g.val]` is attempted
too early, and synthesis fails even though that very instance is in the local context.

The order embedding is into `M.val.Submodule`, the submodules of the underlying *presheaf* of
modules, rather than onto `SheafOfModules.Submodule M` (Mathlib's submodules with a local
membership condition). An order isomorphism onto the latter is true but needs the gluing
argument that the pointwise range of a monomorphism of sheaves of modules has local membership;
an embedding is all that well-poweredness consumes.

`exists_leftInverse_of_dualBasis` reuses the `coev`/`contract`/`proj` calculus of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleLocalSummand.lean` but stops before
assembling a split monomorphism: the sum `∑ j, c W j = 1` turns the retractions supplied by
`PresheafOfModules.homEquivOfIsLocallyBijective` into a left inverse of `pairingTuple` on
sections, which is strictly more information than `IsSplitMono` of a morphism into a categorical
product, because it names the map on sections. That is what lets
`exists_injective_linearMap_of_dualBasis` state its conclusion as an injective
`LinearMap` into `Fin n → O(V)` rather than into the sections of a product object: evaluating
the product at an object would require transporting along
`SheafOfModules.evaluationPreservesLimitsOfShape`, and the resulting target would not be a
*fixed* module, which a cardinality argument needs.

`exists_injective_linearMap_of_dualBasis` runs on the slice site over `V` and then evaluates at
its object `Over.mk (𝟙 V)`; the resulting linear map is produced existentially rather than
named, because its domain `((sliceFunctor V).obj Lp).obj (op (Over.mk (𝟙 V)))` and the stated
domain `Lp.obj (op V)` are definitionally equal but spelled differently — including their
`Module` instances — and `rw` and `simp` refuse any goal mixing the two spellings, reporting the
target as not type-correct at `implicit` transparency. Stating the conclusion existentially
leaves the comparison to the defeq-tolerant `refine`.

What Tag 040B still needs, on top of this file. The remaining argument does **not** need gluing
(Tag 00AK), an extension-by-zero functor `j_{U!}` for sheaves of modules, or any abelian
structure. It is a cardinality encoding:

1. The separatedness of `L` turns `exists_cover_injective_finFree` into an injective linear map
   `L(U) → ∏ (p : Σ W : Cᵒᵖ, (U ⟶ W)), (ℕ → R(W))` for *every* `U`, by sending a section `s` to
   the family `p ↦ ιₚ (L.map p.2 s)`, where `ιₚ` is an injective linear map chosen at those
   objects where one exists. Such a family is automatically natural, because its component at
   `p` is `ιₚ ∘ L.map p.2`.
2. The common target is a presheaf of modules in `PresheafOfModules.{max u v w}`, *not* in
   `PresheafOfModules.{w}`, so it is not an object of the ambient category and no
   universe-lifting functor is available (Mathlib has `ModuleCat.uliftFunctor` but no
   `PresheafOfModules.uliftFunctor`). This is not an obstruction: only the family of semilinear
   injections and their naturality squares is used, never a categorical morphism, so the
   coherence (`map_id`, `map_comp`) of the big object is never needed.
3. The code of `L` is the family of ranges, an element of
   `∀ U, Submodule (R.obj U) (big U)`, which lives in `Type (max u v w)`. Two invertible modules
   with the same code are isomorphic, because two injective linear maps with the same range
   differ by a linear equivalence, and naturality of both makes the comparison an isomorphism
   of presheaves of modules, hence of sheaves of modules by
   `SheafOfModules.fullyFaithfulForget`. Choosing a representative for each code gives the small
   property `Q` that `ObjectProperty.EssentiallySmall.{max u v w}` asks for.

Also note that the statement of Tag 040B carries no sheafification hypotheses, while every
step above (through Tag 0B8N (b)) needs `HasWeakSheafify J AddCommGrpCat.{w}`,
`J.WEqualsLocallyBijective AddCommGrpCat.{w}` and the same for every slice topology `J.over V`.
Those are hypotheses the Stacks Project assumes throughout its chapter on modules on sites, so
adding them is a faithful restatement rather than a weakening.

## References

* [Stacks Project, Tag 040B](https://stacks.math.columbia.edu/tag/040B)
* [Stacks Project, Tag 01CW](https://stacks.math.columbia.edu/tag/01CW)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
-/

@[expose] public section

open CategoryTheory Limits Opposite MonoidalCategory

open scoped TensorProduct

namespace SheafOfModules

universe v v₁ u₁ u

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

section Subobject

variable {M : SheafOfModules.{v} R}

/-- A monomorphism of sheaves of modules is a monomorphism of the underlying presheaves of
modules, because `SheafOfModules.forget` preserves finite limits. -/
instance mono_val {M₁ M₂ : SheafOfModules.{v} R} (f : M₁ ⟶ M₂) [Mono f] : Mono f.val :=
  inferInstanceAs (Mono ((forget R).map f))

/-- Two subobjects of a sheaf of modules, presented by monomorphisms, are comparable exactly
when the families of pointwise ranges of the underlying morphisms of presheaves of modules
are. -/
lemma mk_le_mk_iff_range_le {M₁ M₂ : SheafOfModules.{v} R} (f : M₁ ⟶ M) (g : M₂ ⟶ M)
    [Mono f] [Mono g] :
    Subobject.mk f ≤ Subobject.mk g ↔
      PresheafOfModules.Submodule.range f.val ≤ PresheafOfModules.Submodule.range g.val := by
  refine ⟨fun hle => ?_, fun hle => ?_⟩
  · have h : (Subobject.ofMkLEMk f g hle).val ≫ g.val = f.val :=
      congrArg Hom.val (Subobject.ofMkLEMk_comp hle)
    rw [← h]
    exact PresheafOfModules.Submodule.range_comp_le _ _
  · exact Subobject.mk_le_mk_of_comm ((fullyFaithfulForget R).preimage
      (show M₁.val ⟶ M₂.val from PresheafOfModules.factorThru f.val g.val hle))
      ((forget R).map_injective (PresheafOfModules.factorThru_comp f.val g.val hle))

/-- The family of pointwise ranges of a representing monomorphism of a subobject of a sheaf of
modules, as a family of submodules of the underlying presheaf of modules. -/
noncomputable def rangeSubmodule (P : Subobject M) : M.val.Submodule :=
  PresheafOfModules.Submodule.range P.arrow.val

/-- Two subobjects of a sheaf of modules are comparable exactly when their families of pointwise
ranges are. -/
lemma rangeSubmodule_le_iff {P Q : Subobject M} :
    rangeSubmodule P ≤ rangeSubmodule Q ↔ P ≤ Q := by
  conv_rhs => rw [← Subobject.mk_arrow P, ← Subobject.mk_arrow Q]
  exact (mk_le_mk_iff_range_le P.arrow Q.arrow).symm

/-- The subobjects of a sheaf of modules `M`, order-embedded in the families of submodules of
its underlying presheaf of modules. Since the target lives in `Type (max u₁ v)`, this is what
makes `SheafOfModules.{v} R` well-powered at `max u₁ v`, with the universe of the sections of
the ring and the universe of the morphisms of the site both free. -/
noncomputable def subobjectSubmodule (M : SheafOfModules.{v} R) :
    Subobject M ↪o M.val.Submodule :=
  .ofMapLEIff rangeSubmodule fun _ _ => rangeSubmodule_le_iff

/-- Sheaves of modules are well-powered with the universe of the sections of the ring and the
universe of the morphisms of the site both free. -/
instance wellPowered : WellPowered.{max u₁ v} (SheafOfModules.{v} R) where
  subobject_small M := small_of_injective (subobjectSubmodule M).injective

end Subobject

end SheafOfModules

namespace Stacks.SheafOfModules

universe v u w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- Pairing a section of `Lp` over `X` against finitely many sections of `Np` over `X` through a
pairing `ψ : Lp ⊗ Np ⟶ O`, as a linear map into a finite free module. -/
noncomputable def pairingTuple
    {Lp Np : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      O)}
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    (X : Cᵒᵖ) {n : ℕ} (y : Fin n → Np.obj X) :
    Lp.obj X →ₗ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O).obj X]
      (Fin n → (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O).obj X) :=
  LinearMap.pi fun j => (ψ.app X).hom ∘ₗ ((TensorProduct.mk _ _ _).flip (y j))

/-- **Stacks Project, Tag 0B8N (b), on sections.** A dual basis for a locally bijective pairing
`ψ : Lp ⊗ Np ⟶ O` — finitely many global sections `x j` of `Lp` and `y j` of `Np` whose
pairings `c j` sum to `1` — produces morphisms `r j : O ⟶ Lp` which, summed, left-invert
`pairingTuple ψ _ y` on the sections over every object.

The `r j` are the factorizations of `proj ψ (x j)` through `ψ` supplied by
`PresheafOfModules.homEquivOfIsLocallyBijective`, and the identity is the element-level form of
the splitting in `Stacks.SheafOfModules.isSplitMono_of_dualBasis`. -/
theorem exists_leftInverse_of_dualBasis [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {Lp Np : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      O)}
    (hLp : Presheaf.IsSheaf J Lp.presheaf)
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    [PresheafOfModules.IsLocallySurjective J ψ] [PresheafOfModules.IsLocallyInjective J ψ]
    {n : ℕ} (x : Fin n → Lp.sections) (y : Fin n → Np.sections)
    (c : ∀ W : Cᵒᵖ, Fin n → O.obj W)
    (hc : ∀ (W : Cᵒᵖ) (j : Fin n), ψ.app W ((x j).eval W ⊗ₜ (y j).eval W) = c W j)
    (hsum : ∀ W : Cᵒᵖ, ∑ j, c W j = 1) :
    ∃ r : Fin n → (𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)) ⟶ Lp),
      ∀ (W : Cᵒᵖ) (v : Lp.obj W),
        ∑ j, (r j).app W (ψ.app W (v ⊗ₜ (y j).eval W)) = v := by
  classical
  set E := PresheafOfModules.homEquivOfIsLocallyBijective (f := ψ) hLp with hE
  have hρ : ∀ j, ψ ≫ (E.symm (proj Lp Np ψ (x j))) = proj Lp Np ψ (x j) :=
    fun j => E.apply_symm_apply _
  refine ⟨fun j => E.symm (proj Lp Np ψ (x j)), fun W v => ?_⟩
  have hj : ∀ j : Fin n,
      (E.symm (proj Lp Np ψ (x j))).app W (ψ.app W (v ⊗ₜ (y j).eval W)) = c W j • v := by
    intro j
    calc (E.symm (proj Lp Np ψ (x j))).app W (ψ.app W (v ⊗ₜ (y j).eval W))
        = (coev Lp Np (y j) ≫ ψ ≫ E.symm (proj Lp Np ψ (x j))).app W v := by
          rw [show (coev Lp Np (y j) ≫ ψ ≫ E.symm (proj Lp Np ψ (x j))).app W v
              = (E.symm (proj Lp Np ψ (x j))).app W
                (ψ.app W ((coev Lp Np (y j)).app W v)) from rfl, coev_app]
      _ = (coev Lp Np (y j) ≫ proj Lp Np ψ (x j)).app W v := by rw [hρ j]
      _ = c W j • v := coev_proj_app Lp Np ψ (x j) (y j) W v (c W j) (hc W j)
  rw [Finset.sum_congr rfl (fun j _ => hj j), ← Finset.sum_smul, hsum W, one_smul]

/-- A dual basis for a locally bijective pairing over a single object `V` makes the sections of
`Lp` over `V` embed linearly in a finite free module of sections of the structure sheaf. The
embedding is `pairingTuple`, read on the slice site over `V`. -/
theorem exists_injective_linearMap_of_dualBasis (V : C)
    [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {Lp Np : PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
      O)}
    (hLp : Presheaf.IsSheaf J Lp.presheaf)
    (ψ : Lp ⊗ Np ⟶ 𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O)))
    [PresheafOfModules.IsLocallySurjective J ψ] [PresheafOfModules.IsLocallyInjective J ψ]
    {n : ℕ} (x : Fin n → Lp.obj (op V)) (y : Fin n → Np.obj (op V))
    (hxy : ∑ j, ψ.app (op V) (x j ⊗ₜ y j) = (1 : O.obj (op V))) :
    ∃ φ : Lp.obj (op V) →ₗ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O).obj
      (op V)]
        (Fin n → (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O).obj (op V)),
      Function.Injective φ := by
  classical
  obtain ⟨c, hcdef⟩ : ∃ c : ∀ W : (Over V)ᵒᵖ, Fin n → (((Over.forget V).op ⋙ O)).obj W,
      ∀ W j, c W j = (𝟙_ (PresheafOfModules.{w}
        (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))).map
        (W.unop.hom).op (ψ.app (op V) (x j ⊗ₜ y j)) := ⟨_, fun _ _ => rfl⟩
  have hsum : ∀ W : (Over V)ᵒᵖ, ∑ j, c W j = 1 := by
    intro W
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hcdef W j]
    have hs : ∑ j, (𝟙_ (PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))).map
          (W.unop.hom).op (ψ.app (op V) (x j ⊗ₜ y j))
        = (𝟙_ (PresheafOfModules.{w}
          (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))).map
          (W.unop.hom).op (∑ j, ψ.app (op V) (x j ⊗ₜ y j)) :=
      (map_sum _ _ _).symm
    refine hs.trans ((congrArg (fun z =>
      (𝟙_ (PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
        O))).map
        (W.unop.hom).op z) hxy).trans ?_)
    exact PresheafOfModules.unit_map_one _ _
  obtain ⟨r, hr⟩ := exists_leftInverse_of_dualBasis (J := J.over V)
    (Lp := (sliceFunctor V).obj Lp) (Np := (sliceFunctor V).obj Np)
    (hLp := (Over.forget V).op_comp_isSheaf_of_isSheaf (J.over V) J _ hLp)
    (ψ := slicePairing V ψ)
    (x := fun j => sliceSection V (x j)) (y := fun j => sliceSection V (y j))
    (c := c)
    (hc := fun W j => (PresheafOfModules.naturality_apply ψ (W.unop.hom).op
      (x j ⊗ₜ y j)).trans (hcdef W j).symm)
    (hsum := hsum)
  refine ⟨pairingTuple (slicePairing V ψ) (op (Over.mk (𝟙 V)))
    (fun j => (sliceSection V (y j)).eval (op (Over.mk (𝟙 V)))), fun v v' h => ?_⟩
  rw [← hr (op (Over.mk (𝟙 V))) v, ← hr (op (Over.mk (𝟙 V))) v']
  exact Finset.sum_congr rfl fun j _ => congrArg _ (congrFun h j)

section Cover

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks Project, Tag 0B8N (b), as a uniform local bound.** Every object `U` of the site has
a covering on whose members an invertible sheaf of modules embeds linearly in a finite free
module of sections of the structure sheaf.

This is the smallness input to [Stacks, Tag 040B](https://stacks.math.columbia.edu/tag/040B):
the target `Fin n → O(V i)` depends only on the structure sheaf and on the covering, not on the
invertible module, so it bounds the sections of every invertible module uniformly. -/
theorem exists_cover_injective_finFree
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      [IsInvertible O hO L] (U : C) :
    ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.generate (Presieve.ofArrows V f) ∈ J U ∧
        ∀ i : I, ∃ (n : ℕ)
          (φ : L.val.obj (op (V i)) →ₗ[(Stacks.SheafOfModules.TensorSheafification.structureSheaf O
            hO).obj.obj (op (V i))]
            (Fin n → (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO).obj.obj (op (V
              i)))),
          Function.Injective φ := by
  classical
  obtain ⟨Lp, hLp, rfl⟩ : ∃ (Lp : PresheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
      (hLp : Presheaf.IsSheaf J Lp.presheaf),
      L = (⟨Lp, hLp⟩ : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        O hO)) :=
    ⟨L.val, L.isSheaf, rfl⟩
  obtain ⟨Np, ψ, hsurj, hinj⟩ := exists_locallyBijective_pairing (hO := hO) hLp inferInstance
  obtain ⟨S, hSdef⟩ : ∃ S : Sieve U,
      S = imgSieve (A := SheafOfModules.unit
        (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ψ
        (1 : O.obj (op U)) := ⟨_, rfl⟩
  have hS : S ∈ J U := by
    rw [hSdef]
    exact Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map ψ) _
  refine ⟨Σ W : C, {g : W ⟶ U // S.arrows g}, fun i => i.1, fun i => i.2.1, ?_, ?_⟩
  · refine J.superset_covering ?_ hS
    intro W g hg
    exact ⟨W, 𝟙 W, g,
      Presieve.ofArrows.mk (⟨W, g, hg⟩ : Σ W : C, {g : W ⟶ U // S.arrows g}),
      Category.id_comp g⟩
  · rintro ⟨W, g, hg⟩
    rw [hSdef] at hg
    obtain ⟨t, ht⟩ := hg
    obtain ⟨n, x, y, hxy⟩ := exists_fin_tmul_eq t
    refine ⟨n, exists_injective_linearMap_of_dualBasis W hLp ψ x y ?_⟩
    have h1 : ∑ j, ψ.app (op W) (x j ⊗ₜ y j) = ψ.app (op W) (∑ j, x j ⊗ₜ y j) :=
      (map_sum _ _ _).symm
    exact h1.trans ((congrArg (fun z => ψ.app (op W) z) hxy).trans
      (ht.trans (PresheafOfModules.unit_map_one _ _)))

end Cover

end Stacks.SheafOfModules
