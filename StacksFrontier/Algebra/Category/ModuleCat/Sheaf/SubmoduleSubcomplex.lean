module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleFactorThru
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# The subcomplex cut out by a family of submodules stable under the differential

Let `K` be a homological complex of sheaves of modules and let `N i` be a submodule of the
degree-`i` term for every `i`. If the differentials of `K` carry local sections of `N i` into
`N j`, then the `N i` are the terms of a subcomplex of `K`: the differential of the subcomplex
is the restriction of the differential of `K`, and the inclusions `N i ⟶ K.X i` assemble into a
degreewise monomorphic morphism of complexes.

## Main definitions

* `SheafOfModules.Submodule.subcomplexD`: the restricted differential
  `N i ⟶ N j`.
* `SheafOfModules.Submodule.subcomplex`: **the subcomplex of `K` with terms `N i`.**
* `SheafOfModules.Submodule.subcomplexι`: the inclusion `subcomplex ⟶ K`.

## Main results

* `SheafOfModules.Submodule.subcomplexD_ι`: the restricted differential followed by the
  inclusion is the inclusion followed by the differential of `K`. This pins the differential
  down, the inclusion being a monomorphism.
* `SheafOfModules.Submodule.mono_subcomplexι_f`: the inclusion is a monomorphism in every
  degree.
* `SheafOfModules.Submodule.eq_subcomplexD`: any morphism `N i ⟶ N j` whose composite with the
  inclusion is the differential of `K` is the restricted differential.

## Implementation notes

**Why the hypothesis is sectionwise and not stalkwise or categorical.** A submodule of a sheaf
of modules is, by `SheafOfModules.Submodule`, a sub-presheaf of its sections closed under the
local nature of membership, so "the differential carries `N i` into `N j`" is literally a
statement about local sections and nothing has to be sheafified to say it. The factorization
that follows is then `SheafOfModules.Submodule.factorThru`, which restricts the codomain
objectwise. The alternative — presenting the terms by arbitrary monomorphisms `M i ⟶ K.X i` and
asking that `M i ⟶ K.X i ⟶ K.X j` kill the cokernel of `M j ⟶ K.X j` — needs an abelian
structure on the ambient category and a cokernel at every degree, and delivers the same complex
only after one identifies the subobject with the submodule. Nothing here needs either, and the
statement holds over an arbitrary site.

**No condition on the complex shape.** The differential is restricted for every pair `i, j`, not
only for the pairs related by the shape, so `shape` and `d_comp_d'` are inherited from `K` by
cancelling the monomorphism `(N _).ι` rather than by a case split; in particular the result is
available for `ℕ`-indexed and for `ℤ`-indexed complexes without duplication. The price is that
the hypothesis quantifies over all pairs `i, j`; since `K.d i j = 0` unless `c.Rel i j`, and
`0` lands in every submodule, that is no stronger than quantifying over the related pairs, but
it does have to be supplied in that shape.

**Why `d ∘ d = 0` needs no computation.** The inclusion of a submodule is a monomorphism, so an
equation between morphisms into `N k` may be checked after composing with `(N k).ι`; there the
two restricted differentials unfold to the differentials of `K`, whose composite vanishes. The
same cancellation gives the naturality square of the inclusion and the uniqueness of the
restricted differential.

## References

* [Stacks Project, Tag 01AP](https://stacks.math.columbia.edu/tag/01AP)
-/

@[expose] public noncomputable section

universe w v v₁ u₁ u

open CategoryTheory Opposite

namespace SheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {ι : Type w} {c : ComplexShape ι} {K : HomologicalComplex (SheafOfModules.{v} R) c}
  (N : ∀ i, (K.X i).Submodule)
  (hN : ∀ (i j : ι) (U : Cᵒᵖ) (x : (K.X i).val.obj U), x ∈ (N i).obj U →
    (K.d i j).val.app U x ∈ (N j).obj U)

/-- **The differential of the subcomplex**: the differential of `K` restricted to the
submodules, available because a local section of `N i` is carried into `N j`. -/
def subcomplexD (i j : ι) : (N i).toSheafOfModules ⟶ (N j).toSheafOfModules :=
  (N j).factorThru ((N i).ι ≫ K.d i j) fun U x ↦ hN i j U x.1 x.2

/-- **The restricted differential is the differential of `K`**: composing it with the inclusion
of `N j` gives the inclusion of `N i` followed by the differential of `K`. Since the inclusion
is a monomorphism this determines it. -/
@[reassoc (attr := simp)]
theorem subcomplexD_ι (i j : ι) :
    subcomplexD N hN i j ≫ (N j).ι = (N i).ι ≫ K.d i j :=
  (N j).factorThru_ι _ _

/-- Any morphism `N i ⟶ N j` whose composite with the inclusion is the differential of `K` is
the restricted differential. -/
theorem eq_subcomplexD (i j : ι) (g : (N i).toSheafOfModules ⟶ (N j).toSheafOfModules)
    (hg : g ≫ (N j).ι = (N i).ι ≫ K.d i j) : g = subcomplexD N hN i j :=
  (N j).eq_factorThru _ _ g hg

/-- **The subcomplex of `K` cut out by a family of submodules stable under the differential**:
its degree-`i` term is `N i` and its differential is the restriction of the differential of
`K`. -/
def subcomplex : HomologicalComplex (SheafOfModules.{v} R) c where
  X i := (N i).toSheafOfModules
  d i j := subcomplexD N hN i j
  shape i j hij := by
    rw [← cancel_mono (N j).ι, subcomplexD_ι, K.shape i j hij,
      Limits.comp_zero, Limits.zero_comp]
  d_comp_d' i j k _ _ := by
    rw [← cancel_mono (N k).ι, Category.assoc, subcomplexD_ι, subcomplexD_ι_assoc,
      K.d_comp_d, Limits.comp_zero, Limits.zero_comp]

/-- The degree-`i` term of the subcomplex is `N i`. -/
@[simp]
theorem subcomplex_X (i : ι) : (subcomplex N hN).X i = (N i).toSheafOfModules := rfl

/-- The differential of the subcomplex is the restricted differential `subcomplexD`. -/
@[simp]
theorem subcomplex_d (i j : ι) : (subcomplex N hN).d i j = subcomplexD N hN i j := rfl

/-- **The inclusion of the subcomplex into `K`**, degreewise the inclusion of the submodule. -/
def subcomplexι : subcomplex N hN ⟶ K where
  f i := (N i).ι
  comm' i j _ := (subcomplexD_ι N hN i j).symm

/-- In degree `i`, the inclusion of the subcomplex is the inclusion of `N i`. -/
@[simp]
theorem subcomplexι_f (i : ι) : (subcomplexι N hN).f i = (N i).ι := rfl

/-- The inclusion of the subcomplex is a monomorphism in every degree. -/
instance mono_subcomplexι_f (i : ι) : Mono ((subcomplexι N hN).f i) :=
  inferInstanceAs (Mono (N i).ι)

end SheafOfModules.Submodule

end
