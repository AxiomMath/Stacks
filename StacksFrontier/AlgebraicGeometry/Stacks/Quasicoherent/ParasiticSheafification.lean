module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticFlatRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticModules

/-!
# Sheafification preserves parasitic modules (Stacks 0774)

Let `𝒳` be an algebraic stack over a scheme `S` in a big fppf site `B` and let `τ` be one of the
five topologies of **Stacks 06TP**. Clause (2)(a) of **Stacks 0774** says that the
`τ`-sheafification of a parasitic presheaf of `𝒪_𝒳`-modules (**Stacks 0773**) is parasitic.

The source's proof is that a `τ`-covering of an object lying over a scheme flat over `𝒳` again
consists of such objects, so that the plus construction of a parasitic presheaf has vanishing
sections there, and sheafification is the plus construction twice. The proof below runs the same
argument once, at the level of local surjectivity rather than of the plus construction: the map
from a presheaf to its sheafification is locally surjective, so a section of the sheafification
at a flat object is, locally on a covering, the image of a section of the presheaf; that
covering may be refined by one whose sources are again flat objects
(`AlgebraicGeometry.Stack.exists_flatObject_covering_le_of_mem_associatedTopology`), where the
presheaf vanishes; and a sheaf is separated.

## Main results

* `AlgebraicGeometry.Stack.isParasitic_of_isLocallySurjective`: a sheaf of modules receiving a
  locally surjective map from a parasitic presheaf of modules is parasitic. This is the form in
  which the argument is used twice — here for the sheafification, and in
  `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/ParasiticSerreSubcategory.lean` for the
  quotient of a parasitic module, which is clause (2)(b)'s closure under quotients.
* `AlgebraicGeometry.Stack.isParasitic_sheafification`: **Stacks 0774** (2)(a).

## Implementation notes

The hypothesis of `AlgebraicGeometry.Stack.isParasitic_of_isLocallySurjective` is local
surjectivity of a morphism of the underlying presheaves of abelian groups, not of a morphism of
presheaves of modules. Nothing in the argument uses the module structure of the map, and the two
consumers produce their local surjectivity in that form: for the sheafification it is
`CategoryTheory.GrothendieckTopology.W_toSheafify`, whose target is *definitionally* the
underlying presheaf of the sheafification of presheaves of modules, and for an epimorphism of
sheaves of modules it is `Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi`, which is
stated for the image of the morphism under `PresheafOfModules.toPresheaf`. Asking for a morphism
of presheaves of modules would force a transport along `PresheafOfModules.restrictScalars` of
the identity in the first case and an unfolding of `PresheafOfModules.toPresheaf` in the second.

Local surjectivity is an explicit hypothesis rather than an instance argument because the
instance `CategoryTheory.Presheaf.isLocallySurjective_toSheafify` of Mathlib is not found by
instance search at this seating; it is supplied as a term instead.

Sheafification is Mathlib's `PresheafOfModules.sheafification` at the identity of the structure
presheaf of rings, which is the associated-sheaf functor
`Mod(𝒳_τ^{pre}, 𝒪_𝒳) ⥤ Mod(𝒳_τ, 𝒪_𝒳)` the source means; it is not given a name here, since no
abbreviation for it exists in the library and the statement names it once.

The universe hypothesis `UnivLE.{u + 1, t}` is the one
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/ParasiticSerreSubcategory.lean` carries, and
for the same reason: it is what makes `AddCommGrpCat.{t}`-valued presheaves on a site whose
objects lie in `Type (u + 1)` and whose morphisms lie in `Type u` sheafifiable, with the weak
equivalences the locally bijective morphisms.

## References

* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0774](https://stacks.math.columbia.edu/tag/0774)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w t

attribute [local instance] CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) (τ : SiteKind)
variable [UnivLE.{u + 1, t}]

omit [UnivLE.{u + 1, t}] in
/-- **A sheaf of modules which receives a locally surjective map from a parasitic presheaf of
modules is parasitic.**

Let `x` be a flat object and `s` a section of the sheaf there. Local surjectivity makes the
arrows along which `s` becomes the image of a section of the presheaf a covering sieve of `x`;
that sieve contains a covering family whose sources are again flat objects
(`AlgebraicGeometry.Stack.exists_flatObject_covering_le_of_mem_associatedTopology`), and at a
flat object the presheaf vanishes, so `s` restricts to zero along every member of the family and
hence along every arrow of the sieve it generates. A sheaf is separated, so `s = 0`. -/
theorem isParasitic_of_isLocallySurjective
    {F : PresheafOfModules.{t}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ).obj}
    {G : SheafOfModules.{t}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ)}
    (φ : F.presheaf ⟶ G.val.presheaf)
    (hφ : Presheaf.IsLocallySurjective
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) φ)
    (hF : IsParasitic B S hS 𝒳 τ F) :
    IsParasitic B S hS 𝒳 τ G.val := by
  intro x hx
  have key : ∀ s : G.val.obj (op x), s = 0 := by
    intro s
    obtain ⟨E, hEflat, hEcov, hEle⟩ :=
      exists_flatObject_covering_le_of_mem_associatedTopology B S hS 𝒳 τ hx _
        (Presheaf.imageSieve_mem (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) φ s)
    have hzero : ∀ i, G.val.map (E.f i).op s = 0 := by
      intro i
      obtain ⟨y, hy⟩ := hEle _ _ (E.presieve₀_f i)
      rw [(hF _ (hEflat i)).elim y 0] at hy
      exact hy.symm.trans (map_zero _)
    refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero s hEcov ?_
    rintro Y g ⟨Z, h, k, ⟨i⟩, rfl⟩
    rw [op_comp, PresheafOfModules.map_comp_apply, hzero i]
    exact map_zero _
  exact ⟨fun a b => (key a).trans (key b).symm⟩

/-- **Stacks 0774** (2)(a). The `τ`-sheafification of a parasitic presheaf of
`𝒪_𝒳`-modules is parasitic, for each of the five topologies `τ` of **Stacks 06TP**.

The map from a presheaf of modules to its sheafification is locally surjective, so this is
`AlgebraicGeometry.Stack.isParasitic_of_isLocallySurjective`. -/
@[stacks 0774 "part (2)(a): the τ-sheafification of a parasitic presheaf of modules is
parasitic"]
theorem isParasitic_sheafification
    (F : PresheafOfModules.{t}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ).obj)
    (hF : IsParasitic B S hS 𝒳 τ F) :
    IsParasitic B S hS 𝒳 τ
      ((PresheafOfModules.sheafification.{t}
        (𝟙 (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids τ).obj)).obj F).val :=
  isParasitic_of_isLocallySurjective B S hS 𝒳 τ
    (CategoryTheory.toSheafify
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) F.presheaf)
    ((GrothendieckTopology.W_toSheafify
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
      F.presheaf).isLocallySurjective) hF

end AlgebraicGeometry.Stack

end
