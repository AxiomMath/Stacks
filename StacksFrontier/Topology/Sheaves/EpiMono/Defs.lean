module

public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksCore.Tactic.StacksAttribute

/-!
# Subpresheaves, and injective and surjective morphisms of (pre)sheaves of sets

Stacks 007U fixes the vocabulary for morphisms of (pre)sheaves of sets on a topological
space `X`:

1. a *subpresheaf* of `G` is a choice of subset `F(U) ⊆ G(U)` for each open `U`, compatible
   with the restriction maps of `G`; a *subsheaf* is such a subpresheaf which is itself a
   sheaf;
2. a morphism of presheaves is *injective* when each `F(U) → G(U)` is injective;
3. a morphism of presheaves is *surjective* when each `F(U) → G(U)` is surjective;
4. a morphism of sheaves is *injective* when each `F(U) → G(U)` is injective;
5. a morphism of sheaves is *surjective* when every section of `G` over `U` is, on the parts
   of some open covering of `U`, in the image of `F`.

Each notion is matched here with the corresponding Mathlib notion. Clauses (2), (3) and (4)
are identified with the categorical `Mono`/`Epi` in the relevant category, so that the
Stacks vocabulary is pinned to something usable; note that (3) and (5) differ — a
*presheaf* epimorphism is surjective on every open, whereas a *sheaf* epimorphism is only
locally surjective, which is why the tag states the two separately. Clause (5) is matched
with `TopCat.Presheaf.IsLocallySurjective` by proving that predicate equivalent to the tag's
covering formulation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat
open scoped AlgebraicGeometry

universe u

namespace SheafInjectiveSurjective

variable {X : TopCat.{u}}

/-! ### (1) Subpresheaves and subsheaves -/

/- **Stacks 007U (1).** A subpresheaf of a presheaf of sets `G` on `X` is a
`CategoryTheory.Subfunctor` of `G` regarded as a functor `(Opens X)ᵒᵖ ⥤ Type u`: its data is
exactly a subset of `G(U)` for every open `U`, subject to the requirement that the
restriction maps of `G` carry the chosen subsets into one another. -/
add_to_stacks 007U "A subpresheaf of a presheaf of sets `G` on `X`: `Subfunctor G` is a
  subset `F U ⊆ G U` for each object `U`, required to be carried into itself by every
  restriction map of `G`, which is the tag's condition. Instantiating the ambient category at
  `(Opens X)ᵒᵖ` gives subpresheaves on a topological space." CategoryTheory.Subfunctor

/- The subpresheaf realized as an honest presheaf, whose restriction maps are those induced
by `G` — the second half of the tag's clause (1). A *subsheaf* of a sheaf `G` is such a
subfunctor whose `toFunctor` satisfies the sheaf condition; `Subfunctor.isSheaf_iff`
characterizes when that happens. -/
add_to_stacks 007U "The subpresheaf viewed as a presheaf in its own right, with the
  restriction maps induced by those of `G`. A subsheaf of a sheaf is a subpresheaf whose
  `toFunctor` is again a sheaf." CategoryTheory.Subfunctor.toFunctor
add_to_sga "3 I 1.2" CategoryTheory.Subfunctor.toFunctor

/-! ### (2)–(3) Injective and surjective morphisms of presheaves -/

/-- **Stacks 007U (2).** A morphism of presheaves of sets is injective in the sense of the
tag — injective on sections over every open — exactly when it is a monomorphism of
presheaves. Monomorphisms in a functor category into `Type u` are detected objectwise, and
monomorphisms of types are the injections. -/
@[stacks 007U "(2)"]
theorem presheaf_mono_iff_injective {F G : TopCat.Presheaf (Type u) X} (φ : F ⟶ G) :
    Mono φ ↔ ∀ U : (Opens X)ᵒᵖ, Function.Injective (φ.app U) :=
  (NatTrans.mono_iff_mono_app' (Type u) φ).trans
    (forall_congr' fun U => mono_iff_injective (φ.app U))

/-- **Stacks 007U (3).** A morphism of presheaves of sets is surjective in the sense of the
tag — surjective on sections over every open — exactly when it is an epimorphism of
presheaves. Epimorphisms in a functor category into `Type u` are detected objectwise, and
epimorphisms of types are the surjections.

Contrast clause (5): for *sheaves* this pointwise condition is strictly stronger than being
an epimorphism. -/
@[stacks 007U "(3)"]
theorem presheaf_epi_iff_surjective {F G : TopCat.Presheaf (Type u) X} (φ : F ⟶ G) :
    Epi φ ↔ ∀ U : (Opens X)ᵒᵖ, Function.Surjective (φ.app U) :=
  (NatTrans.epi_iff_epi_app' (Type u) φ).trans
    (forall_congr' fun U => epi_iff_surjective (φ.app U))

/-! ### (4) Injective morphisms of sheaves -/

/-- **Stacks 007U (4).** A morphism of sheaves of sets is injective in the sense of the tag —
injective on sections over every open — exactly when it is a monomorphism of sheaves.

A morphism of sheaves is a monomorphism precisely when the underlying morphism of presheaves
is (`CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono`, which uses that `sheafToPresheaf` is a
right adjoint), and then clause (2) applies. So, unlike surjectivity, injectivity of a
morphism of sheaves is the same condition whether it is read in presheaves or in sheaves. -/
@[stacks 007U "(4)"]
theorem sheaf_mono_iff_injective {F G : TopCat.Sheaf (Type u) X} (φ : F ⟶ G) :
    Mono φ ↔ ∀ U : (Opens X)ᵒᵖ, Function.Injective (φ.hom.app U) :=
  (Sheaf.Hom.mono_iff_presheaf_mono _ _ φ).trans (presheaf_mono_iff_injective φ.hom)

/-! ### (5) Surjective morphisms of sheaves -/

/-- **Stacks 007U (5).** A morphism `φ : F ⟶ G` of presheaves of sets on `X` is locally
surjective exactly when for every open `U` and every section `t` of `G` over `U` there is an
open covering `U = ⨆ i, V i` such that `t|_{V i}` lies in the image of `F(V i) → G(V i)` for
every `i`. The right-hand side is the tag's definition of a surjective morphism of sheaves,
verbatim; so `TopCat.Presheaf.IsLocallySurjective` is that notion.

Mathlib's `TopCat.Presheaf.isLocallySurjective_iff` states the condition pointwise: every
point of `U` has a neighbourhood inside `U` on which `t` is in the image. Passing between the
two is exactly the passage between "an open cover of `U`" and "a neighbourhood for each point
of `U`": indexing the chosen neighbourhoods by the points of `U` produces a cover, and
conversely a member of a cover containing a given point is such a neighbourhood. -/
@[stacks 007U "(5)"]
theorem isLocallySurjective_iff_exists_cover {F G : TopCat.Presheaf (Type u) X} (φ : F ⟶ G) :
    TopCat.Presheaf.IsLocallySurjective φ ↔
      ∀ (U : Opens X) (t : ToType (G.obj (op U))),
        ∃ (ι : Type u) (V : ι → Opens X) (hVU : ∀ i, V i ≤ U), U = iSup V ∧
          ∀ i, ∃ s : ToType (F.obj (op (V i))),
            φ.app (op (V i)) s = TopCat.Presheaf.restrictOpen t (V i) (hVU i) := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  constructor
  · intro h U t
    -- Index the chosen neighbourhoods by the points of `U`; they then form a cover of `U`.
    choose V hVU hs hxV using fun p : {x : X // x ∈ U} => h U t p.1 p.2
    exact ⟨{x : X // x ∈ U}, V, hVU,
      le_antisymm (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩) (iSup_le hVU), hs⟩
  · intro h U t x hx
    obtain ⟨ι, V, hVU, hcover, hsec⟩ := h U t
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover ▸ hx)
    exact ⟨V i, hVU i, hsec i, hi⟩

end SheafInjectiveSurjective
