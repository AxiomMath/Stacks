module

public import StacksFrontier.CategoryTheory.Triangulated.HomologyOfTheMiddleVertex

/-!
# The third vertex of a retraction of distinguished triangles

Let `φ : S ⟶ T` be a morphism of distinguished triangles and suppose the *first two* components
of `φ` admit a common section: morphisms `a : T.obj₁ ⟶ S.obj₁` and `b : T.obj₂ ⟶ S.obj₂` which
commute with the first maps of the two triangles and satisfy `a ≫ φ.hom₁ = 𝟙` and
`b ≫ φ.hom₂ = 𝟙`. Then `φ.hom₃` admits a section *up to an isomorphism*: there is a
`c : T.obj₃ ⟶ S.obj₃` with `c ≫ φ.hom₃` invertible. In particular `φ.hom₃` becomes an
epimorphism under every functor.

The commuting square `T.mor₁ ≫ b = a ≫ S.mor₁` is completed to a morphism of triangles `ψ : T ⟶ S`
by the axiom TR3 (`CategoryTheory.Pretriangulated.complete_distinguished_triangle_morphism`) — the
**dotted arrow**. The composite `ψ ≫ φ : T ⟶ T` then has both of its outer components equal to the
identity, so two-out-of-three (`CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂`) makes its third
component `c ≫ φ.hom₃` invertible — the **sandwich**. A composite which an additive functor sends
to an isomorphism has an epic second factor, which is the shape a homology chase consumes.

This supplies the one hypothesis of
`CategoryTheory.Functor.isIso_and_epi_homology₂_of_triangleMorphism` which that statement takes
as given, namely `Epi ((F.shift m).map φ.hom₃)`. In the last paragraph of the proof of
[Stacks, Tag 0FPV] the two triangles are

`E^• ⟶ K ⟶ σ_{≤ m-1}K^• ⟶ E^•[1]`  and  `E^• ⟶ M ⟶ L^• ⟶ E^•[1]`,

`φ` is the morphism between them which is the identity on `E^•`, and `a = 𝟙`, `b = s` is the
section `s : M ⟶ K` of the middle component produced by the direct-summand argument; the source
reads the conclusion as *"the vertical composition `H^{m-1}(L^•) ⟶ H^{m-1}(σ_{≤ m-1}K^•) ⟶
H^{m-1}(L^•)` in the middle is surjective"*.

Nothing here is a clause of a tag; it is a step of a proof, so no `@[stacks …]` attribute is
attached.

## Main results

* `CategoryTheory.Pretriangulated.exists_isIso_comp_hom₃`: the dotted arrow and the sandwich —
  a `c` with `c ≫ φ.hom₃` invertible.
* `CategoryTheory.Pretriangulated.epi_map_hom₃_of_section₁₂`: the consequence under a functor,
  which is the `Epi` hypothesis of the degree-`m` chase.

## Implementation notes

**Why `IsIso (c ≫ φ.hom₃)` and not `c ≫ φ.hom₃ = 𝟙`.** The dotted arrow of TR3 is not unique,
and nothing forces the composite to be the identity: what the sandwich gives is that it is an
isomorphism, by two-out-of-three applied to the endomorphism `ψ ≫ φ` of `T`. That is already
enough for every consumer, since an isomorphism is in particular an epimorphism and
epimorphy of a composite passes to its second factor.

**Why a bare functor and not a homological one.** The conclusion `Epi (G.map φ.hom₃)` needs only
that `G` carries the isomorphism `c ≫ φ.hom₃` to an isomorphism, which every functor does. The
caller instantiates `G` at `F.shift m` for a homological `F` with a shift sequence, but neither
hypothesis is used here.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Pretriangulated

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
  {S T : Triangle C}

/-- **The dotted arrow and the sandwich.** Let `φ : S ⟶ T` be a morphism of distinguished
triangles whose first two components admit a common section: `a : T.obj₁ ⟶ S.obj₁` and
`b : T.obj₂ ⟶ S.obj₂` with `T.mor₁ ≫ b = a ≫ S.mor₁`, `a ≫ φ.hom₁ = 𝟙` and `b ≫ φ.hom₂ = 𝟙`.
Then there is a `c : T.obj₃ ⟶ S.obj₃` for which `c ≫ φ.hom₃` is an isomorphism.

The square is completed to a morphism of triangles `ψ : T ⟶ S` by TR3; the composite `ψ ≫ φ` is
an endomorphism of `T` whose first two components are the identity, so its third component
`c ≫ φ.hom₃` is an isomorphism by two out of three. -/
theorem exists_isIso_comp_hom₃ (hS : S ∈ distTriang C) (hT : T ∈ distTriang C) (φ : S ⟶ T)
    (a : T.obj₁ ⟶ S.obj₁) (b : T.obj₂ ⟶ S.obj₂) (comm : T.mor₁ ≫ b = a ≫ S.mor₁)
    (ha : a ≫ φ.hom₁ = 𝟙 T.obj₁) (hb : b ≫ φ.hom₂ = 𝟙 T.obj₂) :
    ∃ c : T.obj₃ ⟶ S.obj₃, IsIso (c ≫ φ.hom₃) := by
  obtain ⟨c, hc₂, hc₃⟩ := complete_distinguished_triangle_morphism T S hT hS a b comm
  have h {X : C} (f : X ⟶ X) (hf : f = 𝟙 X) : IsIso f := hf ▸ inferInstance
  exact ⟨c, isIso₃_of_isIso₁₂ (Triangle.homMk T S a b c comm hc₂ hc₃ ≫ φ) hT hT
    (h _ ha) (h _ hb)⟩

/-- **The third component of such a `φ` is epic under every functor.** The isomorphism
`c ≫ φ.hom₃` of `CategoryTheory.Pretriangulated.exists_isIso_comp_hom₃` is carried to an
isomorphism, hence to an epimorphism, and epimorphy of a composite passes to its second factor.

This is the hypothesis `Epi ((F.shift m).map φ.hom₃)` of
`CategoryTheory.Functor.isIso_and_epi_homology₂_of_triangleMorphism`, read at `G = F.shift m`. -/
theorem epi_map_hom₃_of_section₁₂ {A : Type u₂} [Category.{v₂} A] (G : C ⥤ A)
    (hS : S ∈ distTriang C) (hT : T ∈ distTriang C) (φ : S ⟶ T)
    (a : T.obj₁ ⟶ S.obj₁) (b : T.obj₂ ⟶ S.obj₂) (comm : T.mor₁ ≫ b = a ≫ S.mor₁)
    (ha : a ≫ φ.hom₁ = 𝟙 T.obj₁) (hb : b ≫ φ.hom₂ = 𝟙 T.obj₂) :
    Epi (G.map φ.hom₃) := by
  obtain ⟨c, hc⟩ := exists_isIso_comp_hom₃ hS hT φ a b comm ha hb
  have : IsIso (G.map (c ≫ φ.hom₃)) := G.map_isIso _
  rw [G.map_comp] at this
  exact epi_of_epi (G.map c) (G.map φ.hom₃)

end CategoryTheory.Pretriangulated

end
