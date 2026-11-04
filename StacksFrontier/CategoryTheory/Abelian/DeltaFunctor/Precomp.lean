module

public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Effaceable

/-! # Precomposing a cohomological δ-functor with an exact functor

Let `F` be a cohomological δ-functor (`CategoryTheory.DeltaFunctor`, Stacks 010Q) from an abelian
category `A` to an abelian category `B`, and let `Ψ : A' ⥤ A` be an **exact** additive functor.
Then `n ↦ Ψ ⋙ Fⁿ` is again a δ-functor, with the connecting morphism of a short exact sequence
`S` of `A'` taken to be the connecting morphism of the short exact sequence `Ψ(S)` of `A`.

Nothing has to be transported: `Ψ` exact means `Ψ(S)` is short exact
(`CategoryTheory.ShortComplex.ShortExact.map_of_exact`), and the three-term stretches of the long
exact sequence of `Ψ ⋙ F` at `S` are *literally* those of `F` at `Ψ(S)`, because
`(S.map (Ψ ⋙ Fⁿ))` and `((S.map Ψ).map Fⁿ)` are the same short complex.  So every field is the
corresponding field of `F`, evaluated at `Ψ(S)`.

This is one of the two ways the δ-functors appearing in the degree induction of Stacks 0A37 are
assembled.  There the source category is the abelian category of systems of abelian sheaves over
a fixed cofiltered diagram of spectral spaces
(`StacksFrontier/Topology/Sheaves/Limits/AbelianSystemAbelian.lean`), whose evaluation functors at a
stage are exact, and `F` is the cohomology δ-functor over an open of that stage; the limit side is
the cohomology δ-functor over an open of the vertex precomposed with the exact functor
`𝒜 ↦ colimⱼ pⱼ⁻¹𝒜ⱼ`.  The other way of assembling is the filtered colimit of
`StacksFrontier/CategoryTheory/Abelian/DeltaFunctor/Colimit.lean`.

## Main definitions

* `CategoryTheory.DeltaFunctor.mapShortComplexHom`: the image under a functor of a morphism of
  short complexes.
* `CategoryTheory.DeltaFunctor.precomp`: the δ-functor `n ↦ Ψ ⋙ Fⁿ`.
* `CategoryTheory.DeltaFunctor.precompHom`: a morphism of δ-functors precomposes to a morphism of
  the precomposed δ-functors.
* `CategoryTheory.DeltaFunctor.precompNatTrans`: a natural transformation of the precomposing
  exact functors induces a morphism of the precomposed δ-functors.

## Main results

* `CategoryTheory.DeltaFunctor.precomp_functor` and `precomp_δ`: the component functors and the
  connecting morphisms of `precomp`, by definition.
* `CategoryTheory.DeltaFunctor.Effaceable.precomp`: `Ψ ⋙ F` is effaceable — hence universal by
  Stacks 010T — as soon as every object of `A'` admits a monomorphism into an object on which
  `Fⁿ⁺¹ ∘ Ψ` vanishes in every positive degree.  This is the form in which the effaceability input
  of the degree induction of Stacks 0A37 arrives: an embedding of a system into a stagewise
  injective one, together with the two vanishing statements.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 010R](https://stacks.math.columbia.edu/tag/010R)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.DeltaFunctor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {A' : Type u₃} [Category.{v₃} A'] [Abelian A']

/-- **The image of a morphism of short complexes under a functor.**  Mathlib maps a short complex
along a functor and a short complex along a natural transformation, but not a *morphism* of short
complexes along a functor, which is what the naturality of a connecting morphism in the short
exact sequence needs. -/
@[simps]
def mapShortComplexHom (Ψ : A' ⥤ A) [Ψ.Additive] {S T : ShortComplex A'} (φ : S ⟶ T) :
    S.map Ψ ⟶ T.map Ψ where
  τ₁ := Ψ.map φ.τ₁
  τ₂ := Ψ.map φ.τ₂
  τ₃ := Ψ.map φ.τ₃
  comm₁₂ := (Ψ.map_comp φ.τ₁ T.f).symm.trans
    ((congrArg Ψ.map φ.comm₁₂).trans (Ψ.map_comp S.f φ.τ₂))
  comm₂₃ := (Ψ.map_comp φ.τ₂ T.g).symm.trans
    ((congrArg Ψ.map φ.comm₂₃).trans (Ψ.map_comp S.g φ.τ₃))

variable (F : DeltaFunctor A B) (Ψ : A' ⥤ A) [Ψ.Additive]
  [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ]

/-- **A cohomological δ-functor precomposed with an exact functor is a cohomological δ-functor.**
Its degree-`n` component is `Ψ ⋙ Fⁿ` and its connecting morphism at a short exact sequence `S` of
`A'` is the connecting morphism of `F` at the short exact sequence `Ψ(S)`.

Every field is the corresponding field of `F` at `Ψ(S)`: the three-term stretches of the long
exact sequence of `Ψ ⋙ F` at `S` are the stretches of `F` at `Ψ(S)` on the nose, since
`S.map (Ψ ⋙ Fⁿ)` and `(S.map Ψ).map Fⁿ` are the same short complex. -/
def precomp : DeltaFunctor A' B where
  functor n := Ψ ⋙ F.functor n
  additive _ := inferInstance
  δ hS n := F.δ (hS.map_of_exact Ψ) n
  map_g_δ hS n := F.map_g_δ (hS.map_of_exact Ψ) n
  δ_map_f hS n := F.δ_map_f (hS.map_of_exact Ψ) n
  mono_map_f hS := F.mono_map_f (hS.map_of_exact Ψ)
  exact_map hS n := F.exact_map (hS.map_of_exact Ψ) n
  exact_δ₁ hS n := F.exact_δ₁ (hS.map_of_exact Ψ) n
  exact_δ₂ hS n := F.exact_δ₂ (hS.map_of_exact Ψ) n
  δ_naturality hS hT φ n :=
    F.δ_naturality (hS.map_of_exact Ψ) (hT.map_of_exact Ψ) (mapShortComplexHom Ψ φ) n

/-- The component functors of the precomposed δ-functor. -/
@[simp]
theorem precomp_functor (n : ℕ) : (F.precomp Ψ).functor n = Ψ ⋙ F.functor n := rfl

/-- The connecting morphism of the precomposed δ-functor is the connecting morphism of the
original one at the image short exact sequence. -/
@[simp]
theorem precomp_δ {S : ShortComplex A'} (hS : S.ShortExact) (n : ℕ) :
    (F.precomp Ψ).δ hS n = F.δ (hS.map_of_exact Ψ) n := rfl

/-- **A morphism of δ-functors precomposes to a morphism of the precomposed δ-functors.**  Its
degree-`n` component is the whiskering of the degree-`n` component, and the compatibility with the
connecting morphisms is the original compatibility at the image short exact sequence. -/
@[simps]
def precompHom {F G : DeltaFunctor A B} (η : F ⟶ G) : F.precomp Ψ ⟶ G.precomp Ψ where
  app n := Functor.whiskerLeft Ψ (η.app n)
  comm hS n := η.comm (hS.map_of_exact Ψ) n

/-- **A natural transformation of the precomposing exact functors induces a morphism of the
precomposed δ-functors.**  Its degree-`n` component is the whiskering of `η` into `Fⁿ`, and its
compatibility with the connecting morphisms is the naturality of the connecting morphism of `F` in
the short exact sequence (`CategoryTheory.DeltaFunctor.δ_naturality`), applied to the morphism
`Ψ'(S) ⟶ Ψ(S)` of short exact sequences whose components are the components of `η`.

The stage side of the degree induction of [Stacks, Tag 0A37] needs exactly this: its transition
map from the stage `j` to a stage `k` over it is the pullback of cohomology classes followed by
the map induced by the `f`-map of the system, and the second factor is the precomposition of one
cohomology δ-functor along the natural transformation `ev_j ⋙ f⁻¹ ⟶ ev_k` adjoint to that
`f`-map. -/
def precompNatTrans (F : DeltaFunctor A B) {Ψ₁ Ψ₂ : A' ⥤ A} [Ψ₁.Additive]
    [PreservesFiniteLimits Ψ₁] [PreservesFiniteColimits Ψ₁] [Ψ₂.Additive]
    [PreservesFiniteLimits Ψ₂] [PreservesFiniteColimits Ψ₂] (η : Ψ₁ ⟶ Ψ₂) :
    F.precomp Ψ₁ ⟶ F.precomp Ψ₂ where
  app n := Functor.whiskerRight η (F.functor n)
  comm {S} hS n := F.δ_naturality (hS.map_of_exact Ψ₁) (hS.map_of_exact Ψ₂)
    { τ₁ := η.app S.X₁
      τ₂ := η.app S.X₂
      τ₃ := η.app S.X₃
      comm₁₂ := (η.naturality S.f).symm
      comm₂₃ := (η.naturality S.g).symm } n

/-- The degree-`n` component of `CategoryTheory.DeltaFunctor.precompNatTrans`. -/
@[simp]
theorem precompNatTrans_app (F : DeltaFunctor A B) {Ψ₁ Ψ₂ : A' ⥤ A} [Ψ₁.Additive]
    [PreservesFiniteLimits Ψ₁] [PreservesFiniteColimits Ψ₁] [Ψ₂.Additive]
    [PreservesFiniteLimits Ψ₂] [PreservesFiniteColimits Ψ₂] (η : Ψ₁ ⟶ Ψ₂) (n : ℕ) :
    (F.precompNatTrans η).app n = Functor.whiskerRight η (F.functor n) := rfl

/-- **The precomposition of an effaceable δ-functor with an exact functor is effaceable**, as soon
as the effacing monomorphisms are available in the source of the exact functor: if every object
`X` of `A'` admits a monomorphism into an object `E` with `Fⁿ⁺¹(Ψ E) = 0` for every `n`, then
`Ψ ⋙ F` is effaceable, hence universal by Stacks 010T.

This is the shape in which the effaceability input of the degree induction of Stacks 0A37 arrives:
a monomorphism of a system into a stagewise injective one, together with the vanishing of the
positive-degree cohomology of the latter. -/
theorem Effaceable.precomp
    (heff : ∀ X : A', ∃ (E : A') (ι : X ⟶ E), Mono ι ∧
      ∀ n : ℕ, IsZero ((F.functor (n + 1)).obj (Ψ.obj E))) :
    (F.precomp Ψ).Effaceable where
  nonempty X n := by
    obtain ⟨E, ι, hι, hz⟩ := heff X
    exact ⟨{ I := E, ι := ι, mono := hι, map_ι := (hz n).eq_of_tgt _ _ }⟩

end CategoryTheory.DeltaFunctor

end
