module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.HomologicalConstructions

/-! # Two more constructions of morphisms of homological δ-functors

`StacksFrontier/CategoryTheory/Abelian/DeltaFunctor/HomologicalConstructions.lean` builds a
homological δ-functor out of a functor into chain complexes and recognizes coeffaceability. This
file adds the two pieces of API that a comparison of δ-functors *on different categories* needs,
and which that file does not have:

* precomposition of a homological δ-functor, and of a morphism of them, with an exact additive
  functor — the δ-functor whose degree-`n` part is `W ⋙ Hₙ`, with the connecting morphism of the
  image short exact sequence;
* a morphism of the δ-functors attached by
  `Stacks.CategoryHomology.HomologicalDeltaFunctor.ofChainComplexFunctor` to two
  `ChainComplex`-valued functors, from a natural transformation between them.

Both are needed to compare the homology of a category along a functor `f : C' ⥤ C`: the
δ-functor `F ↦ Hₙ(C', f⁻¹F)` is a precomposition, and the explicit chain map of Stacks 08PH is a
natural transformation of simplicial replacement complex functors.

## Main definitions

* `Stacks.CategoryHomology.HomologicalDeltaFunctor.precomp` and
  `Stacks.CategoryHomology.HomologicalDeltaFunctor.Hom.precomp`.
* `Stacks.CategoryHomology.HomologicalDeltaFunctor.homOfChainComplexNatTrans`.

## Implementation notes

Every clause of `precomp` is the corresponding clause of `H` at the image sequence
`S.map W`, which is short exact by `CategoryTheory.ShortComplex.ShortExact.map_of_exact`. No
rewriting is needed because `(S.map W).f`, `(S.map W).X₁` and
`(S.map (W ⋙ H.functor n))` are the `W`-image data on the nose: `ShortComplex.map` is a
structure literal and `ShortComplex.map_comp` holds by `rfl`.

As in `HomologicalConstructions.lean`, the source hypothesis is `[Abelian A]` alone, never
`[Abelian A]` beside `[Preadditive A]`.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category

universe v v' v'' u u' u''

namespace Stacks.CategoryHomology.HomologicalDeltaFunctor

section Precompose

variable {A : Type u} [Category.{v} A] [Abelian A] {A' : Type u'} [Category.{v'} A'] [Abelian A']
  {B : Type u''} [Category.{v''} B] [Preadditive B] (W : A ⥤ A') [W.Additive]
  [PreservesFiniteLimits W] [PreservesFiniteColimits W]

/-- **Precomposition of a homological δ-functor with an exact additive functor.** The degree-`n`
functor is `W ⋙ Hₙ` and the connecting morphism of a short exact sequence `S` is the connecting
morphism of `H` at the image sequence `S.map W`, which is short exact because `W` is exact. -/
def precomp (H : HomologicalDeltaFunctor A' B) : HomologicalDeltaFunctor A B where
  functor n := W ⋙ H.functor n
  additive n := have := H.additive n; inferInstance
  δ hS n := H.δ (hS.map_of_exact W) n
  map_g_δ hS n := H.map_g_δ (hS.map_of_exact W) n
  δ_map_f hS n := H.δ_map_f (hS.map_of_exact W) n
  epi_map_g hS := H.epi_map_g (hS.map_of_exact W)
  exact_map hS n := H.exact_map (hS.map_of_exact W) n
  exact_δ₁ hS n := H.exact_δ₁ (hS.map_of_exact W) n
  exact_δ₂ hS n := H.exact_δ₂ (hS.map_of_exact W) n
  δ_naturality hS hT φ n :=
    H.δ_naturality (hS.map_of_exact W) (hT.map_of_exact W) (W.mapShortComplex.map φ) n

/-- The degree-`n` functor of a precomposition. Deliberately not a `simp` lemma: it rewrites a
whole functor. -/
lemma precomp_functor (H : HomologicalDeltaFunctor A' B) (n : ℕ) :
    (H.precomp W).functor n = W ⋙ H.functor n :=
  rfl

/-- The connecting morphism of a precomposition. Not a `simp` lemma, for the same reason. -/
lemma precomp_δ (H : HomologicalDeltaFunctor A' B) {S : ShortComplex A} (hS : S.ShortExact)
    (n : ℕ) :
    (H.precomp W).δ hS n = H.δ (hS.map_of_exact W) n :=
  rfl

/-- **Precomposition of a morphism of homological δ-functors with an exact additive functor.** -/
def Hom.precomp {H G : HomologicalDeltaFunctor A' B} (η : H ⟶ G) : H.precomp W ⟶ G.precomp W where
  app n := Functor.whiskerLeft W (η.app n)
  comm hS n := η.comm (hS.map_of_exact W) n

/-- The components of `Stacks.CategoryHomology.HomologicalDeltaFunctor.Hom.precomp`. -/
@[simp]
lemma Hom.precomp_app {H G : HomologicalDeltaFunctor A' B} (η : H ⟶ G) (n : ℕ) :
    (Hom.precomp W η).app n = Functor.whiskerLeft W (η.app n) :=
  rfl

end Precompose

section ChainComplexNatTrans

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B] [Abelian B]

/-- **A natural transformation of short-exactness-preserving `ChainComplex`-valued functors
induces a morphism of the homological δ-functors they define.** The degree-`n` component is the
map it induces on homology in degree `n`, and the compatibility with the connecting morphisms is
`HomologicalComplex.HomologySequence.δ_naturality` for the induced morphism of short complexes of
complexes. -/
def homOfChainComplexNatTrans {K L : A ⥤ ChainComplex B ℕ} [K.Additive] [L.Additive]
    (hK : ∀ {S : ShortComplex A}, S.ShortExact → (S.map K).ShortExact)
    (hL : ∀ {S : ShortComplex A}, S.ShortExact → (S.map L).ShortExact) (α : K ⟶ L) :
    ofChainComplexFunctor K hK ⟶ ofChainComplexFunctor L hL where
  app n := Functor.whiskerRight α (HomologicalComplex.homologyFunctor B (ComplexShape.down ℕ) n)
  comm hS n :=
    HomologicalComplex.HomologySequence.δ_naturality (ShortComplex.mapNatTrans _ α)
      (hK hS) (hL hS) (n + 1) n rfl

/-- The components of
`Stacks.CategoryHomology.HomologicalDeltaFunctor.homOfChainComplexNatTrans`. -/
@[simp]
lemma homOfChainComplexNatTrans_app {K L : A ⥤ ChainComplex B ℕ} [K.Additive] [L.Additive]
    (hK : ∀ {S : ShortComplex A}, S.ShortExact → (S.map K).ShortExact)
    (hL : ∀ {S : ShortComplex A}, S.ShortExact → (S.map L).ShortExact) (α : K ⟶ L) (n : ℕ) :
    (homOfChainComplexNatTrans hK hL α).app n =
      Functor.whiskerRight α (HomologicalComplex.homologyFunctor B (ComplexShape.down ℕ) n) :=
  rfl

variable {A' : Type u''} [Category.{v''} A'] [Abelian A'] (W : A ⥤ A') [W.Additive]
  [PreservesFiniteLimits W] [PreservesFiniteColimits W]

/-- **The mixed form of `homOfChainComplexNatTrans`**: a natural transformation `W ⋙ K ⟶ L`,
where `K` is a `ChainComplex`-valued functor on `A'` and `L` one on `A`, induces a morphism from
the precomposition of the δ-functor of `K` with `W` to the δ-functor of `L`. This is the shape
the comparison of the homology of a category along a functor has: the source side is the
simplicial replacement over the other category, applied to the restricted presheaf. -/
def precompHomOfChainComplexNatTrans {K : A' ⥤ ChainComplex B ℕ} [K.Additive]
    {L : A ⥤ ChainComplex B ℕ} [L.Additive]
    (hK : ∀ {S : ShortComplex A'}, S.ShortExact → (S.map K).ShortExact)
    (hL : ∀ {S : ShortComplex A}, S.ShortExact → (S.map L).ShortExact) (α : W ⋙ K ⟶ L) :
    (ofChainComplexFunctor K hK).precomp W ⟶ ofChainComplexFunctor L hL where
  app n := Functor.whiskerRight α (HomologicalComplex.homologyFunctor B (ComplexShape.down ℕ) n)
  comm hS n :=
    HomologicalComplex.HomologySequence.δ_naturality (ShortComplex.mapNatTrans _ α)
      (hK (hS.map_of_exact W)) (hL hS) (n + 1) n rfl

/-- The components of
`Stacks.CategoryHomology.HomologicalDeltaFunctor.precompHomOfChainComplexNatTrans`. -/
@[simp]
lemma precompHomOfChainComplexNatTrans_app {K : A' ⥤ ChainComplex B ℕ} [K.Additive]
    {L : A ⥤ ChainComplex B ℕ} [L.Additive]
    (hK : ∀ {S : ShortComplex A'}, S.ShortExact → (S.map K).ShortExact)
    (hL : ∀ {S : ShortComplex A}, S.ShortExact → (S.map L).ShortExact) (α : W ⋙ K ⟶ L)
    (n : ℕ) :
    (precompHomOfChainComplexNatTrans W hK hL α).app n =
      Functor.whiskerRight α (HomologicalComplex.homologyFunctor B (ComplexShape.down ℕ) n) :=
  rfl

end ChainComplexNatTrans

end Stacks.CategoryHomology.HomologicalDeltaFunctor

end
