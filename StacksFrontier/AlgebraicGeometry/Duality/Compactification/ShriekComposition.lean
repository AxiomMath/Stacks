module

public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.CompositionChase
public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.CompositionData
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChangeHorizontal
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.TwistedInverseImageRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.Compactification.ShriekRefinementBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChangeRestrictionComparison

/-!
# The canonical isomorphism `(g ∘ f)^! ≅ f^! ∘ g^!` of Tag 0ATX

In the situation of [Stacks, Tag 0F42] let `f : X ⟶ Y` and `g : Y ⟶ Z` be composable morphisms of
`AlgebraicGeometry.FTS S` over a Noetherian `S`. [Stacks, Tag 0ATX] says that there is a canonical
isomorphism `(g ∘ f)^! → f^! ∘ g^!`. This file carries out the source's proof.

*The construction.* A choice `D : Stacks.Duality.CompositionData f g` is a compactification
`i : Y ⟶ Ȳ` of `Y` over `Z` together with a compactification `X ⟶ X̄` of `X` over `Ȳ`; it
determines the compactification `X ⟶ X̄ ⟶ Z` of `g ∘ f` and the compactification `X ⟶ U ⟶ Y` of
`f`, where `U` is the inverse image of `Y` in `X̄`. The source's map

  `(g ∘ f)^! = (j' ∘ j)^* ∘ ā ∘ b̄ = j^* ∘ (j')^* ∘ ā ∘ b̄ ⟶ j^* ∘ ā' ∘ i^* ∘ b̄ = f^! ∘ g^!`

is `Stacks.Duality.CompositionData.compMap`, with `γ : (j')^* ∘ ā ⟶ ā' ∘ i^*` the base change map
of [Stacks, Tag 0AA6] for the cartesian square `U ⟶ X̄` over `Y ⟶ Ȳ`
(`Stacks.Duality.CompositionData.baseChange`) and `ā ∘ b̄` read as `(X̄ ⟶ Z)^×` through the
comparison of [Stacks, Tag 0ATX] for the twisted inverse image. On `D⁺_QCoh(𝒪_Z)` it is invertible
by [Stacks, Tag 0A9P], which is the isomorphism `Stacks.Duality.CompositionData.compIso`.

*Independence of the choice.* For a morphism of choices with dense source the source compares the
two maps through the squares `A, …, F` of its proof; that diagram chase, with every functor and
transformation a variable, is `Stacks.Duality.compositionChase`, whose inputs are
[Stacks, Tag 0ATR] (`Stacks.Duality.CompositionData.Hom.h₁`), [Stacks, Tag 0ATQ] twice (`h₂`,
`h₃`), the identification of the two stacks (`h₄`) and two coherences of the comparison of
[Stacks, Tag 0ATX] for the twisted inverse image (`h₅`, `h₆`). The result is
`Stacks.Duality.CompositionData.Hom.naturality`, read as an identity of isomorphisms out of
`D⁺_QCoh(𝒪_Z)` in `Stacks.Duality.CompositionData.Hom.compIso_naturality`. Two choices are
dominated by a third (`Stacks.Duality.CompositionData.exists_hom_hom`), so the isomorphisms of any
two choices agree through the canonical comparisons of [Stacks, Tag 0AA0]
(`Stacks.Duality.CompositionData.compIso_independent`).

*The canonical isomorphism.* `Stacks.Duality.upperShriekCompIsoAtModel` is the isomorphism at
arbitrary compactifications of `g ∘ f`, `f` and `g`, read through the comparisons of
[Stacks, Tag 0AA0] from a choice through the given compactification of `g` (which exists by
[Stacks, Tag 0A9Z]). It agrees with the source's construction for **every** choice
(`Stacks.Duality.upperShriekCompIsoAtModel_choice`) and is compatible with the comparisons of
[Stacks, Tag 0AA0] in all three compactifications
(`Stacks.Duality.upperShriekCompIsoAtModel_naturality`) — which is what "canonical" means in the
source.

## Implementation notes

*The spelling.* The functors are written through the abbreviations `Stacks.Duality.tw` and
`Stacks.Duality.pb` for morphisms of Noetherian schemes, and every morphism with the type it has in
the construction (`CompositionData.topImm`, `CompositionData.baseImm`, …). Comparisons between
this spelling and the one of the compactification API are made once, at the level of isomorphisms
or natural transformations (`refinementIso_outer_hom` and its siblings, `compIso`), never at the
level of components: a conversion read through `.app` makes the kernel reduce the derived functors
and does not fit a declaration's budget. Every component-level identity is proved with the
categories as variables (`Stacks.Duality.compositionChase`, `Stacks.Duality.naturalityShape`,
`Stacks.Duality.isoNaturalityShape`, …) and instantiated.

## References

* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 0A9P](https://stacks.math.columbia.edu/tag/0A9P)
* [Stacks Project, Tag 0A9I](https://stacks.math.columbia.edu/tag/0A9I)
* [Stacks Project, Tag 0ATQ](https://stacks.math.columbia.edu/tag/0ATQ)
* [Stacks Project, Tag 0ATR](https://stacks.math.columbia.edu/tag/0ATR)
* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
* [Stacks Project, Tag 0A9Z](https://stacks.math.columbia.edu/tag/0A9Z)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u

namespace Stacks.Duality

section Chases

variable {𝒞 : Type*} [Category 𝒞]

/-- The bookkeeping of `Stacks.Duality.compN_square`, with variable data. -/
theorem squareChase {P₀ P₁ P₂ P₃ Q R S S' Q' R' : 𝒞} (k : P₀ ⟶ P₁) (A : P₁ ⟶ Q) (B : Q ⟶ R)
    (a₁ : P₁ ⟶ P₂) (T : P₂ ⟶ S) (Ih : S ⟶ R) (C' : P₀ ⟶ Q') (D' : Q' ⟶ R') (a₂ : P₀ ⟶ P₃)
    (T' : P₃ ⟶ S') (Jh : S' ⟶ R') (Ji : R' ⟶ S') (H : S' ⟶ S) (c₃ : P₃ ⟶ P₂)
    (hL : A ≫ B = a₁ ≫ T ≫ Ih) (hR : C' ≫ D' = a₂ ≫ T' ≫ Jh) (hJ : Jh ≫ Ji = 𝟙 S')
    (n : c₃ ≫ T = T' ≫ H) (t : k ≫ a₁ = a₂ ≫ c₃) :
    (k ≫ A) ≫ B = C' ≫ D' ≫ Ji ≫ H ≫ Ih := by
  rw [Category.assoc, hL, reassoc_of% t, reassoc_of% n, reassoc_of% hR, reassoc_of% hJ]

/-- The bookkeeping of `Stacks.Duality.compN_unit`, with variable data. -/
theorem unitChase {P Q R : 𝒞} (a : P ⟶ Q) (b : Q ⟶ P) (Y : Q ⟶ P) (Z : P ⟶ P) (X : P ⟶ R)
    (hab : a ≫ b = 𝟙 P) (hY : Y = b ≫ 𝟙 P) (hZ : Z = 𝟙 P) :
    X = a ≫ Y ≫ Z ≫ X := by
  rw [hY, hZ]; simp [reassoc_of% hab]

/-- The bookkeeping of `Stacks.Duality.compN_cocycleR`, with variable data. -/
theorem cocycleChase {P Q R T : 𝒞} (X₁ : P ⟶ Q) (X₂ : Q ⟶ R) (Y : P ⟶ T) (I : T ≅ R)
    (h : Y = X₁ ≫ X₂ ≫ I.inv) : X₁ ≫ X₂ = 𝟙 P ≫ Y ≫ I.hom := by
  rw [h]; simp


end Chases

/-! ### Twisted inverse image and derived pullback between Noetherian schemes -/

/-- The source of `Over.mk h` is the source of `h`. -/
instance isNoetherian_overMk_left {A B : Scheme.{u}} [IsNoetherian A] (h : A ⟶ B) :
    IsNoetherian (Over.mk h).left :=
  inferInstanceAs (IsNoetherian A)

section Noetherian

variable {A B : Scheme.{u}} [IsNoetherian A] [IsNoetherian B] (h : A ⟶ B)

/-- [Stacks, Tag 08D5] part (1) for a morphism of Noetherian schemes. -/
theorem noethPush : ∀ (K : quasiCoherentDerivedCategory A) (i : ℤ),
    ((DerivedCategory.homologyFunctor B.Modules i).obj
      ((derivedPushforward h).obj K.obj)).IsQuasicoherent :=
  let : QuasiSeparated h := QuasiSeparated.of_quasiSeparatedSpace h
  isQuasicoherent_homology_derivedPushforward_of_qcqs h

/-- [Stacks, Tag 0A9E] for a morphism of Noetherian schemes. -/
theorem noethAdj : (quasiCoherentDerivedPushforward h (noethPush h)).IsLeftAdjoint :=
  let : QuasiSeparated h := QuasiSeparated.of_quasiSeparatedSpace h
  isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward h

/-- The twisted inverse image `h^×` of a morphism of Noetherian schemes. -/
abbrev tw : quasiCoherentDerivedCategory B ⥤ quasiCoherentDerivedCategory A :=
  letI := noethAdj h
  twistedInverseImage h (noethPush h)

/-- The derived pullback `Lh^*` on the quasi-coherent derived categories. -/
abbrev pb : quasiCoherentDerivedCategory B ⥤ quasiCoherentDerivedCategory A :=
  quasiCoherentDerivedPullback h (isQuasicoherent_homology_derivedPullback' h)

end Noetherian

section NoetherianMaps

variable {A B C : Scheme.{u}} [IsNoetherian A] [IsNoetherian B] [IsNoetherian C]

/-- The comparison `(a ≫ b)^× ≅ b^× ⋙ a^×` of [Stacks, Tag 0ATX] for the twisted inverse image,
between Noetherian schemes. -/
abbrev compN (a : A ⟶ B) (b : B ⟶ C) : tw (a ≫ b) ≅ tw b ⋙ tw a :=
  letI := noethAdj a
  letI := noethAdj b
  letI := noethAdj (a ≫ b)
  twistedInverseImageCompIso a b (noethPush a) (noethPush b) (noethPush (a ≫ b))

/-- The identification of the twisted inverse images of two equal morphisms. -/
abbrev congrN {a a' : A ⟶ B} (e : a = a') : tw a ≅ tw a' :=
  letI := noethAdj a
  letI := noethAdj a'
  twistedInverseImageCongrIso (noethPush a) (noethPush a') e

/-- The identification of the derived pullbacks along two equal morphisms. -/
abbrev pbCongrN {a a' : A ⟶ B} (e : a = a') : pb a ≅ pb a' :=
  eqToIso (by subst e; rfl)

/-- The composition formula `Lb^* ⋙ La^* ≅ L(a ≫ b)^*` between Noetherian schemes. -/
abbrev pbCompN (a : A ⟶ B) (b : B ⟶ C) : pb b ⋙ pb a ≅ pb (a ≫ b) :=
  quasiCoherentDerivedPullbackCompIsoConj a b (noethPush a) (noethPush b) (noethPush (a ≫ b))
    (isQuasicoherent_homology_derivedPullback' a) (isQuasicoherent_homology_derivedPullback' b)
    (isQuasicoherent_homology_derivedPullback' (a ≫ b))

/-- The identification `(𝟙_A)^× ≅ 𝟭` for a Noetherian scheme. -/
abbrev idN (A : Scheme.{u}) [IsNoetherian A] : tw (𝟙 A) ≅ 𝟭 _ :=
  twistedInverseImageIdIso A (noethPush (𝟙 A))

/-- The transport along a reflexivity is the identity. -/
@[simp]
theorem congrN_self {a : A ⟶ B} (e : a = a) : congrN e = Iso.refl _ := by
  let := noethAdj a
  exact twistedInverseImageCongrIso_self _ _ _

omit [AlgebraicGeometry.IsNoetherian A] [AlgebraicGeometry.IsNoetherian B] in
/-- The transport along a reflexivity is the identity. -/
@[simp]
theorem pbCongrN_self {a : A ⟶ B} (e : a = a) : pbCongrN e = Iso.refl _ := rfl

/-- Transporting the first factor of the comparison of [Stacks, Tag 0ATX] along an equality of
morphisms. -/
theorem congrN_compN {a a' : A ⟶ B} (e : a = a') (b : B ⟶ C) (e₂ : a ≫ b = a' ≫ b)
    (K : quasiCoherentDerivedCategory C) :
    (congrN e₂).hom.app K ≫ (compN a' b).hom.app K =
      (compN a b).hom.app K ≫ (congrN e).hom.app ((tw b).obj K) := by
  subst e
  simp only [congrN_self, Iso.refl_hom, NatTrans.id_app]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Two transports compose, read at an object. -/
theorem congrN_trans_app {a a' a'' : A ⟶ B} (e : a = a') (e' : a' = a'') (e'' : a = a'')
    (K : quasiCoherentDerivedCategory B) :
    (congrN e).hom.app K ≫ (congrN e').hom.app K = (congrN e'').hom.app K := by
  subst e e'
  simp only [congrN_self, Iso.refl_hom, NatTrans.id_app]
  exact Category.id_comp _

/-- Transporting along an equality of morphisms and back is the identity. -/
theorem congrN_trans {a a' a'' : A ⟶ B} (e : a = a') (e' : a' = a'') :
    congrN e ≪≫ congrN e' = congrN (e.trans e') := by
  subst e e'
  simp only [congrN_self]
  exact Iso.trans_refl _

/-- The transport along `a ≫ b = a ≫ b`, followed by the comparison, is the comparison. -/
private theorem congrN_rfl_symm_trans_compN (a : A ⟶ B) (b : B ⟶ C) :
    congrN (rfl : a ≫ b = a ≫ b).symm ≪≫ compN a b = compN a b := by
  rw [congrN_self]; exact Iso.refl_trans _

end NoetherianMaps

section BaseChangeN

variable {X' X Y' Y : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] [IsNoetherian Y']
  [IsNoetherian Y]

/-- The transformation `ξ` of [Stacks, Tag 0A9K] for a cartesian square of Noetherian schemes. -/
abbrev xiN {t : X' ⟶ X} {l : X' ⟶ Y'} {r : X ⟶ Y} {b : Y' ⟶ Y} (sq : IsPullback t l r b) :=
  letI := noethAdj r
  letI := noethAdj l
  twistedInverseImagePushforwardBaseChange t l r b (noethPush t) (noethPush r) (noethPush l)
    (noethPush b) sq

/-- The base change map of [Stacks, Tag 0AA6] for a cartesian square of Noetherian schemes. -/
abbrev bcN {t : X' ⟶ X} {l : X' ⟶ Y'} {r : X ⟶ Y} {b : Y' ⟶ Y} (sq : IsPullback t l r b)
    [IsIso (xiN sq)] : tw r ⋙ pb t ⟶ pb b ⋙ tw l :=
  letI := noethAdj r
  letI := noethAdj l
  twistedInverseImageBaseChangeMap t l r b (noethPush t) (noethPush r) (noethPush l)
    (noethPush b) sq

/-- **[Stacks, Tag 0A9K] for a cartesian square of Noetherian schemes whose horizontal edges are
open immersions.** -/
instance isIso_xiN_of_isOpenImmersion {t : X' ⟶ X} {l : X' ⟶ Y'} {r : X ⟶ Y} {b : Y' ⟶ Y}
    [IsOpenImmersion t] [IsOpenImmersion b] (sq : IsPullback t l r b) : IsIso (xiN sq) :=
  letI := noethAdj r
  letI := noethAdj l
  OpenImmersion.isIso_twistedInverseImagePushforwardBaseChange_of_isOpenImmersion t l r b
    (noethPush t) (noethPush r) (noethPush l) (noethPush b) sq

/-- The base change map of [Stacks, Tag 0AA6] for a cartesian square of Noetherian schemes whose
horizontal edges are open immersions, where [Stacks, Tag 0A9K] supplies the invertibility of
`ξ`. -/
abbrev bcO {t : X' ⟶ X} {l : X' ⟶ Y'} {r : X ⟶ Y} {b : Y' ⟶ Y} [IsOpenImmersion t]
    [IsOpenImmersion b] (sq : IsPullback t l r b) : tw r ⋙ pb t ⟶ pb b ⋙ tw l :=
  @bcN _ _ _ _ _ _ _ _ t l r b sq (isIso_xiN_of_isOpenImmersion sq)

/-- **The base change map along equal squares.** -/
theorem bcN_congr {t t' : X' ⟶ X} {l l' : X' ⟶ Y'} {r r' : X ⟶ Y} {b b' : Y' ⟶ Y}
    (ht : t = t') (hl : l = l') (hr : r = r') (hb : b = b') (sq : IsPullback t l r b)
    (sq' : IsPullback t' l' r' b') [IsIso (xiN sq)] [IsIso (xiN sq')]
    (M : quasiCoherentDerivedCategory Y) :
    (bcN sq').app M = (pb t').map ((congrN hr).inv.app M) ≫ (pbCongrN ht).inv.app _ ≫
      (bcN sq).app M ≫ (tw l).map ((pbCongrN hb).hom.app M) ≫
        (congrN hl).hom.app ((pb b').obj M) := by
  subst ht hl hr hb
  simp only [congrN_self, pbCongrN_self, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id]
  rw [(pb t).map_id, (tw l).map_id, Category.id_comp]
  exact (Category.comp_id _).symm

end BaseChangeN


section Coherence

variable {X₁ X₂ Y₁ Y₂ Zs : Scheme.{u}} [IsNoetherian X₁] [IsNoetherian X₂] [IsNoetherian Y₁]
  [IsNoetherian Y₂] [IsNoetherian Zs]

/-- The cocycle identity of [Stacks, Tag 0ATY] for the twisted inverse image between Noetherian
schemes. -/
theorem compN_cocycle {A B C D : Scheme.{u}} [IsNoetherian A] [IsNoetherian B] [IsNoetherian C]
    [IsNoetherian D] (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (K : quasiCoherentDerivedCategory D) :
    (compN (a ≫ b) c).hom.app K =
      (compN a (b ≫ c)).hom.app K ≫ (tw a).map ((compN b c).hom.app K) ≫
        (compN a b).inv.app ((tw c).obj K) := by
  let := noethAdj a
  let := noethAdj b
  let := noethAdj c
  let := noethAdj (a ≫ b)
  let := noethAdj (b ≫ c)
  let := noethAdj (a ≫ b ≫ c)
  exact twistedInverseImageCompIso_cocycle_app (noethPush a) (noethPush b) (noethPush c)
    (noethPush (a ≫ b)) (noethPush (b ≫ c)) (noethPush (a ≫ b ≫ c)) K

/-- The transport along the associativity of composition is the identity. -/
theorem congrN_assoc_app {A B C D : Scheme.{u}} [IsNoetherian A] [IsNoetherian B]
    [IsNoetherian C] [IsNoetherian D] (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (K : quasiCoherentDerivedCategory D) :
    (congrN (Category.assoc a b c).symm).hom.app K = 𝟙 ((tw (a ≫ b ≫ c)).obj K) := by
  simp only [congrN, twistedInverseImageCongrIso, eqToIso.hom, eqToHom_app]
  exact eqToHom_refl _ _

/-- The cocycle identity of [Stacks, Tag 0ATY] with the reassociation made explicit, so that no
two spellings of a triple composite of morphisms of schemes have to be compared. -/
theorem compN_cocycleR {A B C D : Scheme.{u}} [IsNoetherian A] [IsNoetherian B] [IsNoetherian C]
    [IsNoetherian D] (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (K : quasiCoherentDerivedCategory D) :
    (compN a (b ≫ c)).hom.app K ≫ (tw a).map ((compN b c).hom.app K) =
      (congrN (Category.assoc a b c).symm).hom.app K ≫ (compN (a ≫ b) c).hom.app K ≫
        (compN a b).hom.app ((tw c).obj K) := by
  rw [congrN_assoc_app]
  exact cocycleChase _ _ _ ((compN a b).app ((tw c).obj K)) (compN_cocycle a b c K)

/-- **The comparisons of [Stacks, Tag 0ATX] along the two factorizations of a commutative square
of twisted inverse images agree.** For `p₁ ≫ d = e ≫ p₂` and `d ≫ b₂ = b₁`, reading
`(p₁ ≫ b₁)^×` through `e` and then `p₂ ≫ b₂`, or through `p₁` and then `b₁ = d ≫ b₂`, gives the
same isomorphism with `b₂^× ⋙ (e ≫ p₂)^×`. This is the hypothesis `h₅` of
`Stacks.Duality.compositionChase`. -/
theorem compN_square (p₁ : X₁ ⟶ Y₁) (p₂ : X₂ ⟶ Y₂) (e : X₁ ⟶ X₂) (d : Y₁ ⟶ Y₂) (b₁ : Y₁ ⟶ Zs)
    (b₂ : Y₂ ⟶ Zs) (hb : d ≫ b₂ = b₁) (hpe : p₁ ≫ d = e ≫ p₂) (hk : p₁ ≫ b₁ = e ≫ p₂ ≫ b₂)
    (K : quasiCoherentDerivedCategory Zs) :
    (congrN hk ≪≫ compN e (p₂ ≫ b₂)).hom.app K ≫ (tw e).map ((compN p₂ b₂).hom.app K) =
      (compN p₁ b₁).hom.app K ≫ (tw p₁).map ((congrN hb.symm ≪≫ compN d b₂).hom.app K) ≫
        (compN p₁ d).inv.app ((tw b₂).obj K) ≫ (congrN hpe).hom.app ((tw b₂).obj K) ≫
          (compN e p₂).hom.app ((tw b₂).obj K) := by
  subst hb
  rw [congrN_rfl_symm_trans_compN]
  simp only [Iso.trans_hom, NatTrans.comp_app]
  have e₂ : (p₁ ≫ d) ≫ b₂ = (e ≫ p₂) ≫ b₂ := by rw [hpe]
  have hE : p₁ ≫ d ≫ b₂ = (e ≫ p₂) ≫ b₂ := by rw [← e₂, Category.assoc]
  exact squareChase ((congrN hk).hom.app K) ((compN e (p₂ ≫ b₂)).hom.app K)
    ((tw e).map ((compN p₂ b₂).hom.app K)) ((congrN (Category.assoc e p₂ b₂).symm).hom.app K)
    ((compN (e ≫ p₂) b₂).hom.app K) ((compN e p₂).hom.app ((tw b₂).obj K))
    ((compN p₁ (d ≫ b₂)).hom.app K) ((tw p₁).map ((compN d b₂).hom.app K))
    ((congrN (Category.assoc p₁ d b₂).symm).hom.app K) ((compN (p₁ ≫ d) b₂).hom.app K)
    ((compN p₁ d).hom.app ((tw b₂).obj K)) ((compN p₁ d).inv.app ((tw b₂).obj K))
    ((congrN hpe).hom.app ((tw b₂).obj K))
    ((congrN e₂).hom.app K) (compN_cocycleR e p₂ b₂ K)
    (compN_cocycleR p₁ d b₂ K) (Iso.hom_inv_id_app _ _) (congrN_compN hpe b₂ e₂ K)
    ((congrN_trans_app hk (Category.assoc e p₂ b₂).symm hE K).trans
      (congrN_trans_app (Category.assoc p₁ d b₂).symm e₂ hE K).symm)

/-- **The right unit law for the comparison of [Stacks, Tag 0ATX], read through a transport.**
For `e' ≫ q₂ = q₁`, the comparison `q₁^× ≅ q₂^× ⋙ e'^×` is the identification of `q₁^×` with
`(q₁ ≫ 𝟙)^×` through `(𝟙)^× ≅ 𝟭`, transported along `q₁ ≫ 𝟙 = e' ≫ q₂`. This is the hypothesis
`h₆` of `Stacks.Duality.compositionChase`. -/
theorem compN_unit (q₁ : X₁ ⟶ Y₁) (q₂ : X₂ ⟶ Y₁) (e' : X₁ ⟶ X₂) (hq : e' ≫ q₂ = q₁)
    (hq' : q₁ ≫ 𝟙 Y₁ = e' ≫ q₂) (M : quasiCoherentDerivedCategory Y₁) :
    (congrN hq.symm ≪≫ compN e' q₂).hom.app M =
      (tw q₁).map ((idN Y₁).inv.app M) ≫ (compN q₁ (𝟙 Y₁)).inv.app M ≫
        (congrN hq').hom.app M ≫ (compN e' q₂).hom.app M := by
  subst hq
  let := noethAdj (e' ≫ q₂)
  have hu := congrArg (fun i => i.inv.app M)
    (twistedInverseImageCompIso_comp_id_eq_leftUnitor_symm (e' ≫ q₂) (noethPush (e' ≫ q₂))
        (noethPush (𝟙 Y₁)))
  simp only [Iso.symm_inv, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hu
  have hr : (congrN hq').hom.app M = 𝟙 _ := by
    have : congrN hq' = congrN (rfl : e' ≫ q₂ = e' ≫ q₂) := rfl
    rw [this, congrN_self]; rfl
  rw [congrN_rfl_symm_trans_compN]
  exact unitChase _ _ _ _ _ ((tw (e' ≫ q₂)).mapIso ((idN Y₁).app M)).inv_hom_id hu hr

end Coherence

section CongrGeneral

variable {X' X Y' Y : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] [IsNoetherian Y']
  [IsNoetherian Y]

/-- **The base change map of [Stacks, Tag 0AA6] along a square whose horizontal edges are replaced
by equal ones.** -/
theorem bcN_congr_horiz {t t' : X' ⟶ X} {l : X' ⟶ Y'} {r : X ⟶ Y} {b b' : Y' ⟶ Y}
    [IsOpenImmersion t] [IsOpenImmersion t'] [IsOpenImmersion b] [IsOpenImmersion b']
    (et : t' = t) (eb : b' = b) (sq : IsPullback t l r b) (sq' : IsPullback t' l r b') :
    bcO sq' = Functor.whiskerLeft (tw r) (pbCongrN et).hom ≫ bcO sq ≫
      Functor.whiskerRight (pbCongrN eb).inv (tw l) := by
  subst et eb
  simp only [pbCongrN_self, Iso.refl_hom, Iso.refl_inv, Functor.whiskerLeft_id',
    Functor.whiskerRight_id', Category.id_comp, Category.comp_id]

/-- **The base change map of [Stacks, Tag 0AA6] along a square whose vertical edges are replaced by
equal ones.** -/
theorem bcN_congr_vert {t : X' ⟶ X} {l l' : X' ⟶ Y'} {r r' : X ⟶ Y} {b : Y' ⟶ Y}
    [IsOpenImmersion t] [IsOpenImmersion b]
    (el : l = l') (er : r = r') (sq : IsPullback t l r b) (sq' : IsPullback t l' r' b) :
    bcO sq = Functor.whiskerRight (congrN er).hom (pb t) ≫ bcO sq' ≫
      Functor.whiskerLeft (pb b) (congrN el).inv := by
  subst el er
  simp only [congrN_self, Iso.refl_hom, Iso.refl_inv, Functor.whiskerLeft_id',
    Functor.whiskerRight_id', Category.id_comp, Category.comp_id]

/-- `Stacks.Duality.bcN_congr_vert` at an object. -/
theorem bcO_congr_vert_app {t : X' ⟶ X} {l l' : X' ⟶ Y'} {r r' : X ⟶ Y} {b : Y' ⟶ Y}
    [IsOpenImmersion t] [IsOpenImmersion b]
    (el : l = l') (er : r = r') (sq : IsPullback t l r b) (sq' : IsPullback t l' r' b)
    (N : quasiCoherentDerivedCategory Y) :
    (bcO sq).app N = (pb t).map ((congrN er).hom.app N) ≫ (bcO sq').app N ≫
      (congrN el).inv.app ((pb b).obj N) := by
  subst el er
  simp only [congrN_self, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  rw [(pb t).map_id, Category.id_comp]
  exact (Category.comp_id _).symm

end CongrGeneral

section Stacking

variable {X' X Y' Y Z' Z : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X] [IsNoetherian Y']
  [IsNoetherian Y] [IsNoetherian Z'] [IsNoetherian Z]

open scoped CategoryTheory.TwoSquare in
/-- **[Stacks, Tag 0ATQ] between Noetherian schemes**, for a vertical stack of two cartesian
squares whose horizontal edges are open immersions. -/
theorem bcN_vcomp {k : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {l : Y' ⟶ Y} {g' : Y' ⟶ Z'}
    {g : Y ⟶ Z} {m : Z' ⟶ Z} [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion m]
    (sq₁ : IsPullback k f' f l) (sq₂ : IsPullback l g' g m) :
    bcN (sq₁.paste_vert sq₂) =
      ((TwoSquare.mk _ _ _ _ (bcN sq₂) ≫ₕ TwoSquare.mk _ _ _ _ (bcN sq₁)).whiskerTop
        (compN f g).hom).whiskerBottom (compN f' g').inv := by
  let := noethAdj f
  let := noethAdj f'
  let := noethAdj g
  let := noethAdj g'
  let := noethAdj (f ≫ g)
  let := noethAdj (f' ≫ g')
  exact twistedInverseImageBaseChangeMap_vcomp k f' f l g' g m (noethPush k) (noethPush f)
    (noethPush f') (noethPush l) (noethPush g) (noethPush g') (noethPush m) (noethPush (f ≫ g))
    (noethPush (f' ≫ g')) sq₁ sq₂

open scoped CategoryTheory.TwoSquare in
/-- **[Stacks, Tag 0ATR] between Noetherian schemes**, for a row of two cartesian squares whose
horizontal edges are open immersions. -/
theorem bcN_hcomp {Xa Xb Xc Ya Yb Yc : Scheme.{u}} [IsNoetherian Xa] [IsNoetherian Xb]
    [IsNoetherian Xc] [IsNoetherian Ya] [IsNoetherian Yb] [IsNoetherian Yc]
    {k' : Xa ⟶ Xb} {k : Xb ⟶ Xc} {f'' : Xa ⟶ Ya} {f' : Xb ⟶ Yb} {f : Xc ⟶ Yc}
    {l' : Ya ⟶ Yb} {l : Yb ⟶ Yc} [IsOpenImmersion k'] [IsOpenImmersion k] [IsOpenImmersion l']
    [IsOpenImmersion l] (sq₁ : IsPullback k' f'' f' l') (sq₂ : IsPullback k f' f l) :
    bcN (sq₁.paste_horiz sq₂) =
      (((TwoSquare.mk _ _ _ _ (bcN sq₂) ≫ᵥ TwoSquare.mk _ _ _ _ (bcN sq₁)).whiskerLeft
        (pbCompN l' l).hom).whiskerRight (pbCompN k' k).inv) := by
  let := noethAdj f
  let := noethAdj f'
  let := noethAdj f''
  exact twistedInverseImageBaseChangeMap_hcomp k' k f'' f' f l' l (noethPush k') (noethPush k)
    (noethPush (k' ≫ k)) (noethPush f'') (noethPush f') (noethPush f) (noethPush l')
    (noethPush l) (noethPush (l' ≫ l)) sq₁ sq₂

end Stacking

/-- **Derived pullback along an open immersion preserves bounded-below cohomology**: it is exact,
so its cohomology sheaves are the restrictions of those of the object. -/
theorem isBoundedBelow_pb_obj {A B : Scheme.{u}} [IsNoetherian A] [IsNoetherian B] (j : A ⟶ B)
    [IsOpenImmersion j] (M : quasiCoherentDerivedCategory B)
    (hM : DerivedCategoryB.IsBoundedBelow M.obj) :
    DerivedCategoryB.IsBoundedBelow ((pb j).obj M).obj := by
  obtain ⟨n₀, h⟩ := hM
  have := pullback_preservesFiniteLimits_of_isOpenImmersion j
  exact ⟨n₀, fun n hn => ((Scheme.Modules.pullback j).map_isZero (h n hn)).of_iso
    (homologyDerivedPullbackIso j M.obj n).symm⟩

variable {S : Scheme.{u}} [IsNoetherian S] {X Y Z : FTS S} {f : X ⟶ Y} {g : Y ⟶ Z}

section Refinement

variable {Xf Yf : FTS S} (h : Xf ⟶ Yf) {j k : CompactificationOf (Over.mk h.left)} (c : j ⟶ k)

/-- `Stacks.Duality.refinementTwistedCompIso` in the spelling of this file. -/
theorem refinementTwistedCompIso_eq_noeth :
    refinementTwistedCompIso h c =
      congrN (CompactificationOf.homMap_comp_toBase c).symm ≪≫
        compN (CompactificationOf.Hom.map c) k.toBase := rfl

/-- `Stacks.Duality.refinementBaseChange` in the spelling of this file. -/
theorem refinementBaseChange_eq_noeth (hc : CompactificationOf.PreservesInterior c) :
    refinementBaseChange h c hc =
      bcN (CompactificationOf.isPullback_of_preservesInterior c hc).flip := rfl

end Refinement

namespace CompositionData

variable (D : CompositionData f g)

/-- `U` is Noetherian. -/
instance : IsNoetherian D.innerSpace := inferInstanceAs (IsNoetherian D.inner.space)

/-- `U ⟶ X̄` is an open immersion. -/
instance : IsOpenImmersion D.innerFst := inferInstanceAs (IsOpenImmersion (pullback.fst _ _))

/-- `U ⟶ X̄` is an open immersion, with source spelled as the ambient scheme of `D.inner`. -/
instance : @IsOpenImmersion D.inner.space D.top.space D.innerFst :=
  inferInstanceAs (IsOpenImmersion (pullback.fst _ _))

omit [AlgebraicGeometry.IsNoetherian S] in
/-- `Stacks.Duality.CompositionData.isPullback_innerFst` with the structure morphism of the
compactification `D.inner` as left edge. -/
theorem isPullback_innerFst' :
    IsPullback D.innerFst D.inner.toBase D.top.toBase D.baseImm :=
  D.isPullback_innerFst

/-- **`(j' ∘ j)^* = j^* ∘ (j')^*`**: the derived pullback along the open immersion of `X` into
`X̄` is the derived pullback along `X ⟶ U` after the one along `U ⟶ X̄`. -/
def restrictCompIso : pb D.topImm ≅ pb D.innerFst ⋙ pb D.innerImmersion :=
  pbCongrN D.innerImmersion_fst.symm ≪≫ (pbCompN D.innerImmersion D.innerFst).symm

/-- **The base change map `γ : (j')^* ∘ ā ⟶ ā' ∘ i^*` of the proof of [Stacks, Tag 0ATX]**, for the
cartesian square `U ⟶ X̄` over `Y ⟶ Ȳ`: the base change map of [Stacks, Tag 0AA6], which along an
open immersion is the map (0A9L) of the source. -/
def baseChange : tw D.top.toBase ⋙ pb D.innerFst ⟶ pb D.baseImm ⋙ tw D.innerSnd :=
  bcO D.isPullback_innerFst

/-- **The comparison `(g ∘ f)^! ⟶ f^! ∘ g^!` of [Stacks, Tag 0ATX] for one choice**, on the
whole of `D_QCoh(𝒪_Z)`:

  `(j' ∘ j)^* ∘ ā ∘ b̄ = j^* ∘ (j')^* ∘ ā ∘ b̄ ⟶ j^* ∘ ā' ∘ i^* ∘ b̄`,

where `ā ∘ b̄` is read as `(X̄ ⟶ Ȳ ⟶ Z)^×` through the comparison of [Stacks, Tag 0ATX] for the
twisted inverse image. -/
def compMap : tw (D.top.toBase ≫ D.base.toBase) ⋙ pb D.topImm ⟶
    tw D.base.toBase ⋙ pb D.baseImm ⋙ tw D.innerSnd ⋙ pb D.innerImmersion :=
  chainMap (compN D.top.toBase D.base.toBase).hom D.restrictCompIso.hom D.baseChange

/-- `Stacks.Duality.CompositionData.compMap` is a `Stacks.Duality.chainMap`. -/
theorem compMap_eq : D.compMap =
    chainMap (compN D.top.toBase D.base.toBase).hom D.restrictCompIso.hom D.baseChange := rfl

/-- The components of `Stacks.Duality.CompositionData.compMap`. -/
theorem compMap_app (K : quasiCoherentDerivedCategory Z.left) :
    D.compMap.app K = (pb D.topImm).map ((compN D.top.toBase D.base.toBase).hom.app K) ≫
      D.restrictCompIso.hom.app ((tw D.top.toBase).obj ((tw D.base.toBase).obj K)) ≫
        (pb D.innerImmersion).map (D.baseChange.app ((tw D.base.toBase).obj K)) :=
  (congrArg (fun φ => NatTrans.app φ K) D.compMap_eq).trans (chainMap_app _ _ _ K)

/-! ### A morphism of choices -/

/-! ### The comparison on `D⁺_QCoh(𝒪_Z)` -/

section Plus

variable (D : CompositionData f g)

/-- The base change map `γ` of the proof of [Stacks, Tag 0ATX] read on `b̄(D⁺_QCoh(𝒪_Z))`; its
invertibility is [Stacks, Tag 0A9P]. -/
abbrev baseChangePlus :=
  Functor.whiskerLeft
    (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Z.left) ⋙ tw D.base.toBase)
    D.baseChange

/-- **[Stacks, Tag 0A9P] for the square `U ⟶ X̄` over `Y ⟶ Ȳ` of a choice**: the base change map
`γ` is invertible on `b̄(D⁺_QCoh(𝒪_Z))`. The morphism `X̄ ⟶ Ȳ` is proper, `Ȳ` is Noetherian and
`Y ⟶ Ȳ` is an open immersion, so [Stacks, Tag 0A9P] (2) applies at every bounded-below object, and
`b̄` carries `D⁺_QCoh(𝒪_Z)` into `D⁺_QCoh(𝒪_Ȳ)` by [Stacks, Tag 0A9I]. -/
instance isIso_baseChangePlus : IsIso D.baseChangePlus := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun K => ?_
  let := noethAdj D.top.toBase
  let := noethAdj D.innerSnd
  exact isIso_twistedInverseImageBaseChangeMap_app_of_isProper D.innerFst D.innerSnd
    D.top.toBase D.baseImm (noethPush D.innerFst) (noethPush D.top.toBase)
    (noethPush D.innerSnd) (noethPush D.baseImm) D.isPullback_innerFst _
    (isBoundedBelow_twistedInverseImage_obj D.base.toBase K.obj K.property)

/-- The comparison is invertible on `D⁺_QCoh(𝒪_Z)` as soon as `γ` is, which is
[Stacks, Tag 0A9P]. -/
instance isIso_compMapPlus :
    IsIso (Functor.whiskerLeft (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Z.left))
      D.compMap) :=
  haveI := D.isIso_baseChangePlus
  isIso_whiskerLeft_chainMap (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Z.left))
    (compN D.top.toBase D.base.toBase) D.restrictCompIso D.baseChange

/-- **The isomorphism `(g ∘ f)^! ≅ f^! ∘ g^!` of [Stacks, Tag 0ATX] for one choice**, on
`D⁺_QCoh(𝒪_Z)`. -/
def compIsoPlus : compactificationUpperShriek (f ≫ g) D.outer ≅
    ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Z.left) ⋙ (tw D.base.toBase ⋙
      pb D.baseImm ⋙ tw D.innerSnd ⋙ pb D.innerImmersion) :=
  @asIso _ _ _ _ (Functor.whiskerLeft (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Z.left))
    D.compMap) D.isIso_compMapPlus

/-- The underlying transformation of `Stacks.Duality.CompositionData.compIsoPlus`. -/
theorem compIsoPlus_hom : D.compIsoPlus.hom =
    (Functor.whiskerLeft (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Z.left)) D.compMap :
      compactificationUpperShriek (f ≫ g) D.outer ⟶
        ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Z.left) ⋙ (tw D.base.toBase ⋙
          pb D.baseImm ⋙ tw D.innerSnd ⋙ pb D.innerImmersion)) := rfl

end Plus

namespace Hom

open CompactificationOf

variable {D₁ D₂ : CompositionData f g} (φ : Hom D₁ D₂)
  (hb : CompactificationOf.PreservesInterior φ.base)
  (ho : CompactificationOf.PreservesInterior φ.outerHom)

omit [AlgebraicGeometry.IsNoetherian S] in
include ho in
/-- The square `A` of the source: `X ⟶ U₁` over `X ⟶ U₂`. -/
theorem sqA : IsPullback D₁.innerImmersion (𝟙 X.left) φ.innerMap D₂.innerImmersion :=
  (CompactificationOf.isPullback_of_preservesInterior φ.innerHom
    (φ.preservesInterior_innerHom ho)).flip

omit [AlgebraicGeometry.IsNoetherian S] in
include ho in
/-- The square `E` of the source: `X ⟶ X̄₁` over `X ⟶ X̄₂`. -/
theorem sqE : IsPullback D₁.topImm (𝟙 X.left) φ.top D₂.topImm :=
  (CompactificationOf.isPullback_of_preservesInterior φ.outerHom ho).flip

omit [AlgebraicGeometry.IsNoetherian S] in
include hb in
/-- The square `D` of the source: `Y ⟶ Ȳ₁` over `Y ⟶ Ȳ₂`. -/
theorem sqD : IsPullback D₁.baseImm (𝟙 Y.left) (Hom.map φ.base) D₂.baseImm :=
  (CompactificationOf.isPullback_of_preservesInterior φ.base hb).flip

omit [AlgebraicGeometry.IsNoetherian S] in
include hb in
/-- The square `F` of the source: `U₁ ⟶ X̄₁` over `U₂ ⟶ X̄₂`. -/
theorem sqF : IsPullback D₁.innerFst φ.innerMap φ.top D₂.innerFst :=
  (φ.isPullback_innerMap hb).flip

include hb ho in
/-- **`γ_E = γ_A ∘ γ_F`**: the hypothesis `h₁` of `Stacks.Duality.compositionChase`, from
[Stacks, Tag 0ATR]. -/
theorem h₁ (M : quasiCoherentDerivedCategory D₂.top.space) :
    (bcO (φ.sqE ho)).app M =
      D₁.restrictCompIso.hom.app ((tw φ.top).obj M) ≫
        (pb D₁.innerImmersion).map ((bcO (φ.sqF hb)).app M) ≫
          (bcO (φ.sqA ho)).app ((pb D₂.innerFst).obj M) ≫
            (tw (𝟙 X.left)).map (D₂.restrictCompIso.inv.app M) :=
  rowChase (pbCongrN D₁.innerImmersion_fst.symm) (pbCongrN D₂.innerImmersion_fst.symm)
    (pbCompN D₁.innerImmersion D₁.innerFst) (pbCompN D₂.innerImmersion D₂.innerFst)
    D₁.restrictCompIso D₂.restrictCompIso rfl rfl (bcO (φ.sqE ho))
    (bcO ((φ.sqA ho).paste_horiz (φ.sqF hb))) (bcO (φ.sqF hb)) (bcO (φ.sqA ho))
    (bcN_congr_horiz D₁.innerImmersion_fst.symm D₂.innerImmersion_fst.symm _ _)
    (bcN_hcomp (φ.sqA ho) (φ.sqF hb)) M

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The left vertical edges of the two stacks of the source agree. -/
theorem hq' : D₁.innerSnd ≫ 𝟙 Y.left = φ.innerMap ≫ D₂.innerSnd :=
  (Category.comp_id _).trans φ.innerMap_snd.symm

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The right vertical edges of the two stacks of the source agree. -/
theorem hp' : D₁.top.toBase ≫ CompactificationOf.Hom.map φ.base = φ.top ≫ D₂.top.toBase :=
  φ.top_comp_toBase.symm

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The structure morphism of `X̄₁` over `Z` factors through `X̄₂`. -/
theorem hk : D₁.top.toBase ≫ D₁.base.toBase = φ.top ≫ D₂.top.toBase ≫ D₂.base.toBase :=
  (CompactificationOf.homMap_comp_toBase φ.outerHom).symm

/-- The comparison `ā₁ ≅ ā₂ ⋙ c̄` for the compactifications of `f ≫ g`. -/
abbrev eK : tw (D₁.top.toBase ≫ D₁.base.toBase) ≅
    tw (D₂.top.toBase ≫ D₂.base.toBase) ⋙ tw φ.top :=
  congrN φ.hk ≪≫ compN φ.top (D₂.top.toBase ≫ D₂.base.toBase)

/-- The comparison for the compactifications of `g`. -/
abbrev eB : tw D₁.base.toBase ≅ tw D₂.base.toBase ⋙ tw (CompactificationOf.Hom.map φ.base) :=
  congrN (CompactificationOf.homMap_comp_toBase φ.base).symm ≪≫
    compN (CompactificationOf.Hom.map φ.base) D₂.base.toBase

/-- The comparison for the compactifications of `f`. -/
abbrev eQ : tw D₁.innerSnd ≅ tw D₂.innerSnd ⋙ tw φ.innerMap :=
  congrN φ.innerMap_snd.symm ≪≫ compN φ.innerMap D₂.innerSnd

include hb in
/-- **`γ_B ∘ γ_F`** is the base change map of the stack of `F` over `B`: the hypothesis `h₂` of
`Stacks.Duality.compositionChase`, from [Stacks, Tag 0ATQ]. -/
theorem h₂ (N : quasiCoherentDerivedCategory D₂.base.space) :
    (bcO ((φ.sqF hb).paste_vert D₂.isPullback_innerFst)).app N =
      (pb D₁.innerFst).map ((compN φ.top D₂.top.toBase).hom.app N) ≫
        (bcO (φ.sqF hb)).app ((tw D₂.top.toBase).obj N) ≫
          (tw φ.innerMap).map (D₂.baseChange.app N) ≫
            (compN φ.innerMap D₂.innerSnd).inv.app ((pb D₂.baseImm).obj N) :=
  stackChase D₂.baseChange (bcO (φ.sqF hb)) (compN φ.top D₂.top.toBase)
    (compN φ.innerMap D₂.innerSnd) _ (bcN_vcomp (φ.sqF hb) D₂.isPullback_innerFst) N

include hb in
/-- **`γ_D ∘ γ_C`** is the base change map of the stack of `C` over `D`: the hypothesis `h₃` of
`Stacks.Duality.compositionChase`, from [Stacks, Tag 0ATQ]. -/
theorem h₃ (N : quasiCoherentDerivedCategory D₂.base.space) :
    (bcO (D₁.isPullback_innerFst.paste_vert (φ.sqD hb))).app N =
      (pb D₁.innerFst).map ((compN D₁.top.toBase (CompactificationOf.Hom.map φ.base)).hom.app N) ≫
        D₁.baseChange.app ((tw (CompactificationOf.Hom.map φ.base)).obj N) ≫
          (tw D₁.innerSnd).map ((bcO (φ.sqD hb)).app N) ≫
            (compN D₁.innerSnd (𝟙 Y.left)).inv.app ((pb D₂.baseImm).obj N) :=
  stackChase (bcO (φ.sqD hb)) D₁.baseChange
    (compN D₁.top.toBase (CompactificationOf.Hom.map φ.base))
    (compN D₁.innerSnd (𝟙 Y.left)) _ (bcN_vcomp D₁.isPullback_innerFst (φ.sqD hb)) N

include hb in
/-- The two stacks are one square: the hypothesis `h₄` of `Stacks.Duality.compositionChase`. -/
theorem h₄ (N : quasiCoherentDerivedCategory D₂.base.space) :
    (bcO (D₁.isPullback_innerFst.paste_vert (φ.sqD hb))).app N =
      (pb D₁.innerFst).map ((congrN φ.hp').hom.app N) ≫
        (bcO ((φ.sqF hb).paste_vert D₂.isPullback_innerFst)).app N ≫
          (congrN φ.hq').inv.app ((pb D₂.baseImm).obj N) :=
  bcO_congr_vert_app φ.hq' φ.hp' _ _ N

/-- The hypothesis `h₅` of `Stacks.Duality.compositionChase`, from
`Stacks.Duality.compN_square`. -/
theorem h₅ (K : quasiCoherentDerivedCategory Z.left) :
    (congrN φ.hk ≪≫ compN φ.top (D₂.top.toBase ≫ D₂.base.toBase)).hom.app K ≫
        (tw φ.top).map ((compN D₂.top.toBase D₂.base.toBase).hom.app K) =
      (compN D₁.top.toBase D₁.base.toBase).hom.app K ≫
        (tw D₁.top.toBase).map ((congrN (CompactificationOf.homMap_comp_toBase φ.base).symm ≪≫
          compN (CompactificationOf.Hom.map φ.base) D₂.base.toBase).hom.app K) ≫
        (compN D₁.top.toBase (CompactificationOf.Hom.map φ.base)).inv.app
          ((tw D₂.base.toBase).obj K) ≫
          (congrN φ.hp').hom.app ((tw D₂.base.toBase).obj K) ≫
            (compN φ.top D₂.top.toBase).hom.app ((tw D₂.base.toBase).obj K) :=
  compN_square D₁.top.toBase D₂.top.toBase φ.top (CompactificationOf.Hom.map φ.base)
    D₁.base.toBase D₂.base.toBase (CompactificationOf.homMap_comp_toBase φ.base) φ.hp' φ.hk K

/-- The hypothesis `h₆` of `Stacks.Duality.compositionChase`, from `Stacks.Duality.compN_unit`. -/
theorem h₆ (M : quasiCoherentDerivedCategory Y.left) :
    (congrN φ.innerMap_snd.symm ≪≫ compN φ.innerMap D₂.innerSnd).hom.app M =
      (tw D₁.innerSnd).map ((idN Y.left).inv.app M) ≫
      (compN D₁.innerSnd (𝟙 Y.left)).inv.app M ≫ (congrN φ.hq').hom.app M ≫
        (compN φ.innerMap D₂.innerSnd).hom.app M :=
  compN_unit D₁.innerSnd D₂.innerSnd φ.innerMap φ.innerMap_snd φ.hq' M

include hb ho in
/-- **The chase of the second half of the proof of [Stacks, Tag 0ATX] for a morphism of choices**,
read at an object of `D_QCoh(𝒪_Z)`: the comparison `α_E` of the compactifications of `f ≫ g`,
followed by the comparison of [Stacks, Tag 0ATX] for the target choice, is the comparison for the
source choice followed by the comparisons `α_A` of the compactifications of `f` and `α_D` of
those of `g`. -/
theorem chase (K : quasiCoherentDerivedCategory Z.left) :
    ((pb D₁.topImm).map ((congrN φ.hk ≪≫ compN φ.top (D₂.top.toBase ≫ D₂.base.toBase)).hom.app K) ≫
        (bcO (φ.sqE ho)).app ((tw (D₂.top.toBase ≫ D₂.base.toBase)).obj K) ≫
          (idN X.left).hom.app ((pb D₂.topImm).obj ((tw (D₂.top.toBase ≫ D₂.base.toBase)).obj K))) ≫
      D₂.compMap.app K =
    D₁.compMap.app K ≫
      ((pb D₁.innerImmersion).map
        ((congrN φ.innerMap_snd.symm ≪≫ compN φ.innerMap D₂.innerSnd).hom.app
          ((pb D₁.baseImm).obj ((tw D₁.base.toBase).obj K))) ≫
        (bcO (φ.sqA ho)).app
          ((tw D₂.innerSnd).obj ((pb D₁.baseImm).obj ((tw D₁.base.toBase).obj K))) ≫
          (idN X.left).hom.app ((pb D₂.innerImmersion).obj ((tw D₂.innerSnd).obj
            ((pb D₁.baseImm).obj ((tw D₁.base.toBase).obj K))))) ≫
        (pb D₂.innerImmersion).map ((tw D₂.innerSnd).map
          ((pb D₁.baseImm).map ((congrN (CompactificationOf.homMap_comp_toBase φ.base).symm ≪≫
              compN (CompactificationOf.Hom.map φ.base) D₂.base.toBase).hom.app K) ≫
            (bcO (φ.sqD hb)).app ((tw D₂.base.toBase).obj K) ≫
              (idN Y.left).hom.app ((pb D₂.baseImm).obj ((tw D₂.base.toBase).obj K)))) := by
  rw [D₁.compMap_app, D₂.compMap_app]
  exact compositionChase (compN D₁.top.toBase D₁.base.toBase) (compN D₂.top.toBase D₂.base.toBase)
    D₁.restrictCompIso D₂.restrictCompIso D₁.baseChange D₂.baseChange
    (congrN φ.hk ≪≫ compN φ.top (D₂.top.toBase ≫ D₂.base.toBase)) (bcO (φ.sqE ho)) (idN X.left)
    (congrN (CompactificationOf.homMap_comp_toBase φ.base).symm ≪≫
      compN (CompactificationOf.Hom.map φ.base) D₂.base.toBase) (bcO (φ.sqD hb)) (idN Y.left)
    (congrN φ.innerMap_snd.symm ≪≫ compN φ.innerMap D₂.innerSnd) (bcO (φ.sqA ho)) (bcO (φ.sqF hb))
    (compN φ.top D₂.top.toBase) (compN φ.innerMap D₂.innerSnd)
    (compN D₁.top.toBase (CompactificationOf.Hom.map φ.base)) (compN D₁.innerSnd (𝟙 Y.left))
    (congrN φ.hp') (congrN φ.hq') (bcO ((φ.sqF hb).paste_vert D₂.isPullback_innerFst))
    (bcO (D₁.isPullback_innerFst.paste_vert (φ.sqD hb))) (φ.h₁ hb ho) (φ.h₂ hb) (φ.h₃ hb)
    (φ.h₄ hb) φ.h₅ φ.h₆ K

end Hom

end CompositionData

section RefinementShape

variable {Xf Yf : FTS S} (h : Xf ⟶ Yf) {j k : CompactificationOf (Over.mk h.left)} (c : j ⟶ k)
  (hc : CompactificationOf.PreservesInterior c)

/-- The comparison `α_c` of [Stacks, Tag 0AA0] has the shape `Stacks.Duality.alphaShape`. -/
theorem refinementIso_eq_alphaShape [hβ : IsIso (refinementBaseChangePlus h c hc)] :
    refinementIso h c hc =
      alphaShape (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Yf.left))
        (refinementTwistedCompIso h c) (refinementBaseChange h c hc)
        (twistedInverseImageIdIso Xf.left
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 Xf.left))) (hβ := hβ) :=
  rfl

end RefinementShape

namespace CompositionData

namespace Hom

variable {D₁ D₂ : CompositionData f g} (φ : Hom D₁ D₂)
  (hb : CompactificationOf.PreservesInterior φ.base)
  (ho : CompactificationOf.PreservesInterior φ.outerHom)

/-- The comparison of twisted inverse images of `α_E`, in the spelling of this file. -/
theorem refinementTwistedCompIso_outer :
    refinementTwistedCompIso (f ≫ g) φ.outerHom =
      congrN φ.hk ≪≫ compN φ.top (D₂.top.toBase ≫ D₂.base.toBase) := rfl

/-- The base change map of `α_E`, in the spelling of this file. -/
theorem refinementBaseChange_outer :
    refinementBaseChange (f ≫ g) φ.outerHom ho = bcO (φ.sqE ho) := rfl

include hb ho in
/-- **The comparison of [Stacks, Tag 0ATX] for one choice is natural in morphisms of choices**,
as an identity of transformations of functors out of `D_QCoh(𝒪_Z)`: the comparison `α_E` of
[Stacks, Tag 0AA0] for the compactifications of `f ≫ g` followed by the comparison for the target
choice is the comparison for the source choice followed by the comparisons `α_A` and `α_D` of the
compactifications of `f` and of `g`. -/
theorem naturality :
    alphaNat (congrN φ.hk ≪≫ compN φ.top (D₂.top.toBase ≫ D₂.base.toBase)) (bcO (φ.sqE ho))
        (idN X.left) ≫ D₂.compMap =
      D₁.compMap ≫ Functor.whiskerLeft (tw D₁.base.toBase ⋙ pb D₁.baseImm)
        (alphaNat (congrN φ.innerMap_snd.symm ≪≫ compN φ.innerMap D₂.innerSnd) (bcO (φ.sqA ho))
          (idN X.left)) ≫
        Functor.whiskerRight
          (alphaNat (congrN (CompactificationOf.homMap_comp_toBase φ.base).symm ≪≫
            compN (CompactificationOf.Hom.map φ.base) D₂.base.toBase) (bcO (φ.sqD hb))
          (idN Y.left)) (tw D₂.innerSnd ⋙ pb D₂.innerImmersion) :=
  naturalityShape _ _ _ _ _ _ _ _ D₁.compMap D₂.compMap (φ.chase hb ho)

include hb in
/-- `α_D` in transformation form, in the spelling of this file. -/
theorem refinementIso_base_hom [IsIso (refinementBaseChangePlus g φ.base hb)] :
    (refinementIso g φ.base hb).hom =
      Functor.whiskerLeft (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Z.left))
        (alphaNat (congrN (CompactificationOf.homMap_comp_toBase φ.base).symm ≪≫
            compN (CompactificationOf.Hom.map φ.base) D₂.base.toBase) (bcO (φ.sqD hb))
          (idN Y.left)) := by
  rw [refinementIso_eq_alphaShape, alphaShape_hom]
  rfl

include ho in
/-- `α_A` in transformation form, in the spelling of this file. -/
theorem refinementIso_inner_hom
    [IsIso (refinementBaseChangePlus f φ.innerHom (φ.preservesInterior_innerHom ho))] :
    (refinementIso f φ.innerHom (φ.preservesInterior_innerHom ho)).hom =
      Functor.whiskerLeft (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Y.left))
        (alphaNat (congrN φ.innerMap_snd.symm ≪≫ compN φ.innerMap D₂.innerSnd) (bcO (φ.sqA ho))
          (idN X.left)) := by
  rw [refinementIso_eq_alphaShape, alphaShape_hom]
  rfl

include ho in
/-- `α_E` in transformation form, in the spelling of this file. -/
theorem refinementIso_outer_hom [IsIso (refinementBaseChangePlus (f ≫ g) φ.outerHom ho)] :
    (refinementIso (f ≫ g) φ.outerHom ho).hom =
      Functor.whiskerLeft (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Z.left))
        (alphaNat (congrN φ.hk ≪≫ compN φ.top (D₂.top.toBase ≫ D₂.base.toBase)) (bcO (φ.sqE ho))
          (idN X.left)) := by
  rw [refinementIso_eq_alphaShape, alphaShape_hom]
  rfl

end Hom

end CompositionData

/-- **`g^!` maps `D⁺_QCoh(𝒪_Z)` into `D⁺_QCoh(𝒪_Y)`**: the twisted inverse image of the proper
structure morphism of a compactification preserves bounded-below cohomology by
[Stacks, Tag 0A9I], and so does derived pullback along its open immersion, which is exact. -/
theorem isBoundedBelow_compactificationUpperShriek_obj (j : CompactificationOf (Over.mk g.left))
    (K : quasiCoherentDerivedCategoryPlusAtModel Z.left) :
    DerivedCategoryB.IsBoundedBelow ((compactificationUpperShriek g j).obj K).obj :=
  isBoundedBelow_pb_obj j.immersion _
    (isBoundedBelow_twistedInverseImage_obj j.toBase K.obj K.property)

/-! ### The isomorphism `(g ∘ f)^! ≅ f^! ∘ g^!` with `g^!` read in `D⁺_QCoh(𝒪_Y)` -/

section Lifted

namespace CompositionData

variable (D : CompositionData f g)

/-- `g^! : D⁺_QCoh(𝒪_Z) ⥤ D⁺_QCoh(𝒪_Y)` for the compactification of `g` of a choice. -/
abbrev plus :
    quasiCoherentDerivedCategoryPlusAtModel Z.left ⥤
      quasiCoherentDerivedCategoryPlusAtModel Y.left :=
  (isBoundedBelowQuasiCoherentAtModel Y.left).lift
    (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Z.left) ⋙
      (tw D.base.toBase ⋙ pb D.baseImm))
    (isBoundedBelow_compactificationUpperShriek_obj D.base)

/-- **The isomorphism `(g ∘ f)^! ≅ f^! ∘ g^!` of [Stacks, Tag 0ATX] for one choice.** -/
def compIso : compactificationUpperShriek (f ≫ g) D.outer ≅
    D.plus ⋙ (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Y.left) ⋙
      (tw D.innerSnd ⋙ pb D.innerImmersion)) :=
  D.compIsoPlus

/-- The underlying transformation of `Stacks.Duality.CompositionData.compIso`. -/
theorem compIso_hom : (D.compIso).hom =
    (Functor.whiskerLeft (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Z.left)) D.compMap :
      compactificationUpperShriek (f ≫ g) D.outer ⟶
        D.plus ⋙ (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Y.left) ⋙
          (tw D.innerSnd ⋙ pb D.innerImmersion))) := rfl

namespace Hom

variable {D₁ D₂ : CompositionData f g} (φ : Hom D₁ D₂)
  (hb : CompactificationOf.PreservesInterior φ.base)
  (ho : CompactificationOf.PreservesInterior φ.outerHom)

/-- The comparison `α_D` of [Stacks, Tag 0AA0] for the compactifications of `g`, read in
`D⁺_QCoh(𝒪_Y)`. -/
abbrev alphaDPlus [IsIso (refinementBaseChangePlus g φ.base hb)] : D₁.plus ≅ D₂.plus :=
  liftIsoOf (isBoundedBelowQuasiCoherentAtModel Y.left)
    (F₁ := ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Z.left) ⋙
      (tw D₁.base.toBase ⋙ pb D₁.baseImm))
    (F₂ := ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Z.left) ⋙
      (tw D₂.base.toBase ⋙ pb D₂.baseImm))
    (isBoundedBelow_compactificationUpperShriek_obj D₁.base)
    (isBoundedBelow_compactificationUpperShriek_obj D₂.base)
    (refinementIso g φ.base hb)

/-- The comparison `α_A` of [Stacks, Tag 0AA0] for the compactifications of `f`, in the spelling of
this file. -/
abbrev alphaA
    [hA : IsIso (refinementBaseChangePlus f φ.innerHom (φ.preservesInterior_innerHom ho))] :
    ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Y.left) ⋙
      (tw D₁.innerSnd ⋙ pb D₁.innerImmersion) ≅
    ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Y.left) ⋙
      (tw D₂.innerSnd ⋙ pb D₂.innerImmersion) :=
  alphaShape (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Y.left))
    (congrN φ.innerMap_snd.symm ≪≫ compN φ.innerMap D₂.innerSnd) (bcO (φ.sqA ho)) (idN X.left)
    (hβ := hA)


/-- `Stacks.Duality.CompositionData.Hom.alphaA` is the comparison `α_A` of [Stacks, Tag 0AA0]. -/
theorem alphaA_eq
    [IsIso (refinementBaseChangePlus f φ.innerHom (φ.preservesInterior_innerHom ho))] :
    (φ.alphaA ho :
        compactificationUpperShriek f D₁.inner ≅ compactificationUpperShriek f D₂.inner) =
      refinementIso f φ.innerHom (φ.preservesInterior_innerHom ho) := by
  rw [refinementIso_eq_alphaShape]
  rfl

include hb ho in
/-- **The isomorphism of [Stacks, Tag 0ATX] for one choice is natural in morphisms of choices**:
the comparison `α_E` of [Stacks, Tag 0AA0] for the compactifications of `f ≫ g`, followed by the
isomorphism for the target choice, is the isomorphism for the source choice followed by the
horizontal composite of the comparisons `α_D` for `g` and `α_A` for `f`. -/
theorem compIso_naturality
    [IsIso (refinementBaseChangePlus (f ≫ g) φ.outerHom ho)]
    [IsIso (refinementBaseChangePlus g φ.base hb)]
    [IsIso (refinementBaseChangePlus f φ.innerHom (φ.preservesInterior_innerHom ho))] :
    refinementIso (f ≫ g) φ.outerHom ho ≪≫ D₂.compIso =
      D₁.compIso ≪≫ NatIso.hcomp (φ.alphaDPlus hb) (φ.alphaA ho) :=
  isoNaturalityShape (isBoundedBelowQuasiCoherentAtModel Y.left)
    (ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Z.left))
    (isBoundedBelow_compactificationUpperShriek_obj D₁.base)
    (isBoundedBelow_compactificationUpperShriek_obj D₂.base)
    (refinementIso (f ≫ g) φ.outerHom ho) (D₁.compIso) (D₂.compIso)
    (refinementIso g φ.base hb) (φ.alphaA ho) _ D₁.compMap D₂.compMap _ _
    (φ.refinementIso_outer_hom ho) (D₁.compIso_hom) (D₂.compIso_hom)
    (φ.refinementIso_base_hom hb) (alphaShape_hom _ _ _ _ (hβ := _)) (φ.naturality hb ho)

end Hom

/-! ### Independence of the choice -/

section Independence

/-- The comparisons of [Stacks, Tag 0AA0] for the compactifications of `g`, read in
`D⁺_QCoh(𝒪_Y)`, between the compactifications of two choices. -/
def basePlusIso (D₁ D₂ : CompositionData f g) : D₁.plus ≅ D₂.plus :=
  liftIsoOf (isBoundedBelowQuasiCoherentAtModel Y.left)
    (F₁ := ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Z.left) ⋙
      (tw D₁.base.toBase ⋙ pb D₁.baseImm))
    (F₂ := ObjectProperty.ι (isBoundedBelowQuasiCoherentAtModel Z.left) ⋙
      (tw D₂.base.toBase ⋙ pb D₂.baseImm))
    (isBoundedBelow_compactificationUpperShriek_obj D₁.base)
    (isBoundedBelow_compactificationUpperShriek_obj D₂.base)
    (compactificationUpperShriekIso g D₁.base D₂.base)

/-- **The isomorphism of [Stacks, Tag 0ATX] does not depend on the choice**: for two choices of
compactifications, the isomorphism built from the second is the one built from the first read
through the canonical comparisons of [Stacks, Tag 0AA0] of the compactifications of `g ∘ f`, of
`g` and of `f`. This is the second half of the source's proof. -/
theorem compIso_independent (D₁ D₂ : CompositionData f g) :
    D₂.compIso =
      (compactificationUpperShriekIso (f ≫ g) D₁.outer D₂.outer).symm ≪≫ D₁.compIso ≪≫
        NatIso.hcomp (basePlusIso D₁ D₂)
          (compactificationUpperShriekIso f D₁.inner D₂.inner) := by
  have hp₁ := Hom.preservesInterior_of_dom D₁ D₂ (domFst D₁ D₂)
  have hp₂ := Hom.preservesInterior_of_dom D₁ D₂ (domSnd D₁ D₂)
  have n₁ := (domFst D₁ D₂).compIso_naturality hp₁.1 hp₁.2
  have n₂ := (domSnd D₁ D₂).compIso_naturality hp₂.1 hp₂.2
  rw [independenceShape _ _ _ _ _ _ _ _ _ n₁ n₂]
  have coh := fun {Xf Yf : FTS S} (h : Xf ⟶ Yf) =>
    coherent_eq_symm_trans (compactificationUpperShriekIso h)
      (compactificationUpperShriekIso_refl h) (compactificationUpperShriekIso_trans h)
  have ha : (refinementIso (f ≫ g) (domFst D₁ D₂).outerHom hp₁.2).symm ≪≫
      refinementIso (f ≫ g) (domSnd D₁ D₂).outerHom hp₂.2 =
        compactificationUpperShriekIso (f ≫ g) D₁.outer D₂.outer := by
    rw [coh (f ≫ g) (dom D₁ D₂).outer D₁.outer D₂.outer,
      compactificationUpperShriekIso_eq_iso (f ≫ g) (domFst D₁ D₂).outerHom hp₁.2,
      compactificationUpperShriekIso_eq_iso (f ≫ g) (domSnd D₁ D₂).outerHom hp₂.2]
  have hb' : ((domFst D₁ D₂).alphaDPlus hp₁.1).symm ≪≫ (domSnd D₁ D₂).alphaDPlus hp₂.1 =
      basePlusIso D₁ D₂ := by
    refine liftIsoOf_symm_trans _ _ _ _ _ _ _ ?_
    rw [coh g (dom D₁ D₂).base D₁.base D₂.base,
      compactificationUpperShriekIso_eq_iso g (domFst D₁ D₂).base hp₁.1,
      compactificationUpperShriekIso_eq_iso g (domSnd D₁ D₂).base hp₂.1]
    rfl
  have hc : (((domFst D₁ D₂).alphaA hp₁.2).symm ≪≫ (domSnd D₁ D₂).alphaA hp₂.2 :
      compactificationUpperShriek f D₁.inner ≅ compactificationUpperShriek f D₂.inner) =
        compactificationUpperShriekIso f D₁.inner D₂.inner := by
    rw [coh f (dom D₁ D₂).inner D₁.inner D₂.inner,
      compactificationUpperShriekIso_eq_iso f (domFst D₁ D₂).innerHom
        ((domFst D₁ D₂).preservesInterior_innerHom hp₁.2),
      compactificationUpperShriekIso_eq_iso f (domSnd D₁ D₂).innerHom
        ((domSnd D₁ D₂).preservesInterior_innerHom hp₂.2)]
    exact congrArg₂
      (fun (a : compactificationUpperShriek f (dom D₁ D₂).inner ≅
          compactificationUpperShriek f D₁.inner)
        (b : compactificationUpperShriek f (dom D₁ D₂).inner ≅
          compactificationUpperShriek f D₂.inner) =>
          a.symm ≪≫ b) ((domFst D₁ D₂).alphaA_eq hp₁.2) ((domSnd D₁ D₂).alphaA_eq hp₂.2)
  rw [ha, hb']
  exact congrArg (fun c => (compactificationUpperShriekIso (f ≫ g) D₁.outer D₂.outer).symm ≪≫
    D₁.compIso ≪≫ NatIso.hcomp (basePlusIso D₁ D₂) c) hc

end Independence

end CompositionData

/-! ### The canonical isomorphism -/

section Canonical

/-- `g^! : D⁺_QCoh(𝒪_Z) ⥤ D⁺_QCoh(𝒪_Y)` of a compactification `i` of `g`. -/
abbrev upperShriekPlusAtModel (i : CompactificationOf (Over.mk g.left)) :
    quasiCoherentDerivedCategoryPlusAtModel Z.left ⥤
      quasiCoherentDerivedCategoryPlusAtModel Y.left :=
  (isBoundedBelowQuasiCoherentAtModel Y.left).lift (compactificationUpperShriek g i)
    (isBoundedBelow_compactificationUpperShriek_obj i)

/-- The isomorphism of [Stacks, Tag 0ATX] for one choice, between the upper shriek functors of the
three compactifications the choice determines. -/
def CompositionData.compIsoAPI (D : CompositionData f g) :
    compactificationUpperShriek (f ≫ g) D.outer ≅
      upperShriekPlusAtModel D.base ⋙ compactificationUpperShriek f D.inner :=
  D.compIso

/-- The comparison of `g^!` read in `D⁺_QCoh(𝒪_Y)`. -/
abbrev basePlusIsoAPI (i i' : CompactificationOf (Over.mk g.left)) :
    upperShriekPlusAtModel i ≅ upperShriekPlusAtModel i' :=
  liftIsoOf _ (isBoundedBelow_compactificationUpperShriek_obj i)
    (isBoundedBelow_compactificationUpperShriek_obj i') (compactificationUpperShriekIso g i i')

/-- `Stacks.Duality.CompositionData.compIso_independent` for
`Stacks.Duality.CompositionData.compIsoAPI`. -/
theorem CompositionData.compIsoAPI_independent (D₁ D₂ : CompositionData f g) :
    D₂.compIsoAPI =
      (compactificationUpperShriekIso (f ≫ g) D₁.outer D₂.outer).symm ≪≫
        D₁.compIsoAPI ≪≫ NatIso.hcomp (basePlusIsoAPI D₁.base D₂.base)
          (compactificationUpperShriekIso f D₁.inner D₂.inner) :=
  CompositionData.compIso_independent D₁ D₂

/-- **[Stacks, Tag 0ATX]: the canonical isomorphism `(g ∘ f)^! ≅ f^! ∘ g^!`**, for any
compactifications `k` of `g ∘ f`, `j` of `f` and `i` of `g`. It is the source's construction for a
choice of compactifications whose compactification of `Y` is `i` (that one exists is
[Stacks, Tag 0A9Z]), read through the canonical comparisons of [Stacks, Tag 0AA0]. -/
@[stacks 0ATX "the canonical isomorphism (g o f)^! = f^! o g^! of upper shriek functors for \
  composable morphisms f : X -> Y, g : Y -> Z of FTS S over a Noetherian S, at arbitrary \
  compactifications k of g o f, j of f and i of g, as functors out of D^+_QCoh(O_Z), with g^! \
  read in D^+_QCoh(O_Y) (Stacks 0A9I) and each f^! the functor \
  Stacks.Duality.compactificationUpperShriek of Stacks 0A9Y/0AA0. It is the source's \
  construction for a choice of compactifications through i: (j' o j)^* a b = j^* (j')^* a b -> \
  j^* a' i^* b via the base change map of Stacks 0AA6, invertible by Stacks 0A9P (2), read \
  through the canonical comparisons of Stacks 0AA0. Canonicity is proved, not assumed: \
  Stacks.Duality.upperShriekCompIsoAtModel_choice says it is the source's isomorphism for every \
  choice (the second half of the source's proof: the chase of squares A..F through Stacks 0ATQ \
  and 0ATR, and a dominating choice from Stacks 0ATU), and \
  Stacks.Duality.upperShriekCompIsoAtModel_naturality says it is compatible with the comparisons \
  of Stacks 0AA0 in all three compactifications. The compactifications are arguments, as in Stacks \
  0AA0; that they exist is Stacks 0F41"]
def upperShriekCompIsoAtModel (k : CompactificationOf (Over.mk (f ≫ g).left))
    (j : CompactificationOf (Over.mk f.left)) (i : CompactificationOf (Over.mk g.left)) :
    compactificationUpperShriek (f ≫ g) k ≅
      upperShriekPlusAtModel i ⋙ compactificationUpperShriek f j :=
  compactificationUpperShriekIso (f ≫ g) k (CompositionData.ofCompactifications k i).outer ≪≫
    (CompositionData.ofCompactifications k i).compIsoAPI ≪≫
      Functor.isoWhiskerLeft (upperShriekPlusAtModel i)
        (compactificationUpperShriekIso f (CompositionData.ofCompactifications k i).inner j)

/-- The comparisons of [Stacks, Tag 0AA0] are inverse to each other. -/
theorem coherent_symm {Xf Yf : FTS S} (h : Xf ⟶ Yf)
    (j k : CompactificationOf (Over.mk h.left)) :
    (compactificationUpperShriekIso h j k).symm = compactificationUpperShriekIso h k j := by
  rw [coherent_eq_symm_trans (compactificationUpperShriekIso h)
      (compactificationUpperShriekIso_refl h) (compactificationUpperShriekIso_trans h) j k j,
    compactificationUpperShriekIso_refl]
  simp

/-- **The canonical isomorphism is the source's construction for every choice**: for a choice of
compactifications `D`, the canonical isomorphism at the three compactifications `D` determines is
the isomorphism the proof of [Stacks, Tag 0ATX] builds from `D`. -/
theorem upperShriekCompIsoAtModel_choice (D : CompositionData f g) :
    upperShriekCompIsoAtModel D.outer D.inner D.base = D.compIsoAPI := by
  have hb : basePlusIsoAPI (CompositionData.ofCompactifications D.outer D.base).base
      D.base = Iso.refl _ := by
    change liftIsoOf _ _ _ (compactificationUpperShriekIso g D.base D.base) = _
    rw [compactificationUpperShriekIso_refl]
    exact liftIsoOf_refl _ _
  rw [(CompositionData.ofCompactifications D.outer D.base).compIsoAPI_independent D,
    coherent_symm, hb]
  exact congrArg (fun c => _ ≪≫ _ ≪≫ c) (hcomp_refl_left _).symm

/-- **The canonical isomorphism is compatible with the comparisons of [Stacks, Tag 0AA0]** in all
three compactifications: changing the compactification of `g ∘ f` before, or those of `f` and of
`g` after, gives the same isomorphism. -/
theorem upperShriekCompIsoAtModel_naturality (k k' : CompactificationOf (Over.mk (f ≫ g).left))
    (j j' : CompactificationOf (Over.mk f.left)) (i i' : CompactificationOf (Over.mk g.left)) :
    compactificationUpperShriekIso (f ≫ g) k k' ≪≫ upperShriekCompIsoAtModel k' j' i' =
      upperShriekCompIsoAtModel k j i ≪≫
        NatIso.hcomp (basePlusIsoAPI i i') (compactificationUpperShriekIso f j j') :=
  canonicalShape _ _ _ _ _ _ _ _ _ _ _
    ((CompositionData.ofCompactifications k i).compIsoAPI_independent
      (CompositionData.ofCompactifications k' i'))
    ((compactificationUpperShriekIso_trans (f ≫ g) _ _ _).trans
      (compactificationUpperShriekIso_trans (f ≫ g) _ _ _).symm)
    ((compactificationUpperShriekIso_trans f _ _ _).trans
      (compactificationUpperShriekIso_trans f _ _ _).symm)

/-- **[Stacks, Tag 0ATX]: there is a canonical isomorphism `(g ∘ f)^! → f^! ∘ g^!`.** For
composable morphisms `f : X ⟶ Y`, `g : Y ⟶ Z` of `AlgebraicGeometry.FTS S` over a Noetherian `S`
there is a family of isomorphisms `(g ∘ f)^!_k ≅ f^!_j ∘ g^!_i`, indexed by compactifications `k`
of `g ∘ f`, `j` of `f` and `i` of `g`, which is the source's construction for **every** choice of
compactifications, and which is compatible with the canonical comparisons of [Stacks, Tag 0AA0] in
all three compactifications — so it is independent of the choices made. The family is
`Stacks.Duality.upperShriekCompIsoAtModel`. -/
@[stacks 0ATX "existence and canonicity of the isomorphism (g o f)^! = f^! o g^! for composable \
  morphisms of FTS S over a Noetherian S, the upper shriek functors being those of Stacks 0AA0 \
  on D^+_QCoh and g^! read in D^+_QCoh(O_Y): a family of isomorphisms indexed by \
  compactifications of g o f, f and g that equals the source's construction for every choice of \
  compactifications (Stacks.Duality.CompositionData.compIsoAPI) and is compatible with the \
  comparisons of Stacks 0AA0 in all three compactifications. Nothing is assumed beyond the \
  compactifications themselves, which are arguments as in Stacks 0AA0 (their existence is Stacks \
  0F41)"]
theorem exists_canonical_upperShriekCompIso :
    ∃ e : ∀ (k : CompactificationOf (Over.mk (f ≫ g).left))
        (j : CompactificationOf (Over.mk f.left)) (i : CompactificationOf (Over.mk g.left)),
        compactificationUpperShriek (f ≫ g) k ≅ upperShriekPlusAtModel i ⋙
            compactificationUpperShriek f j,
      (∀ D : CompositionData f g, e D.outer D.inner D.base = D.compIsoAPI) ∧
      ∀ k k' j j' i i', compactificationUpperShriekIso (f ≫ g) k k' ≪≫ e k' j' i' =
        e k j i ≪≫ NatIso.hcomp (basePlusIsoAPI i i') (compactificationUpperShriekIso f j j') :=
  ⟨upperShriekCompIsoAtModel, upperShriekCompIsoAtModel_choice,
      upperShriekCompIsoAtModel_naturality⟩

end Canonical

end Lifted

end Stacks.Duality

end
