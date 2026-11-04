module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeCategory
public import StacksCore.Tactic.StacksAttribute

/-!
# Transitivity of normalization of dualizing complexes

Let `S` be a Noetherian scheme carrying a complex `ω_S^•`, let `Y` be of finite type over `S`
and let `X` be of finite type over `Y`. A dualizing complex on `X` normalized relative to
`ω_S^•` is then normalized relative to a dualizing complex on `Y` normalized relative to
`ω_S^•`. This file states and proves that transitivity.

The statement is about the upper shriek functors `f^!` of [Stacks, Tag 0A9Y], which this
repository does not yet carry: they are built from the right adjoint of `Rf_*`
([Stacks, Tag 0A9E]) and Nagata compactification, and their composition comparison
([Stacks, Tag 0ATX]) and coherence ([Stacks, Tag 0ATY]) are what the bookkeeping below runs
on. The formalism is therefore a *parameter* here, `Stacks.Duality.UpperShriek`, bundling
exactly those three things, and the normalization relation is **defined** from it rather than
assumed, so that the transitivity statement has content.

## Main definitions

* `Stacks.Duality.IsShriekable` — the morphisms for which `f^!` is defined: separated, of
  finite type, with Noetherian target.
* `Stacks.Duality.IsFiniteTypeOverNoetherian` — the standing hypothesis on the schemes of
  [Stacks, Tag 0AU5]: of finite type over a Noetherian base.
* `Stacks.Duality.UpperShriek` — an upper shriek formalism: a functor `f^!` for every
  shriekable `f`, a composition comparison, and its associativity coherence.
* `Stacks.Duality.UpperShriek.factorIso` — the comparison `k^! ≅ f^! ∘ g^!` attached to a
  factorization `k = g ∘ f`, the only way the comparison is used below.
* `Stacks.Duality.SeparatedCovering` — a finite covering of `X` by opens separated and of
  finite type over the base, the `𝒰` of [Stacks, Tag 0AU5].
* `Stacks.Duality.Normalized` — a complex normalized relative to `ω_S^•` and `𝒰`: the pair
  `(K, α_i)` of [Stacks, Tag 0AU5] together with its compatibility on overlaps.
* `Stacks.Duality.UpperShriek.transport` — the map `f_{ji}^! β_j^{-1}` of the proof of
  [Stacks, Tag 0AUB], conjugated by the canonical comparisons.
* `Stacks.Duality.Normalized.overMid` — the renormalization of [Stacks, Tag 0AUB].

## Main results

* `Stacks.Duality.UpperShriek.restrictCompare_transport` — the transports of
  `UpperShriek.transport` are a morphism of local systems. This is the whole content of the
  "this is formal and we omit the details" of [Stacks, Tag 0AUB]: two applications of the
  coherence [Stacks, Tag 0ATY] and one naturality.
* `Stacks.Duality.exists_normalized_of_normalized` — [Stacks, Tag 0AUB].

## References

* [Stacks Project, Tag 0AU5](https://stacks.math.columbia.edu/tag/0AU5)
* [Stacks Project, Tag 0AUB](https://stacks.math.columbia.edu/tag/0AUB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v v' w w'

namespace Stacks.Duality

/-- A morphism admits an upper shriek functor when it is separated, of finite type, and has
Noetherian target. These are the morphisms of the categories `FTS_S` of
[Stacks, Tag 0F42] for which [Stacks, Tag 0A9Y] constructs `f^!`. -/
structure IsShriekable {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  /-- The target is Noetherian, so that `f` admits a compactification. -/
  target_noetherian : AlgebraicGeometry.IsNoetherian Y
  /-- The morphism is separated and of finite type. -/
  separatedFiniteType : isSeparatedFiniteType f

/-- A scheme of finite type over a Noetherian base. This is the standing hypothesis on the
schemes `X` of [Stacks, Tag 0AU5]: unlike the objects of `FTS_S`, they are *not* assumed
separated over the base. -/
structure IsFiniteTypeOverNoetherian {X S : Scheme.{u}} (p : X ⟶ S) : Prop where
  /-- The base is Noetherian. -/
  base_noetherian : AlgebraicGeometry.IsNoetherian S
  /-- The structure morphism is locally of finite type. -/
  locallyOfFiniteType : LocallyOfFiniteType p
  /-- The structure morphism is quasi-compact. -/
  quasiCompact : QuasiCompact p

namespace IsShriekable

variable {X Y Z : Scheme.{u}}

/-- A shriekable morphism is separated. -/
theorem isSeparated {f : X ⟶ Y} (hf : IsShriekable f) : IsSeparated f :=
  hf.separatedFiniteType.1.1

/-- A shriekable morphism is locally of finite type. -/
theorem locallyOfFiniteType {f : X ⟶ Y} (hf : IsShriekable f) : LocallyOfFiniteType f :=
  hf.separatedFiniteType.1.2

/-- A shriekable morphism is quasi-compact. -/
theorem quasiCompact {f : X ⟶ Y} (hf : IsShriekable f) : QuasiCompact f :=
  hf.separatedFiniteType.2

/-- Shriekability transports along an equality of morphisms. -/
theorem of_eq {f g : X ⟶ Y} (e : f = g) (hf : IsShriekable f) : IsShriekable g := e ▸ hf

/-- The source of a shriekable morphism is Noetherian. -/
theorem source_noetherian {f : X ⟶ Y} (hf : IsShriekable f) :
    AlgebraicGeometry.IsNoetherian X :=
  let := hf.target_noetherian
  let := hf.locallyOfFiniteType
  let := hf.quasiCompact
  { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }

/-- Shriekable morphisms are closed under composition. -/
theorem comp {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsShriekable f) (hg : IsShriekable g) :
    IsShriekable (f ≫ g) :=
  let := hf.isSeparated
  let := hf.locallyOfFiniteType
  let := hf.quasiCompact
  let := hg.isSeparated
  let := hg.locallyOfFiniteType
  let := hg.quasiCompact
  { target_noetherian := hg.target_noetherian
    separatedFiniteType := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ }

end IsShriekable

namespace IsFiniteTypeOverNoetherian

variable {X S : Scheme.{u}} {p : X ⟶ S}

/-- A scheme of finite type over a Noetherian base is Noetherian. -/
@[ega "IV 1.5.3"]
theorem source_noetherian (hp : IsFiniteTypeOverNoetherian p) :
    AlgebraicGeometry.IsNoetherian X :=
  let := hp.base_noetherian
  let := hp.locallyOfFiniteType
  let := hp.quasiCompact
  { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian p
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace p }

/-- An open subscheme of a scheme of finite type over a Noetherian base is Noetherian. -/
theorem opens_noetherian (hp : IsFiniteTypeOverNoetherian p) (U : X.Opens) :
    AlgebraicGeometry.IsNoetherian U.toScheme :=
  let := hp.source_noetherian
  let : NoetherianSpace U.toScheme := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  { toIsLocallyNoetherian := inferInstance
    toCompactSpace := inferInstance }

/-- The inclusion of an open subscheme is shriekable. -/
theorem isShriekable_ι (hp : IsFiniteTypeOverNoetherian p) (U : X.Opens) :
    IsShriekable (U.ι : U.toScheme ⟶ X) :=
  let := hp.source_noetherian
  let : NoetherianSpace U.toScheme := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  { target_noetherian := hp.source_noetherian
    separatedFiniteType :=
      ⟨⟨inferInstance, inferInstance⟩, quasiCompact_of_noetherianSpace_source _⟩ }

/-- The inclusion of an open subscheme into a larger one is shriekable. -/
theorem isShriekable_homOfLE (hp : IsFiniteTypeOverNoetherian p) {W U : X.Opens} (h : W ≤ U) :
    IsShriekable (X.homOfLE h) :=
  let := hp.source_noetherian
  let : NoetherianSpace W.toScheme := W.ι.isOpenEmbedding.isInducing.noetherianSpace
  { target_noetherian := hp.opens_noetherian U
    separatedFiniteType :=
      ⟨⟨inferInstance, inferInstance⟩, quasiCompact_of_noetherianSpace_source _⟩ }

/-- An open subscheme of an open subscheme separated over the base is itself separated over
the base, so inherits shriekability of its structure morphism. -/
theorem isShriekable_le (hp : IsFiniteTypeOverNoetherian p) {W U : X.Opens} (h : W ≤ U)
    (hU : IsShriekable (U.ι ≫ p)) : IsShriekable (W.ι ≫ p) :=
  IsShriekable.of_eq (by rw [← Category.assoc, X.homOfLE_ι])
    ((hp.isShriekable_homOfLE h).comp hU)

end IsFiniteTypeOverNoetherian

/-- If `X` is of finite type over the Noetherian base `S` through `Y`, it is of finite type
over `Y`, which is itself Noetherian. -/
theorem IsFiniteTypeOverNoetherian.of_comp {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S}
    (hp : IsFiniteTypeOverNoetherian (f ≫ q)) (hq : IsFiniteTypeOverNoetherian q) :
    IsFiniteTypeOverNoetherian f :=
  let := hp.source_noetherian
  let := hp.locallyOfFiniteType
  let : NoetherianSpace X := inferInstance
  { base_noetherian := hq.source_noetherian
    locallyOfFiniteType := locallyOfFiniteType_of_comp f q
    quasiCompact := quasiCompact_of_noetherianSpace_source _ }

variable (𝒟 : Scheme.{u} → Type v) [∀ X : Scheme.{u}, Category.{v'} (𝒟 X)]

/-- An *upper shriek formalism* on a family of categories `𝒟` indexed by schemes: a functor
`f^! : 𝒟 Y ⥤ 𝒟 X` for every separated finite-type `f : X ⟶ Y` with Noetherian target, the
canonical comparison `k^! ≅ f^! ∘ g^!` for every factorization `k = g ∘ f`, and the
associativity coherence making these into a pseudofunctor.

The three fields are [Stacks, Tag 0A9Y] (the construction of `f^!` on `D_QCoh^+`, through
[Stacks, Tag 0A9E] and [Stacks, Tag 0AA0]), [Stacks, Tag 0ATX] and [Stacks, Tag 0ATY].

The comparison is taken in the *factored* form `k^! ≅ f^! ∘ g^!` for `e : f ≫ g = k` rather
than as `(g ∘ f)^! ≅ f^! ∘ g^!`. The two carry the same data, since `e` forces `k = f ≫ g`,
but the factored form lets the associativity coherence be stated without transporting along
`Category.assoc`: both bracketings of a triple composite are compared with one and the same
morphism `k`. -/
structure UpperShriek where
  /-- The upper shriek functor `f^!`, [Stacks, Tag 0A9Y]. -/
  shriek {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsShriekable f) : 𝒟 Y ⥤ 𝒟 X
  /-- The canonical comparison `k^! ≅ f^! ∘ g^!` attached to a factorization `k = g ∘ f`,
  [Stacks, Tag 0ATX]. -/
  factorIso {W X Y : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Y} {k : W ⟶ Y} (e : f ≫ g = k)
    (hf : IsShriekable f) (hg : IsShriekable g) (hk : IsShriekable k) :
    shriek k hk ≅ shriek g hg ⋙ shriek f hf
  /-- The comparisons are associative: for a triple composite `k = h ∘ g ∘ f`, splitting off
  `f` first and splitting off `h` first give the same isomorphism `k^! ≅ f^! ∘ g^! ∘ h^!`.
  This is the coherence of [Stacks, Tag 0ATY]. -/
  factorIso_assoc {W X Y Z : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z} {fg : W ⟶ Y}
    {gh : X ⟶ Z} {k : W ⟶ Z} (efg : f ≫ g = fg) (egh : g ≫ h = gh) (ek : fg ≫ h = k)
    (ek' : f ≫ gh = k) (hf : IsShriekable f) (hg : IsShriekable g) (hh : IsShriekable h)
    (hfg : IsShriekable fg) (hgh : IsShriekable gh) (hk : IsShriekable k) (K : 𝒟 Z) :
    (factorIso ek' hf hgh hk).hom.app K ≫
        (shriek f hf).map ((factorIso egh hg hh hgh).hom.app K) =
      (factorIso ek hfg hh hk).hom.app K ≫
        (factorIso efg hf hg hfg).hom.app ((shriek h hh).obj K)

namespace UpperShriek

variable {𝒟} (A : UpperShriek 𝒟)

/-- The upper shriek functor depends on the morphism alone. -/
theorem shriek_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) (hf : IsShriekable f)
    (hg : IsShriekable g) : A.shriek f hf = A.shriek g hg := by
  subst e; rfl

end UpperShriek

/-- A finite covering of `X` by opens which are separated and of finite type over the base
`p : X ⟶ S`. This is the `𝒰 : X = ⋃ U_i` of [Stacks, Tag 0AU5]; the source takes the `U_i`
affine, which is a way of guaranteeing the separatedness recorded here. -/
structure SeparatedCovering {X S : Scheme.{u}} (p : X ⟶ S) (ι : Type w) where
  /-- The members of the covering. -/
  U : ι → X.Opens
  /-- The covering is finite, as in the source. -/
  finite : Finite ι
  /-- The members cover `X`. -/
  covers : ⨆ i, U i = ⊤
  /-- Each member is separated and of finite type over the base. -/
  shriekable : ∀ i, IsShriekable ((U i).ι ≫ p)

namespace UpperShriek

variable {𝒟} (A : UpperShriek 𝒟) {X S : Scheme.{u}} {p : X ⟶ S}
  (hp : IsFiniteTypeOverNoetherian p)

/-- The restriction `K|_U` of a complex to an open subscheme, read as `(U → X)^! K`; by
[Stacks, Tag 0AU0] this agrees with derived restriction. -/
abbrev restrictTo (U : X.Opens) (K : 𝒟 X) : 𝒟 U.toScheme :=
  (A.shriek U.ι (hp.isShriekable_ι U)).obj K

/-- The local model `ω_U^• = (U → S)^! ω_S^•` of [Stacks, Tag 0AU5] attached to an open
subscheme separated over the base. -/
abbrev localModel {U : X.Opens} (hU : IsShriekable (U.ι ≫ p)) (ωS : 𝒟 S) : 𝒟 U.toScheme :=
  (A.shriek (U.ι ≫ p) hU).obj ωS

/-- The restriction to `W ≤ U` of a normalization isomorphism `α_U : K|_U ≅ ω_U^•`, read as
an isomorphism `K|_W ≅ ω_W^•` through the canonical comparisons on both sides. -/
def restrictLocalIso (ωS : 𝒟 S) (K : 𝒟 X) {W U : X.Opens} (h : W ≤ U)
    (hU : IsShriekable (U.ι ≫ p))
    (α : A.restrictTo hp U K ≅ A.localModel hU ωS) :
    A.restrictTo hp W K ≅ A.localModel (hp.isShriekable_le h hU) ωS :=
  (A.factorIso (X.homOfLE_ι h) (hp.isShriekable_homOfLE h) (hp.isShriekable_ι U)
      (hp.isShriekable_ι W)).app K ≪≫
    (A.shriek (X.homOfLE h) (hp.isShriekable_homOfLE h)).mapIso α ≪≫
    ((A.factorIso (show X.homOfLE h ≫ U.ι ≫ p = W.ι ≫ p by
        rw [← Category.assoc, X.homOfLE_ι]) (hp.isShriekable_homOfLE h) hU
        (hp.isShriekable_le h hU)).app ωS).symm

end UpperShriek

/-- A dualizing complex on `X` normalized relative to `ω_S^•` and the covering `𝒰`: the pair
`(K, α_i)` of [Stacks, Tag 0AU5], consisting of a complex on `X` and isomorphisms
`α_i : K|_{U_i} ≅ ω_{U_i}^•` whose transition isomorphisms on overlaps are the canonical
ones.

The source states the compatibility as `φ_{ij} = α_j|_{U_i ∩ U_j} ∘ α_i^{-1}|_{U_i ∩ U_j}`
for the canonical `φ_{ij} : ω_i^•|_{U_i ∩ U_j} → ω_j^•|_{U_i ∩ U_j}`. Since `φ_{ij}` is by
construction the composite of the two canonical comparisons `ω_i^•|_{U_i ∩ U_j} ≅
ω_{U_i ∩ U_j}^•` and `ω_{U_i ∩ U_j}^• ≅ ω_j^•|_{U_i ∩ U_j}`, that condition says exactly that
`α_i` and `α_j` restrict to the *same* isomorphism `K|_{U_i ∩ U_j} ≅ ω_{U_i ∩ U_j}^•`, which
is the form used here. -/
structure Normalized {𝒟 : Scheme.{u} → Type v} [∀ X : Scheme.{u}, Category.{v'} (𝒟 X)]
    (A : UpperShriek 𝒟) {X S : Scheme.{u}} {p : X ⟶ S}
    (hp : IsFiniteTypeOverNoetherian p) (ωS : 𝒟 S) {ι : Type w}
    (𝒰 : SeparatedCovering p ι) where
  /-- The complex `ω_X^•` itself. -/
  complex : 𝒟 X
  /-- The normalization isomorphism `α_i : K|_{U_i} ≅ ω_{U_i}^•` on each member. -/
  localIso (i : ι) : A.restrictTo hp (𝒰.U i) complex ≅ A.localModel (𝒰.shriekable i) ωS
  /-- On an overlap, `α_i` and `α_j` restrict to the same isomorphism. -/
  compat (i j : ι) :
    A.restrictLocalIso hp ωS complex (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U i)
        (𝒰.shriekable i) (localIso i) =
      A.restrictLocalIso hp ωS complex (inf_le_right : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U j)
        (𝒰.shriekable j) (localIso j)

/-! ### Transitivity

The bookkeeping of [Stacks, Tag 0AUB]. -/

/-- The restriction `f.resLE V U : U → V` of `f` to opens, followed by the structure morphism
of `V`, is the structure morphism of `U`. -/
theorem resLE_comp_structure {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S}
    (hpe : f ≫ q = p) {U : X.Opens} {V : Y.Opens} (hle : U ≤ f ⁻¹ᵁ V) :
    f.resLE V U hle ≫ V.ι ≫ q = U.ι ≫ p := by
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hpe]

namespace IsFiniteTypeOverNoetherian

variable {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S}

/-- `IsFiniteTypeOverNoetherian.of_comp` with the factorization given as an equation, the form
in which a morphism of schemes over `S` presents it. -/
theorem of_comp' (hp : IsFiniteTypeOverNoetherian p) (hq : IsFiniteTypeOverNoetherian q)
    (hpe : f ≫ q = p) : IsFiniteTypeOverNoetherian f :=
  IsFiniteTypeOverNoetherian.of_comp (by rw [hpe]; exact hp) hq

/-- The restriction of `f` to an open `U` of the source which is separated and of finite type
over the base, and an open `V` of the target containing its image, is shriekable. These are
the morphisms `f_{ji} : U_{ji} → V_j` of the proof of [Stacks, Tag 0AUB]. -/
theorem isShriekable_resLE (hp : IsFiniteTypeOverNoetherian p)
    (hq : IsFiniteTypeOverNoetherian q) (hpe : f ≫ q = p) {U : X.Opens} {V : Y.Opens}
    (hle : U ≤ f ⁻¹ᵁ V) (hU : IsShriekable (U.ι ≫ p)) : IsShriekable (f.resLE V U hle) := by
  have := hp.source_noetherian
  have : NoetherianSpace U.toScheme := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : IsSeparated (f.resLE V U hle ≫ V.ι ≫ q) := by
    rw [resLE_comp_structure hpe]; exact hU.isSeparated
  have : LocallyOfFiniteType (f.resLE V U hle ≫ V.ι ≫ q) := by
    rw [resLE_comp_structure hpe]; exact hU.locallyOfFiniteType
  exact
    { target_noetherian := hq.opens_noetherian V
      separatedFiniteType :=
        ⟨⟨IsSeparated.of_comp _ (V.ι ≫ q), locallyOfFiniteType_of_comp _ (V.ι ≫ q)⟩,
          quasiCompact_of_noetherianSpace_source _⟩ }

/-- An open of the source which is separated and of finite type over the base, and whose
image lies in an open of the target separated and of finite type over the base, is separated
and of finite type over the *target*. These are the morphisms `f'_{ji} : U_{ji} → Y` of the
proof of [Stacks, Tag 0AUB]. -/
theorem isShriekable_ι_comp (hp : IsFiniteTypeOverNoetherian p)
    (hq : IsFiniteTypeOverNoetherian q) (hpe : f ≫ q = p) {U : X.Opens} {V : Y.Opens}
    (hle : U ≤ f ⁻¹ᵁ V) (hU : IsShriekable (U.ι ≫ p)) : IsShriekable (U.ι ≫ f) :=
  IsShriekable.of_eq (Scheme.Hom.resLE_comp_ι f hle)
    ((hp.isShriekable_resLE hq hpe hle hU).comp (hq.isShriekable_ι V))

end IsFiniteTypeOverNoetherian

namespace SeparatedCovering

/-- A covering of `X` by opens separated and of finite type over `S`, each contained in the
preimage of a member of such a covering of `Y`, is also a covering by opens separated and of
finite type over `Y`. This is the covering `𝒰 : X = ⋃ U_{ji}` of the proof of
[Stacks, Tag 0AUB], read over `Y` rather than over `S`. -/
def overMid {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S} {ι : Type w}
    {J : Type w'} (𝒰 : SeparatedCovering p ι) (𝒱 : SeparatedCovering q J)
    (hp : IsFiniteTypeOverNoetherian p) (hq : IsFiniteTypeOverNoetherian q) (hpe : f ≫ q = p)
    (idx : ι → J) (hle : ∀ k, 𝒰.U k ≤ f ⁻¹ᵁ 𝒱.U (idx k)) : SeparatedCovering f ι where
  U := 𝒰.U
  finite := 𝒰.finite
  covers := 𝒰.covers
  shriekable k := hp.isShriekable_ι_comp hq hpe (hle k) (𝒰.shriekable k)

end SeparatedCovering

namespace UpperShriek

variable {𝒟} (A : UpperShriek 𝒟)

/-- The transport of a comparison along a factorization: given `g : W → V` over both `c` and
`b`, and an identification `β : b^! L ≅ c^! ω` on `V`, the isomorphism `m^! ω ≅ n^! L` on `W`
obtained from `g^! β^{-1}` by the canonical comparisons of [Stacks, Tag 0ATX].

With `g = f_{ji}`, `β = β_j` and `m = p_{ji}`, this is the composite
`p_{ji}^! ω_S^• = f_{ji}^! q_j^! ω_S^• → f_{ji}^!(L|_{V_j}) = (f'_{ji})^! L` of the proof of
[Stacks, Tag 0AUB]. -/
def transport {W V T Z : Scheme.{u}} {g : W ⟶ V} {c : V ⟶ T} {b : V ⟶ Z} {m : W ⟶ T}
    {n : W ⟶ Z} (hgc : g ≫ c = m) (hgb : g ≫ b = n) (hg : IsShriekable g)
    (hc : IsShriekable c) (hb : IsShriekable b) (hm : IsShriekable m) (hn : IsShriekable n)
    {ω : 𝒟 T} {L : 𝒟 Z} (β : (A.shriek b hb).obj L ≅ (A.shriek c hc).obj ω) :
    (A.shriek m hm).obj ω ≅ (A.shriek n hn).obj L :=
  (A.factorIso hgc hg hc hm).app ω ≪≫ (A.shriek g hg).mapIso β.symm ≪≫
    ((A.factorIso hgb hg hb hn).app L).symm

/-- The restriction along `r : W' → W` of a comparison `m^! ω ≅ n^! L`, conjugated by the
canonical comparisons for `r ≫ m` and `r ≫ n`. These conjugations are the maps `φ` by which
the normalizations of [Stacks, Tag 0AU5] are compared on an overlap. -/
def restrictCompare {W' W T Z : Scheme.{u}} {r : W' ⟶ W} {m : W ⟶ T} {n : W ⟶ Z}
    {m' : W' ⟶ T} {n' : W' ⟶ Z} (hrm : r ≫ m = m') (hrn : r ≫ n = n') (hr : IsShriekable r)
    (hm : IsShriekable m) (hn : IsShriekable n) (hm' : IsShriekable m')
    (hn' : IsShriekable n') {ω : 𝒟 T} {L : 𝒟 Z}
    (Θ : (A.shriek m hm).obj ω ≅ (A.shriek n hn).obj L) :
    (A.shriek m' hm').obj ω ≅ (A.shriek n' hn').obj L :=
  (A.factorIso hrm hr hm hm').app ω ≪≫ (A.shriek r hr).mapIso Θ ≪≫
    ((A.factorIso hrn hr hn hn').app L).symm

/-- The transports are a morphism of local systems: restricting the transport built from `β`
along `r : W' → W` gives the transport built from `β` and the factorization `r ≫ g` of the
restriction. This is the coherence of [Stacks, Tag 0ATY] applied twice, once over `c` and
once over `b`, together with the naturality of the remaining comparison. -/
theorem restrictCompare_transport {W' W V T Z : Scheme.{u}} {r : W' ⟶ W} {g : W ⟶ V}
    {g' : W' ⟶ V} {c : V ⟶ T} {b : V ⟶ Z} {m : W ⟶ T} {n : W ⟶ Z} {m' : W' ⟶ T}
    {n' : W' ⟶ Z} (hgc : g ≫ c = m) (hgb : g ≫ b = n) (hrg : r ≫ g = g')
    (hrm : r ≫ m = m') (hrn : r ≫ n = n') (hg'c : g' ≫ c = m') (hg'b : g' ≫ b = n')
    (hr : IsShriekable r) (hg : IsShriekable g) (hc : IsShriekable c) (hb : IsShriekable b)
    (hm : IsShriekable m) (hn : IsShriekable n) (hg' : IsShriekable g')
    (hm' : IsShriekable m') (hn' : IsShriekable n') {ω : 𝒟 T} {L : 𝒟 Z}
    (β : (A.shriek b hb).obj L ≅ (A.shriek c hc).obj ω) :
    A.restrictCompare hrm hrn hr hm hn hm' hn' (A.transport hgc hgb hg hc hb hm hn β) =
      A.transport hg'c hg'b hg' hc hb hm' hn' β := by
  have pc := A.factorIso_assoc hrg hgc hg'c hrm hr hg hc hg' hm hm' ω
  have pb := A.factorIso_assoc hrg hgb hg'b hrn hr hg hb hg' hn hn' L
  have pbiso : (A.factorIso hrn hr hn hn').app L ≪≫
      (A.shriek r hr).mapIso ((A.factorIso hgb hg hb hn).app L) =
        (A.factorIso hg'b hg' hb hn').app L ≪≫
          (A.factorIso hrg hr hg hg').app ((A.shriek b hb).obj L) := Iso.ext pb
  have pbinv := congrArg Iso.inv pbiso
  have nat := (A.factorIso hrg hr hg hg').hom.naturality β.inv
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Functor.comp_map] at pbinv nat
  refine Iso.ext ?_
  simp only [restrictCompare, transport, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc]
  rw [reassoc_of% pc, ← reassoc_of% nat, pbinv, Iso.hom_inv_id_app_assoc]

/-- Two factorizations of the same morphism through members `V`, `V'` of a covering give the
same transport, as soon as the two transports agree on a common refinement `D`. This is the
cocycle condition for the `β_j` of [Stacks, Tag 0AUB], pulled back along `W → D`. -/
theorem transport_eq_transport {W D V V' T Z : Scheme.{u}} {w : W ⟶ D} {s : D ⟶ V}
    {s' : D ⟶ V'} {g : W ⟶ V} {g' : W ⟶ V'} {c : V ⟶ T} {c' : V' ⟶ T} {b : V ⟶ Z}
    {b' : V' ⟶ Z} {dc : D ⟶ T} {db : D ⟶ Z} {m : W ⟶ T} {n : W ⟶ Z} (hws : w ≫ s = g)
    (hws' : w ≫ s' = g') (hsc : s ≫ c = dc) (hsb : s ≫ b = db) (hsc' : s' ≫ c' = dc)
    (hsb' : s' ≫ b' = db) (hwc : w ≫ dc = m) (hwb : w ≫ db = n) (hgc : g ≫ c = m)
    (hgb : g ≫ b = n) (hgc' : g' ≫ c' = m) (hgb' : g' ≫ b' = n) (hw : IsShriekable w)
    (hs : IsShriekable s) (hs' : IsShriekable s') (hg : IsShriekable g)
    (hg' : IsShriekable g') (hc : IsShriekable c) (hc' : IsShriekable c')
    (hb : IsShriekable b) (hb' : IsShriekable b') (hdc : IsShriekable dc)
    (hdb : IsShriekable db) (hm : IsShriekable m) (hn : IsShriekable n) {ω : 𝒟 T} {L : 𝒟 Z}
    (β : (A.shriek b hb).obj L ≅ (A.shriek c hc).obj ω)
    (β' : (A.shriek b' hb').obj L ≅ (A.shriek c' hc').obj ω)
    (hβ : A.transport hsc hsb hs hc hb hdc hdb β =
      A.transport hsc' hsb' hs' hc' hb' hdc hdb β') :
    A.transport hgc hgb hg hc hb hm hn β = A.transport hgc' hgb' hg' hc' hb' hm hn β' := by
  rw [← A.restrictCompare_transport hsc hsb hws hwc hwb hgc hgb hw hs hc hb hdc hdb hg hm hn β,
    ← A.restrictCompare_transport hsc' hsb' hws' hwc hwb hgc' hgb' hw hs' hc' hb' hdc hdb hg'
      hm hn β', hβ]

/-- The restriction of a normalization isomorphism to a smaller open is the transport, read
backwards, of that isomorphism along the inclusion. -/
theorem restrictLocalIso_eq_transport_symm {X S : Scheme.{u}} {p : X ⟶ S}
    (hp : IsFiniteTypeOverNoetherian p) (ω : 𝒟 S) (K : 𝒟 X) {W U : X.Opens} (h : W ≤ U)
    (hU : IsShriekable (U.ι ≫ p)) (α : A.restrictTo hp U K ≅ A.localModel hU ω) :
    A.restrictLocalIso hp ω K h hU α =
      (A.transport (show X.homOfLE h ≫ U.ι ≫ p = W.ι ≫ p by
            rw [← Category.assoc, X.homOfLE_ι])
          (X.homOfLE_ι h) (hp.isShriekable_homOfLE h) hU (hp.isShriekable_ι U)
          (hp.isShriekable_le h hU) (hp.isShriekable_ι W) α).symm :=
  Iso.ext (by simp [restrictLocalIso, transport])

/-- Restricting a normalization isomorphism which has been composed with a transport: the
restriction of the composite is the restriction of the isomorphism followed by the
restriction of the transport. -/
theorem restrictLocalIso_trans {X S Z : Scheme.{u}} {p : X ⟶ S} {f : X ⟶ Z}
    (hp : IsFiniteTypeOverNoetherian p) (hf : IsFiniteTypeOverNoetherian f) (ω : 𝒟 S)
    (L : 𝒟 Z) (K : 𝒟 X) {W U : X.Opens} (h : W ≤ U) (hU : IsShriekable (U.ι ≫ p))
    (hU' : IsShriekable (U.ι ≫ f)) (α : A.restrictTo hp U K ≅ A.localModel hU ω)
    (Θ : A.localModel hU ω ≅ A.localModel hU' L) :
    A.restrictLocalIso hf L K h hU' (α ≪≫ Θ) =
      A.restrictLocalIso hp ω K h hU α ≪≫
        A.restrictCompare
          (show X.homOfLE h ≫ U.ι ≫ p = W.ι ≫ p by rw [← Category.assoc, X.homOfLE_ι])
          (show X.homOfLE h ≫ U.ι ≫ f = W.ι ≫ f by rw [← Category.assoc, X.homOfLE_ι])
          (hp.isShriekable_homOfLE h) hU hU' (hp.isShriekable_le h hU)
          (hf.isShriekable_le h hU') Θ :=
  Iso.ext (by simp [restrictLocalIso, restrictCompare])

end UpperShriek

namespace Normalized

variable {𝒟} {A : UpperShriek 𝒟} {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S}
  (hpe : f ≫ q = p) (hp : IsFiniteTypeOverNoetherian p) (hq : IsFiniteTypeOverNoetherian q)
  {ωS : 𝒟 S} {ι : Type w} {J : Type w'} {𝒰 : SeparatedCovering p ι}
  {𝒱 : SeparatedCovering q J} (idx : ι → J) (hle : ∀ k, 𝒰.U k ≤ f ⁻¹ᵁ 𝒱.U (idx k))
  (𝒩X : Normalized A hp ωS 𝒰) (𝒩Y : Normalized A hq ωS 𝒱)

/-- The isomorphism `α_{ji}` of the proof of [Stacks, Tag 0AUB]: the normalization
`γ_{ji} : K|_{U_{ji}} ≅ p_{ji}^! ω_S^•` relative to `ω_S^•`, followed by the transport of the
normalization `β_j` of `L` along `f_{ji} : U_{ji} → V_j`. -/
def overMidIso (k : ι) :
    A.restrictTo (hp.of_comp' hq hpe) (𝒰.U k) 𝒩X.complex ≅
      A.localModel ((𝒰.overMid 𝒱 hp hq hpe idx hle).shriekable k) 𝒩Y.complex :=
  𝒩X.localIso k ≪≫
    A.transport (resLE_comp_structure hpe (hle k)) (Scheme.Hom.resLE_comp_ι f (hle k))
      (hp.isShriekable_resLE hq hpe (hle k) (𝒰.shriekable k)) (𝒱.shriekable (idx k))
      (hq.isShriekable_ι (𝒱.U (idx k))) (𝒰.shriekable k)
      (hp.isShriekable_ι_comp hq hpe (hle k) (𝒰.shriekable k)) (𝒩Y.localIso (idx k))

/-- The isomorphisms `α_{ji}` of [Stacks, Tag 0AUB] agree on overlaps. This is the
verification the source calls formal: composing with `γ` reduces it to a statement about the
canonical comparisons alone, namely that the transports are a morphism of local systems
(`UpperShriek.restrictCompare_transport`), together with the cocycle condition for the `β_j`
pulled back to the overlap (`UpperShriek.transport_eq_transport`). -/
theorem overMid_compat (k k' : ι) :
    A.restrictLocalIso (hp.of_comp' hq hpe) 𝒩Y.complex 𝒩X.complex
        (inf_le_left : 𝒰.U k ⊓ 𝒰.U k' ≤ 𝒰.U k)
        (hp.isShriekable_ι_comp hq hpe (hle k) (𝒰.shriekable k))
        (𝒩X.localIso k ≪≫
          A.transport (resLE_comp_structure hpe (hle k)) (Scheme.Hom.resLE_comp_ι f (hle k))
            (hp.isShriekable_resLE hq hpe (hle k) (𝒰.shriekable k)) (𝒱.shriekable (idx k))
            (hq.isShriekable_ι (𝒱.U (idx k))) (𝒰.shriekable k)
            (hp.isShriekable_ι_comp hq hpe (hle k) (𝒰.shriekable k)) (𝒩Y.localIso (idx k))) =
      A.restrictLocalIso (hp.of_comp' hq hpe) 𝒩Y.complex 𝒩X.complex
        (inf_le_right : 𝒰.U k ⊓ 𝒰.U k' ≤ 𝒰.U k')
        (hp.isShriekable_ι_comp hq hpe (hle k') (𝒰.shriekable k'))
        (𝒩X.localIso k' ≪≫
          A.transport (resLE_comp_structure hpe (hle k')) (Scheme.Hom.resLE_comp_ι f (hle k'))
            (hp.isShriekable_resLE hq hpe (hle k') (𝒰.shriekable k')) (𝒱.shriekable (idx k'))
            (hq.isShriekable_ι (𝒱.U (idx k'))) (𝒰.shriekable k')
            (hp.isShriekable_ι_comp hq hpe (hle k') (𝒰.shriekable k'))
            (𝒩Y.localIso (idx k'))) := by
  have hfc := hp.of_comp' hq hpe
  -- the overlaps `W = U_{ji} ∩ U_{j'i'}` in `X` and `D = V_j ∩ V_{j'}` in `Y`
  have hWp : IsShriekable ((𝒰.U k ⊓ 𝒰.U k').ι ≫ p) :=
    hp.isShriekable_le inf_le_left (𝒰.shriekable k)
  have hWf : IsShriekable ((𝒰.U k ⊓ 𝒰.U k').ι ≫ f) :=
    hfc.isShriekable_le inf_le_left (hp.isShriekable_ι_comp hq hpe (hle k) (𝒰.shriekable k))
  have hleW : 𝒰.U k ⊓ 𝒰.U k' ≤ f ⁻¹ᵁ (𝒱.U (idx k) ⊓ 𝒱.U (idx k')) := fun x hx =>
    ⟨hle k hx.1, hle k' hx.2⟩
  have hleWk : 𝒰.U k ⊓ 𝒰.U k' ≤ f ⁻¹ᵁ 𝒱.U (idx k) := inf_le_left.trans (hle k)
  have hleWk' : 𝒰.U k ⊓ 𝒰.U k' ≤ f ⁻¹ᵁ 𝒱.U (idx k') := inf_le_right.trans (hle k')
  have hDq : IsShriekable ((𝒱.U (idx k) ⊓ 𝒱.U (idx k')).ι ≫ q) :=
    hq.isShriekable_le inf_le_left (𝒱.shriekable (idx k))
  -- the cocycle condition for the `β_j` on `D`
  have hβ := 𝒩Y.compat (idx k) (idx k')
  rw [A.restrictLocalIso_eq_transport_symm hq, A.restrictLocalIso_eq_transport_symm hq] at hβ
  rw [Iso.symm_eq_iff] at hβ
  rw [A.restrictLocalIso_trans hp hfc, A.restrictLocalIso_trans hp hfc,
    A.restrictCompare_transport
      (hrg := by simp)
      (hg'c := resLE_comp_structure hpe hleWk) (hg'b := Scheme.Hom.resLE_comp_ι f hleWk)
      (hg' := hp.isShriekable_resLE hq hpe hleWk hWp),
    A.restrictCompare_transport
      (hrg := by simp)
      (hg'c := resLE_comp_structure hpe hleWk') (hg'b := Scheme.Hom.resLE_comp_ι f hleWk')
      (hg' := hp.isShriekable_resLE hq hpe hleWk' hWp),
    𝒩X.compat k k',
    A.transport_eq_transport (by simp) (by simp)
      (by simp)
      (Y.homOfLE_ι _)
      (by simp)
      (Y.homOfLE_ι _) (resLE_comp_structure hpe hleW) (Scheme.Hom.resLE_comp_ι f hleW)
      (resLE_comp_structure hpe hleWk) (Scheme.Hom.resLE_comp_ι f hleWk)
      (resLE_comp_structure hpe hleWk') (Scheme.Hom.resLE_comp_ι f hleWk')
      (hp.isShriekable_resLE hq hpe hleW hWp) (hq.isShriekable_homOfLE inf_le_left)
      (hq.isShriekable_homOfLE inf_le_right) (hp.isShriekable_resLE hq hpe hleWk hWp)
      (hp.isShriekable_resLE hq hpe hleWk' hWp) (𝒱.shriekable (idx k))
      (𝒱.shriekable (idx k')) (hq.isShriekable_ι _) (hq.isShriekable_ι _) hDq
      (hq.isShriekable_ι _) hWp hWf (𝒩Y.localIso (idx k)) (𝒩Y.localIso (idx k')) hβ]

/-- **[Stacks, Tag 0AUB]**, the transitivity of normalization: a complex on `X` normalized
relative to `ω_S^•` is normalized relative to a complex on `Y` normalized relative to
`ω_S^•`, for the covering of `X` read over `Y`. -/
def overMid : Normalized A (hp.of_comp' hq hpe) 𝒩Y.complex
    (𝒰.overMid 𝒱 hp hq hpe idx hle) where
  complex := 𝒩X.complex
  localIso k := overMidIso hpe hp hq idx hle 𝒩X 𝒩Y k
  compat k k' := overMid_compat hpe hp hq idx hle 𝒩X 𝒩Y k k'

/-- The complex of `Normalized.overMid` is the one it started from: it is `ω_X^•` itself that
[Stacks, Tag 0AUB] renormalizes. -/
@[simp]
theorem overMid_complex : (𝒩X.overMid hpe hp hq idx hle 𝒩Y).complex = 𝒩X.complex := rfl

end Normalized

/-- **[Stacks, Tag 0AUB]** Let `S` be a Noetherian scheme carrying `ω_S^•`, let `q : Y ⟶ S`
and `p = f ≫ q : X ⟶ S` be of finite type, and let `𝒱` and `𝒰` be coverings of `Y` and of
`X` by opens separated and of finite type over `S`, with each `U_k` carried by `f` into
`V_{idx k}`. If `ω_X^•` is normalized relative to `ω_S^•` and `𝒰`, and `ω_Y^•` is normalized
relative to `ω_S^•` and `𝒱`, then `ω_X^•` is normalized relative to `ω_Y^•` and `𝒰` read over
`Y`.

Normalization here is the primitive notion of the text of [Stacks, Tag 0AU5] -- the pair
`(K, α_i)` -- rather than the covering-free Definition [Stacks, Tag 0AUA], and it is the
notion the proof of 0AUB manipulates. That `ω_X^•` is again dualizing is not part of the
statement because `Normalized` does not record dualizing-ness; it is [Stacks, Tag 0AU8]. -/
@[stacks 0AUB "assuming the upper-shriek formalism of Stacks 0A9E/0ATX/0ATY as the \
parameter UpperShriek, pending its landing"]
theorem exists_normalized_of_normalized {𝒟 : Scheme.{u} → Type v}
    [∀ X : Scheme.{u}, Category.{v'} (𝒟 X)] (A : UpperShriek 𝒟) {X Y S : Scheme.{u}}
    {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S} (hpe : f ≫ q = p)
    (hp : IsFiniteTypeOverNoetherian p) (hq : IsFiniteTypeOverNoetherian q) (ωS : 𝒟 S)
    {ι : Type w} {J : Type w'} (𝒰 : SeparatedCovering p ι) (𝒱 : SeparatedCovering q J)
    (idx : ι → J) (hle : ∀ k, 𝒰.U k ≤ f ⁻¹ᵁ 𝒱.U (idx k)) (𝒩X : Normalized A hp ωS 𝒰)
    (𝒩Y : Normalized A hq ωS 𝒱) :
    ∃ 𝒩 : Normalized A (hp.of_comp' hq hpe) 𝒩Y.complex (𝒰.overMid 𝒱 hp hq hpe idx hle),
      𝒩.complex = 𝒩X.complex :=
  ⟨𝒩X.overMid hpe hp hq idx hle 𝒩Y, rfl⟩

end Stacks.Duality

end
