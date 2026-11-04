module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedLocality.InvertibilityAlongDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangePasting
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeLocalOnTheBase
import StacksCore.Tactic.EgaSgaAttribute

/-!
# [Stacks, Tag 08IB]: from an affine base to an arbitrary one

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a Cartesian square of schemes with `f` quasi-compact and quasi-separated and `X`, `S'` tor
independent over `S`, and let `K` be an object of `D(𝒪_X)` with quasi-coherent cohomology sheaves.
[Stacks, Tag 08IB] asserts that the derived base-change map of [Stacks, Tag 08HY] is then an
isomorphism.  This module carries the localization step of the source's proof of
[Stacks, Tag 0DJ9]: the statement over an *arbitrary* base follows from the statement over a base
that is affine, together with an affine source of the horizontal arrow.

## Main definitions

* `AlgebraicGeometry.DerivedBaseChangeIsIsoOverAffineBase` — [Stacks, Tag 08IB] for a Cartesian
  square both of whose bases are affine.  This is
  `AlgebraicGeometry.DerivedBaseChangeIsIsoOnQuasicoherent` with `IsAffine S` and `IsAffine S'`
  added.

## Main results

* `AlgebraicGeometry.torIndependent_resLE` — **tor independence restricts to opens**: if `X` and
  `Y` are tor independent over `S`, then for opens `U ⊆ X`, `W ⊆ Y` lying over an open `V ⊆ S` the
  restrictions `U ⟶ V` and `W ⟶ V` are tor independent.  Checked on affine opens through the
  criterion of [Stacks, Tag 0FXV].
* `AlgebraicGeometry.exists_affineOpens_cover_le_preimage` — the refined affine cover: a cover of
  `S'` by affine opens, each lying over an affine open of `S`.
* `AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent_of_overAffineBase` — **the theorem**:
  `DerivedBaseChangeIsIsoOverAffineBase` implies
  `AlgebraicGeometry.DerivedBaseChangeIsIsoOnQuasicoherent`, i.e. [Stacks, Tag 08IB] over an
  affine base implies [Stacks, Tag 08IB].
* `Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_hpaste` and
  `Stacks.Cohomology.DerivedBaseChange.isIso_derivedPullback_map_derivedBaseChangeMap_hpaste` —
  the two transports of invertibility across the horizontal pasting of [Stacks, Tag 0ATM]: from
  the two constituent squares to the rectangle, and back from the rectangle to the right-hand
  square after derived pullback along the lower-left arrow.

## Implementation notes

The source says "to check this is an isomorphism we may work locally on `S'`".  Working locally on
`S'` alone is not enough here, because the affine case needs *both* bases affine; so the cover of
`S'` is refined to one whose members map into affine opens of `S`, which is possible by
`exists_affineOpens_cover_le_preimage`, and the base `S` is shrunk along with `S'`.  The steps are
the exact analogues of the two reductions of
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_quasiCoherent` for
[Stacks, Tag 08EU].

*Invertibility is local on `S'`.*  This is
`Stacks.Cohomology.isIso_of_isIso_derivedPullback_ofRestrict`, applied to the refined cover.  The
inclusion
`S'.toRingedSpace.ofRestrict V'.isOpenEmbedding` of that statement is the morphism of ringed
spaces underlying `V'.ι`, so no bridging lemma is needed; this is the identification
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/ProjectionFormulaQuasiCoherent.lean`
also relies on.

*Two pastings.*  Fix a member `V' ⊆ S'` of the cover and the affine open `V ⊆ S` it maps into, let
`f_V : f ⁻¹ᵁ V ⟶ V` be the restriction of `f` and `g_V : V' ⟶ V` the restriction of `g`, and let
`Z = (f ⁻¹ᵁ V) ×_V V'`.  Then `Z` is also `X' ×_{S'} V'`, by `CategoryTheory.IsPullback.of_right`
applied to the rectangle; the two presentations of the fourth corner are the same scheme because
`Z` is chosen once and the comparison `Z ⟶ X'` is the lift supplied by the given Cartesian square.
Pasting the square of `f_V` along `g_V` with the base change of `f` along `V.ι` gives invertibility
of the rectangle's base-change map, whose bottom arrow is `g_V ≫ V.ι`; pasting the base change of
`f'` along `V'.ι` with the given square reduces `L(V'.ι)^*` of the given map to the same rectangle,
whose bottom arrow is read as `V'.ι ≫ g`.  The two readings are identified by
`isIso_derivedBaseChangeMap_congr`, a transport along the equalities of the two composites — the
only transport in the argument, and it is needed because the rectangle is reached through two
different factorizations of its bottom arrow.

Of the two inner squares, the one over the open immersions contributes an invertible base-change
map for *every* object, by
`Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersion`; the one over
`g_V : V' ⟶ V` is the affine case, and the hypotheses it needs are discharged as follows.
Quasi-compactness and quasi-separatedness of `f_V` are stability of those properties under base
change.  Quasi-coherence of the restricted complex is [Stacks, Tag 08DW] part (1),
`Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel`.  Tor independence of `f_V` and
`g_V` is `torIndependent_resLE`, which is proved — not assumed — from the affine criterion of
[Stacks, Tag 0FXV]: a compatible triple of affine opens for the restricted morphisms is, under the
open immersions, a compatible triple for the original ones, and `Scheme.Hom.resLE_appLE` says that
the two ring maps whose algebra structures the condition is stated against are literally the same.

## References

* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 0ATM](https://stacks.math.columbia.edu/tag/0ATM)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 0FXV](https://stacks.math.columbia.edu/tag/0FXV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Cohomology.DerivedBaseChange

/-! ### Invertibility across the horizontal pasting of [Stacks, Tag 0ATM] -/

section Pasting

/-- **The middle factor of a fourfold composite is invertible** when the composite and the three
other factors are.  Used to read the identity of [Stacks, Tag 0ATM] as a transport of
invertibility; stated abstractly so that the derived functors never have to be unfolded. -/
private theorem isIso_of_comp₄_middle {C : Type*} [Category C] {O₁ O₂ O₃ O₄ O₅ : C}
    (a : O₁ ⟶ O₂) (b : O₂ ⟶ O₃) (c : O₃ ⟶ O₄) (d : O₄ ⟶ O₅) (e : O₁ ⟶ O₅)
    [IsIso a] [IsIso c] [IsIso d] [IsIso e] (key : a ≫ b ≫ c ≫ d = e) : IsIso b := by
  have : IsIso (b ≫ c ≫ d) := by
    rw [(IsIso.eq_inv_comp a).mpr key]
    infer_instance
  exact IsIso.of_isIso_comp_right b (c ≫ d)

variable {X'' X' X Y'' Y' Y : RingedSpace.{u, u}} (g' : X'' ⟶ X') (g : X' ⟶ X)
  (f'' : X'' ⟶ Y'') (f' : X' ⟶ Y') (f : X ⟶ Y) (h' : Y'' ⟶ Y') (h : Y' ⟶ Y)

/-- **From the two squares to the rectangle.**  For two horizontally composable commutative
squares of ringed spaces, the derived base-change map of the outer rectangle is invertible at `K`
as soon as the derived pullback along `h'` of the right-hand square's map at `K` and the left-hand
square's map at `Lg^*K` are.

The identity of [Stacks, Tag 0ATM],
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_comp_horizontal`, exhibits the
rectangle's map as a composite of those two together with the composition isomorphisms of
[Stacks, Tag 0D5S]. -/
theorem isIso_derivedBaseChangeMap_hpaste (sq₁ : g ≫ f = f' ≫ h) (sq₂ : g' ≫ f' = f'' ≫ h')
    (sq : (g' ≫ g) ≫ f = f'' ≫ h' ≫ h)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hright : IsIso ((derivedPullback h').map (derivedBaseChangeMap g f' f h sq₁ K)))
    (hleft : IsIso (derivedBaseChangeMap g' f'' f' h' sq₂ ((derivedPullback g).obj K))) :
    IsIso (derivedBaseChangeMap (g' ≫ g) f'' f (h' ≫ h) sq K) := by
  have := hright
  have := hleft
  have key := derivedBaseChangeMap_comp_horizontal g' g f'' f' f h' h sq₁ sq₂ K
  rw [← key]
  infer_instance

/-- **From the rectangle back to the right-hand square.**  For two horizontally composable
commutative squares of ringed spaces, the derived pullback along `h'` of the right-hand square's
base-change map at `K` is invertible as soon as the outer rectangle's map at `K` and the left-hand
square's map at `Lg^*K` are.

This is the localization step in the shape it is consumed: taking `h'` to be an open immersion of
the base and the left-hand square its base change, the left-hand square's map is invertible
unconditionally, so invertibility over the open follows from invertibility of the rectangle. -/
theorem isIso_derivedPullback_map_derivedBaseChangeMap_hpaste
    (sq₁ : g ≫ f = f' ≫ h) (sq₂ : g' ≫ f' = f'' ≫ h')
    (sq : (g' ≫ g) ≫ f = f'' ≫ h' ≫ h)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (houter : IsIso (derivedBaseChangeMap (g' ≫ g) f'' f (h' ≫ h) sq K))
    (hleft : IsIso (derivedBaseChangeMap g' f'' f' h' sq₂ ((derivedPullback g).obj K))) :
    IsIso ((derivedPullback h').map (derivedBaseChangeMap g f' f h sq₁ K)) := by
  have := hleft
  have : IsIso (derivedBaseChangeMap (g' ≫ g) f'' f (h' ≫ h)
      (hcomp_square g' g f'' f' f h' h sq₁ sq₂) K) := houter
  exact isIso_of_comp₄_middle _ _ _ _ _
    (derivedBaseChangeMap_comp_horizontal g' g f'' f' f h' h sq₁ sq₂ K)

end Pasting

end Stacks.Cohomology.DerivedBaseChange

namespace AlgebraicGeometry

/-! ### Tor independence restricted to opens -/

/-- **Tor independence of two algebras over a base transports along equalities of the two
structure maps.**  The condition is stated against the algebra structures the two ring maps
induce, so replacing the maps by equal ones replaces those instances. -/
private theorem torIndependent_congr_appLE {R A B : CommRingCat.{u}} {a a' : R ⟶ A} {b b' : R ⟶ B}
    (ha : a = a') (hb : b = b')
    (h : letI := a'.hom.toAlgebra; letI := b'.hom.toAlgebra
      Algebra.TorIndependent R A B) :
    letI := a.hom.toAlgebra; letI := b.hom.toAlgebra
    Algebra.TorIndependent R A B := by
  subst ha
  subst hb
  exact h

/-- **Tor independence restricts to opens.**  Let `X` and `Y` be tor independent over `S`, let
`V ⊆ S` be an open and let `U ⊆ X`, `W ⊆ Y` be opens lying over `V`.  Then the restrictions
`U ⟶ V` and `W ⟶ V` of `f` and `g` are tor independent.

The criterion of [Stacks, Tag 0FXV] reduces the conclusion to a condition on compatible triples of
affine opens of `U`, `W` and `V`.  Under the open immersions such a triple becomes a compatible
triple of affine opens of `X`, `Y` and `S`: an affine open of an open subscheme has affine image,
by `AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion`, the compatibility is
`AlgebraicGeometry.Scheme.Hom.le_resLE_preimage_iff`, and the sections over the image are by
definition the sections over the affine open.  Moreover the two ring maps the condition is stated
against coincide, by `AlgebraicGeometry.Scheme.Hom.resLE_appLE`, so the restricted condition *is*
the original one. -/
@[sga "6 III 1.5" "restriction to opens"]
theorem torIndependent_resLE {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (htor : TorIndependent f g) {V : S.Opens} {U : X.Opens} {W : Y.Opens}
    (hU : U ≤ f ⁻¹ᵁ V) (hW : W ≤ g ⁻¹ᵁ V) :
    TorIndependent (f.resLE V U hU) (g.resLE V W hW) := by
  have h2 := ((torIndependent_tfae f g).out 1 2).mp htor
  refine ((torIndependent_tfae (f.resLE V U hU) (g.resLE V W hW)).out 2 1).mp ?_
  intro A hA B hB O hO hAO hBO
  exact torIndependent_congr_appLE (Scheme.Hom.resLE_appLE f hU O A hAO)
    (Scheme.Hom.resLE_appLE g hW O B hBO)
    (h2 (U.ι ''ᵁ A) (U.ι.isAffineOpen_iff_of_isOpenImmersion.mpr hA)
      (W.ι ''ᵁ B) (W.ι.isAffineOpen_iff_of_isOpenImmersion.mpr hB)
      (V.ι ''ᵁ O) (V.ι.isAffineOpen_iff_of_isOpenImmersion.mpr hO)
      ((Scheme.Hom.le_resLE_preimage_iff f hU O A).mp hAO)
      ((Scheme.Hom.le_resLE_preimage_iff g hW O B).mp hBO))

/-- **Tor independence of the restriction of `f` to the preimage of an open with the restriction
of `g` to an open over it.**  This is `torIndependent_resLE` read at
`AlgebraicGeometry.morphismRestrict`, the form in which the restricted square is Cartesian. -/
theorem torIndependent_morphismRestrict_resLE {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (htor : TorIndependent f g) {V : S.Opens} {W : Y.Opens} (hW : W ≤ g ⁻¹ᵁ V) :
    TorIndependent (f ∣_ V) (g.resLE V W hW) := by
  rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  exact torIndependent_resLE f g htor le_rfl hW

/-! ### The refined affine cover of `S'` -/

/-- **The refined affine cover of `S'`**: an affine open `V' s' ⊆ S'` around each point `s'`,
together with an affine open `V s' ⊆ S` containing its image under `g`.  The `V' s'` cover `S'`.

Around `g(s')` take an affine open `V` of `S`, then inside `g ⁻¹ᵁ V` an affine open of `S'` around
`s'`; both exist because the affine opens form a basis.  The choice is then made at every point at
once. -/
theorem exists_affineOpens_cover_le_preimage {S S' : Scheme.{u}} (g : S' ⟶ S) :
    ∃ (V' : S' → S'.affineOpens) (V : S' → S.affineOpens),
      (∀ s', (V' s' : S'.Opens) ≤ g ⁻¹ᵁ (V s' : S.Opens)) ∧
        (⨆ s', (V' s' : S'.Opens)) = ⊤ := by
  have key : ∀ s' : S', ∃ p : S'.affineOpens × S.affineOpens,
      s' ∈ (p.1 : S'.Opens) ∧ (p.1 : S'.Opens) ≤ g ⁻¹ᵁ (p.2 : S.Opens) := by
    intro s'
    obtain ⟨V, hV, hgs', -⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens S)
        (U := (⊤ : S.Opens)) (x := g.base s') trivial
    obtain ⟨V', hV', hs', hle⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens S')
        (U := g ⁻¹ᵁ V) (x := s') hgs'
    exact ⟨(⟨V', hV'⟩, ⟨V, hV⟩), hs', hle⟩
  choose p hmem hle using key
  refine ⟨fun s' => (p s').1, fun s' => (p s').2, hle, eq_top_iff.mpr fun s' _ => ?_⟩
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨s', hmem s'⟩

/-! ### [Stacks, Tag 08IB] over an affine base -/

/-- **[Stacks, Tag 08IB] for a Cartesian square both of whose bases are affine.**  This is
`AlgebraicGeometry.DerivedBaseChangeIsIsoOnQuasicoherent` with `IsAffine S` and `IsAffine S'`
added; it is the form in which the affine chart comparison of [Stacks, Tag 0DJ8] can be fed to the
globalization of [Stacks, Tag 0DJ9]. -/
abbrev DerivedBaseChangeIsIsoOverAffineBase : Prop :=
  ∀ {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S),
    IsAffine S → IsAffine S' →
    IsPullback g' f' f g → QuasiCompact f → QuasiSeparated f → TorIndependent f g →
      ∀ (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
          f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom) (K : DerivedCategory X.Modules),
        (∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj K).IsQuasicoherent) →
        IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
          g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq K)

/-! ### The localization step -/

/-- The commutativity of a square of schemes, read on the underlying ringed spaces. -/
private theorem toShHom_w {Z A B C : Scheme.{u}} {a : Z ⟶ A} {b : A ⟶ C} {c : Z ⟶ B} {d : B ⟶ C}
    (w : a ≫ b = c ≫ d) :
    a.toLRSHom.toShHom ≫ b.toLRSHom.toShHom = c.toLRSHom.toShHom ≫ d.toLRSHom.toShHom :=
  congrArg (fun φ : Z ⟶ C => φ.toLRSHom.toShHom) w

/-- **[Stacks, Tag 08IB] after derived pullback to a member of the refined affine cover.**  For a
Cartesian square as in [Stacks, Tag 08IB], an affine open `V ⊆ S` and an affine open `V' ⊆ S'`
with `g(V') ⊆ V`, the derived pullback along `V'.ι` of the derived base-change map is invertible,
granted [Stacks, Tag 08IB] over an affine base.

Two applications of the horizontal pasting of [Stacks, Tag 0ATM] around the rectangle over
`V' ⟶ S`: one factoring its bottom arrow as `V' ⟶ S' ⟶ S`, the other as `V' ⟶ V ⟶ S`.  The two
inner squares over open immersions contribute unconditionally invertible maps; the remaining
square is the base change of `f ⁻¹ᵁ V ⟶ V` along `V' ⟶ V`, whose two bases are affine. -/
theorem isIso_derivedPullback_map_derivedBaseChangeMap_of_affineOpens
    (H : DerivedBaseChangeIsIsoOverAffineBase.{u})
    {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (hsq : IsPullback g' f' f g) (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
    (htor : TorIndependent f g)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (K : DerivedCategory X.Modules)
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj K).IsQuasicoherent)
    (V : S.affineOpens) (V' : S'.affineOpens)
    (hle : (V' : S'.Opens) ≤ g ⁻¹ᵁ (V : S.Opens)) :
    IsIso ((derivedPullback (V' : S'.Opens).ι.toLRSHom.toShHom).map
      (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g'.toLRSHom.toShHom
        f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom sq K)) := by
  have : IsAffine (V : S.Opens).toScheme := V.2
  have : IsAffine (V' : S'.Opens).toScheme := V'.2
  -- the restriction of `f` over the affine open `V`, and the restriction of `g` to `V'`
  have hXV : IsPullback (f ⁻¹ᵁ (V : S.Opens)).ι (f ∣_ (V : S.Opens)) f (V : S.Opens).ι :=
    (isPullback_morphismRestrict f (V : S.Opens)).flip
  have hgV : g.resLE (V : S.Opens) (V' : S'.Opens) hle ≫ (V : S.Opens).ι =
      (V' : S'.Opens).ι ≫ g := Scheme.Hom.resLE_comp_ι g hle
  -- the fourth corner, formed once as `(f ⁻¹ᵁ V) ×_V V'`
  have hZ : IsPullback (pullback.fst (f ∣_ (V : S.Opens)) (g.resLE _ _ hle))
      (pullback.snd (f ∣_ (V : S.Opens)) (g.resLE _ _ hle)) (f ∣_ (V : S.Opens))
      (g.resLE _ _ hle) := IsPullback.of_hasPullback _ _
  have hR : IsPullback (pullback.fst (f ∣_ (V : S.Opens)) (g.resLE _ _ hle) ≫
        (f ⁻¹ᵁ (V : S.Opens)).ι) (pullback.snd (f ∣_ (V : S.Opens)) (g.resLE _ _ hle)) f
      (g.resLE (V : S.Opens) (V' : S'.Opens) hle ≫ (V : S.Opens).ι) := hZ.paste_horiz hXV
  have hw : (pullback.fst (f ∣_ (V : S.Opens)) (g.resLE _ _ hle) ≫
        (f ⁻¹ᵁ (V : S.Opens)).ι) ≫ f =
      (pullback.snd (f ∣_ (V : S.Opens)) (g.resLE _ _ hle) ≫ (V' : S'.Opens).ι) ≫ g := by
    rw [hR.w, hgV, Category.assoc]
  -- the fourth corner is also `X' ×_{S'} V'`
  have hr₁ : hsq.lift _ _ hw ≫ g' =
      pullback.fst (f ∣_ (V : S.Opens)) (g.resLE _ _ hle) ≫ (f ⁻¹ᵁ (V : S.Opens)).ι :=
    hsq.lift_fst _ _ hw
  have hr₂ : hsq.lift _ _ hw ≫ f' =
      pullback.snd (f ∣_ (V : S.Opens)) (g.resLE _ _ hle) ≫ (V' : S'.Opens).ι :=
    hsq.lift_snd _ _ hw
  have hL : IsPullback (hsq.lift _ _ hw)
      (pullback.snd (f ∣_ (V : S.Opens)) (g.resLE _ _ hle)) f' (V' : S'.Opens).ι := by
    refine IsPullback.of_right ?_ hr₂ hsq
    rw [hr₁, ← hgV]
    exact hR
  -- the rectangle over `V' ⟶ V ⟶ S` : the affine case pasted with base change along `V.ι`
  have houterV := Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_hpaste
    (pullback.fst (f ∣_ (V : S.Opens)) (g.resLE _ _ hle)).toLRSHom.toShHom
    (f ⁻¹ᵁ (V : S.Opens)).ι.toLRSHom.toShHom
    (pullback.snd (f ∣_ (V : S.Opens)) (g.resLE _ _ hle)).toLRSHom.toShHom
    (f ∣_ (V : S.Opens)).toLRSHom.toShHom f.toLRSHom.toShHom
    (g.resLE (V : S.Opens) (V' : S'.Opens) hle).toLRSHom.toShHom
    (V : S.Opens).ι.toLRSHom.toShHom (toShHom_w hXV.w) (toShHom_w hZ.w) (toShHom_w hR.w) K
    (@Functor.map_isIso _ _ _ _ _ _ _ _
      (Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersion
        (f ⁻¹ᵁ (V : S.Opens)).ι (f ∣_ (V : S.Opens)) f (V : S.Opens).ι hXV K))
    (H (pullback.fst (f ∣_ (V : S.Opens)) (g.resLE _ _ hle))
      (pullback.snd (f ∣_ (V : S.Opens)) (g.resLE _ _ hle)) (f ∣_ (V : S.Opens))
      (g.resLE (V : S.Opens) (V' : S'.Opens) hle) V.2 V'.2 hZ
      (MorphismProperty.of_isPullback (P := @QuasiCompact) hXV hqc)
      (MorphismProperty.of_isPullback (P := @QuasiSeparated) hXV hqs)
      (torIndependent_morphismRestrict_resLE f g htor hle) (toShHom_w hZ.w) _
      fun j => Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel
        (f ⁻¹ᵁ (V : S.Opens)).ι K hK j)
  -- the same rectangle read over `V' ⟶ S' ⟶ S`
  have houter := (Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_congr
    (f' := (pullback.snd (f ∣_ (V : S.Opens)) (g.resLE _ _ hle)).toLRSHom.toShHom)
    (f := f.toLRSHom.toShHom)
    (toShHom_w hr₁).symm (toShHom_w hgV) (toShHom_w hR.w)
    (Stacks.Cohomology.DerivedBaseChange.hcomp_square _ _ _ _ _ _ _ sq (toShHom_w hr₂)) K).mp
    houterV
  exact Stacks.Cohomology.DerivedBaseChange.isIso_derivedPullback_map_derivedBaseChangeMap_hpaste
    (hsq.lift _ _ hw).toLRSHom.toShHom g'.toLRSHom.toShHom
    (pullback.snd (f ∣_ (V : S.Opens)) (g.resLE _ _ hle)).toLRSHom.toShHom
    f'.toLRSHom.toShHom f.toLRSHom.toShHom (V' : S'.Opens).ι.toLRSHom.toShHom
    g.toLRSHom.toShHom sq (toShHom_w hr₂) _ K houter
    (Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_of_isOpenImmersion
      (hsq.lift _ _ hw) (pullback.snd (f ∣_ (V : S.Opens)) (g.resLE _ _ hle)) f'
      (V' : S'.Opens).ι hL _)

/-- **[Stacks, Tag 08IB] over an affine base implies [Stacks, Tag 08IB].**  Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a Cartesian square of schemes with `f` quasi-compact and quasi-separated and `X`, `S'` tor
independent over `S`.  If the derived base-change map of [Stacks, Tag 08HY] is invertible on
complexes with quasi-coherent cohomology whenever both bases are affine, then it is invertible on
such complexes for every such square.

Invertibility in `D(𝒪_{S'})` is local for the derived pullback to the members of an open cover, by
`Stacks.Cohomology.isIso_of_isIso_derivedPullback_ofRestrict`, and
`exists_affineOpens_cover_le_preimage` supplies a cover of `S'` by affine opens each of which lies
over an affine open of `S`; over such a member the statement is
`isIso_derivedPullback_map_derivedBaseChangeMap_of_affineOpens`.  This is the source's step "to
check this is an isomorphism we may work locally on `S'`", with `S` shrunk alongside `S'` so that
the affine case applies. -/
theorem derivedBaseChangeIsIsoOnQuasicoherent_of_overAffineBase
    (H : DerivedBaseChangeIsIsoOverAffineBase.{u}) :
    AlgebraicGeometry.DerivedBaseChangeIsIsoOnQuasicoherent.{u} := by
  intro X' X S' S g' f' f g hsq hqc hqs htor sq K hK
  obtain ⟨V', V, hle, hsup⟩ := exists_affineOpens_cover_le_preimage g
  refine Stacks.Cohomology.isIso_of_isIso_derivedPullback_ofRestrict
    (fun s' => ((V' s' : S'.Opens) : Opens S'.toRingedSpace.carrier)) hsup _ fun s' => ?_
  exact isIso_derivedPullback_map_derivedBaseChangeMap_of_affineOpens H hsq hqc hqs htor sq K hK
    (V s') (V' s') (hle s')

end AlgebraicGeometry

end
