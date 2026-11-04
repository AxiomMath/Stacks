module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksFrontier.CategoryTheory.Sites.CoverLifting

/-!
# F-crystals

Let `(S, I, γ)` be an affine divided power scheme whose divided power ideal contains the prime
`p`, let `σ` be a divided power endomorphism of its ring of global sections which is the `p`-th
power map modulo `p`, and let `X` be a scheme over the closed fibre `S₀ = V(I)` on which `p` is
locally nilpotent.  Taking spectra turns `σ` into an endomorphism of the divided power base which
lifts the absolute Frobenius of `S₀`, and together with the absolute Frobenius `F_X` of `X` it
induces the Frobenius endomorphism `(F_X)_cris` of the crystalline topos.  An *F-crystal* on
`X/S` relative to `σ` is a crystal `E` in finite locally free `𝒪_{X/S}`-modules together with a
map `F_E : (F_X)_cris^* E ⟶ E`.

Two things have to be put in place before that definition can be read.

First, the *crystal* condition.  A sheaf of `𝒪_{X/S}`-modules `E` assigns to every object
`(U, T, δ)` of the big crystalline site an `𝒪_T`-module `E_T`, and to every morphism
`f : (U, T, δ) ⟶ (U', T', δ')` a comparison map `c_f : f^* E_{T'} ⟶ E_T` of `𝒪_T`-modules.  The
module `E` is a crystal when every comparison map is an isomorphism: the value of `E` on an
object is then determined, as a module with descent data, by its value on any object it maps to.

Second, the pullback `(F_X)_cris^*` of sheaves of modules.  The Frobenius morphism of topoi comes
from change of divided power base, an endofunctor `u` of the big crystalline category which
leaves the underlying divided power thickening and every map between thickenings untouched and
only composes the structure maps `T ⟶ S` and `U ⟶ X` with `Spec(σ)` and with `F_X`.  Change of
base is cocontinuous, which is what produces the morphism of topoi; it is proved below to be
*continuous* as well, so its inverse image needs no sheafification and is plain restriction along
`u`.  Both the covering families and the structure sheaf of the big crystalline site are read off
the ambient divided power scheme of an object alone, and change of base does not touch that; so a
Zariski covering family maps to the same family of thickenings, again Zariski covering, and the
restriction of `𝒪_{X/S}` along `u` is `𝒪_{X/S}` itself.  The inverse image of the structure sheaf
is therefore the structure sheaf, by the identity map, and the pullback of a sheaf of modules —
which is in general the inverse image tensored over the inverse image of the structure sheaf with
the structure sheaf — is simply the restriction of the module along `u`.

Continuity itself comes from the fact that change of base is, in a precise sense, invertible on
objects lying over its image: a morphism `p : W ⟶ u(A)` of the big crystalline category of
`X/S` presents the underlying thickening of `W` as a divided power thickening over `A` already in
the big crystalline category of `X/S`, in such a way that `u` of the resulting object is `W` up to
an isomorphism which is the identity on the underlying thickening.  Hence a commuting square
over the image of a covering family can be pulled back to a commuting square over the family
itself, which is exactly what is needed to turn a compatible family of sections into a compatible
family after applying `u`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.Thickening.ofSquareLift` — the factorization, in the
  big crystalline category of `X/S`, of a morphism into the image of an object under change of
  divided power base.
* `Crystalline.GlobalCrystallineSituation.changeBaseStructureHom` — the comparison map of
  structure sheaves for change of divided power base, the identity.
* `Crystalline.GlobalCrystallineSituation.changeBaseModulePullback` — the pullback of sheaves of
  modules along change of divided power base.
* `Crystalline.GlobalCrystallineSituation.IsCrystal` — the crystal condition on a sheaf of
  `𝒪_{X/S}`-modules, read with the comparison maps of *presheaves* of modules.
* `Crystalline.GlobalCrystallineSituation.IsFiniteLocallyFreeCrystal` — that condition together
  with finite local freeness.
* `Crystalline.GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal` — a *crystal in
  finite locally free modules* on `CRIS(X/S)`, [Stacks, Tag 07IU]: the condition an F-crystal is
  built on.
* `Crystalline.FCrystalSituation.frobeniusModulePullback` — the Frobenius pullback
  `(F_X)_cris^*` of sheaves of `𝒪_{X/S}`-modules.
* `Crystalline.FCrystal` — an F-crystal on `X/S` relative to `σ`, [Stacks, Tag 07N3].
* `Crystalline.FCrystal.Nondegenerate` — nondegeneracy of an F-crystal, [Stacks, Tag 07N3].

## Main results

* `Crystalline.GlobalCrystallineSituation.Thickening.isIso_ofSquareComparison` — the comparison
  morphism identifying the image under change of base of a rebased object with that object is an
  isomorphism.
* `Crystalline.GlobalCrystallineSituation.changeBase_compatiblePreserving` — change of divided
  power base turns compatible families of sections into compatible families.
* `Crystalline.GlobalCrystallineSituation.changeBase_isContinuous` — change of divided power base
  is continuous, [Stacks, Tag 07IC].
* `Crystalline.GlobalCrystallineSituation.changeBase_op_comp_crisRing` — change of divided power
  base preserves the structure sheaf of the big crystalline site on the nose.
* `Crystalline.FCrystalSituation.crystallineFrobeniusInverseImageIso` — the inverse image of the
  Frobenius morphism of crystalline topoi is restriction along the Frobenius endofunctor of the
  big crystalline category.

## Implementation notes

The big crystalline category of a global crystalline situation over `Scheme.{u}` is a category
whose objects form a `Type (u + 1)` and whose morphisms form a `Type u`, so the crystalline topos
is one of sheaves of `Type (u + 1)`.  Sheaves of modules are taken in the module universe `u`,
the universe of the structure sheaf: the pullback along change of base is plain restriction, no
sheafification of sheaves of modules is involved, and the comparison maps of
[Stacks, Tag 07IQ] are available in that universe.

## The presheaf-level conditions here are stronger than the source's, and carry no tag

`Crystalline.GlobalCrystallineSituation.IsCrystal` states the crystal condition with the
comparison map
`Crystalline.GlobalCrystallineSituation.Thickening.moduleComparison` of the underlying *presheaf*
of modules.  That is strictly stronger than the condition of [Stacks, Tag 07IS](3), which is read
with the comparison maps of sheaves of modules: the pullback of sheaves of modules sheafifies the
pullback of presheaves of modules, and the library proves only the implication
`Crystalline.GlobalCrystallineSituation.isSheafCrystal_of_isCrystal`, the converse failing for a
countable coproduct of copies of `𝒪_{X/S}` over an ambient scheme with countably many components
— see the module documentation of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.SheafCrystal`.  `IsCrystal` therefore
carries **no** `@[stacks 07IS]` attribute.  The three conditions [Stacks, Tag 07IS] defines are
stated, for both crystalline sites, by
`Crystalline.GlobalCrystallineSituation.IsLocallyQuasiCoherent` and
`Crystalline.GlobalCrystallineSituation.SmallSite.IsLocallyQuasiCoherent` (part 1),
`SheafOfModules.IsQuasicoherentOnSite` (part 2) and
`Crystalline.GlobalCrystallineSituation.IsSheafCrystal` and
`Crystalline.GlobalCrystallineSituation.SmallSite.IsSheafCrystal` (part 3), and those carry the
attribute.

For the same reason `Crystalline.GlobalCrystallineSituation.IsFiniteLocallyFreeCrystal` carries no
`@[stacks 07IU]` attribute.  [Stacks, Tag 07IU] asks for a crystal in *quasi-coherent* modules
which is in addition finite locally free, and that predicate conjoins finite local freeness with
the presheaf-level crystal condition instead.  A finite locally free module is already
quasi-coherent — `SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite` followed
by the instance `SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite` — so it is
the source's notion together with the presheaf-level crystal condition, an extra condition the
source does not impose.  It is kept only to name that stronger condition; nothing in the library
is stated about it.

## Where the condition an F-crystal carries is defined, and why here

[Stacks, Tag 07N3] builds its F-crystal on a *crystal in finite locally free modules*, which is
the notion of [Stacks, Tag 07IU], and that is what
`Crystalline.GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal` below states:
quasi-coherence, which is condition (1) of [Stacks, Tag 07IT] and is what the source's "crystal in
quasi-coherent modules" is taken to be throughout this library, together with finite local
freeness.  The small-site form of the same condition, the second half of [Stacks, Tag 07IU], and
the consequences both forms have through the one half of [Stacks, Tag 07IT] the library proves are
in `StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.FiniteLocallyFreeCrystal`.

The big-site form is stated *here* rather than there because that file is downstream of this one:
it reaches this module through
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentImpliesLocal`,
`...CrystalsModules.QuasicoherentCriterion` and `...CrystalsModules.SheafCrystal`, the last of
which needs `Crystalline.GlobalCrystallineSituation.IsCrystal` from this file.  Stating the
predicate at the level where it is first needed — it asks for nothing beyond
`SheafOfModules.IsQuasicoherentOnSite` and `SheafOfModules.IsFiniteLocallyFreeOnSite` of
`StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite`, already imported here — lets
`Crystalline.FCrystal` carry the source's condition and leaves the rest of
[Stacks, Tag 07IU] where it was.

Nondegeneracy quantifies over `i : ℕ`, which carries the source's `i ≥ 0`, and the scalar `p ^ i`
acts on the endomorphism group of `(F_X)_cris^* E` through the `ℕ`-action of the additive group of
morphisms in a preadditive category.  The source's `V ∘ F_E` is the diagrammatic composite
`F_E ≫ V`, an endomorphism of `(F_X)_cris^* E`.

## References

* [Stacks Project, Tag 07N3](https://stacks.math.columbia.edu/tag/07N3)
* [Stacks Project, Tag 07N2](https://stacks.math.columbia.edu/tag/07N2)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IU](https://stacks.math.columbia.edu/tag/07IU)
* [Stacks Project, Tag 07IX](https://stacks.math.columbia.edu/tag/07IX)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe t u

namespace Crystalline.GlobalCrystallineSituation

variable {S S' : GlobalCrystallineSituation.{u}} {f : S.S ⟶ S'.S} {g : S.X ⟶ S'.X}
  {h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber}

namespace Thickening

/-- **The comparison morphism of a rebased object is an isomorphism.**  Both of its components
are identities, change of divided power base leaving the underlying thickening untouched. -/
theorem isIso_ofSquareComparison {A : Thickening S} {B : Thickening S'}
    (k : B ⟶ (changeBase S S' f g h).obj A) : IsIso (ofSquareComparison k) := by
  have h₁ : IsIso (ofSquareComparison k).sourceHom :=
    inferInstanceAs (IsIso (𝟙 B.thickening.source))
  have h₂ : IsIso (ofSquareComparison k).targetHom.hom :=
    inferInstanceAs (IsIso (𝟙 B.thickening.target.scheme))
  exact isIso_of_isIso_sourceHom_targetHom _

/-- **A factorization of a morphism into the image of an object under change of divided power
base, read in the big crystalline category of `X/S`.**  Let `p : B ⟶ u(A)` and let `q : B ⟶ u(Y)`
factor `p` through the image of a morphism `k : Y ⟶ A`.  The underlying thickening of `B`, read as
a divided power thickening over `A` by `p`, is then a divided power thickening over `Y` by the
components of `q`: being over the divided power base and over `X` for `Y` follows from the same
conditions for `k` and the factorization. -/
noncomputable def ofSquareLift {A Y : Thickening S} (k : Y ⟶ A) {B : Thickening S'}
    (p : B ⟶ (changeBase S S' f g h).obj A) (q : B ⟶ (changeBase S S' f g h).obj Y)
    (hq : q ≫ (changeBase S S' f g h).map k = p) :
    ofSquare A B.thickening p.targetHom p.sourceHom p.immersion_naturality ⟶ Y where
  sourceHom := q.sourceHom
  targetHom := q.targetHom
  immersion_naturality := q.immersion_naturality
  base_naturality :=
    (congrArg (fun z ↦ q.targetHom ≫ z) k.base_naturality.symm).trans
      ((Category.assoc q.targetHom k.targetHom A.toBase).symm.trans
        (congrArg (fun z ↦ z ≫ A.toBase)
          (congrArg (fun m : B ⟶ (changeBase S S' f g h).obj A ↦ m.targetHom) hq)))
  toX_naturality :=
    (congrArg (fun z ↦ q.sourceHom ≫ z) k.toX_naturality.symm).trans
      ((Category.assoc q.sourceHom k.sourceHom A.toX).symm.trans
        (congrArg (fun z ↦ z ≫ A.toX)
          (congrArg (fun m : B ⟶ (changeBase S S' f g h).obj A ↦ m.sourceHom) hq)))

/-- **The image of the factorization is the original morphism**, up to the comparison isomorphism
of the underlying thickenings. -/
theorem changeBase_map_ofSquareLift {A Y : Thickening S} (k : Y ⟶ A) {B : Thickening S'}
    (p : B ⟶ (changeBase S S' f g h).obj A) (q : B ⟶ (changeBase S S' f g h).obj Y)
    (hq : q ≫ (changeBase S S' f g h).map k = p) :
    (changeBase S S' f g h).map (ofSquareLift k p q hq) = ofSquareComparison p ≫ q := by
  refine Hom.ext ?_ ?_ <;> exact (Category.id_comp _).symm

/-- **The factorization composed with the morphism it factors through is the structure morphism of
the rebased object**, so in particular it does not depend on the factorization. -/
theorem ofSquareLift_comp {A Y : Thickening S} (k : Y ⟶ A) {B : Thickening S'}
    (p : B ⟶ (changeBase S S' f g h).obj A) (q : B ⟶ (changeBase S S' f g h).obj Y)
    (hq : q ≫ (changeBase S S' f g h).map k = p) :
    ofSquareLift k p q hq ≫ k =
      ofSquareHom A B.thickening p.targetHom p.sourceHom p.immersion_naturality :=
  Hom.ext (congrArg (fun m : B ⟶ (changeBase S S' f g h).obj A ↦ m.sourceHom) hq)
    (congrArg (fun m : B ⟶ (changeBase S S' f g h).obj A ↦ m.targetHom) hq)

/-- **Sections of a presheaf which agree over the big crystalline category of `X/S` agree over
the images of the two morphisms of a commuting square of the big crystalline category of
`Y/S'`.**  The square is defined over the image of an object `A`; rebasing its vertex along the
diagonal `B ⟶ u(A)` and lifting the two morphisms produces a commuting square over `A` itself,
to which the hypothesis applies, and the comparison morphism of the rebased vertex is an
isomorphism, so it may be cancelled. -/
theorem map_eq_of_changeBase_comm {P : (Thickening S')ᵒᵖ ⥤ Type t} {A Y₁ Y₂ : Thickening S}
    (k₁ : Y₁ ⟶ A) (k₂ : Y₂ ⟶ A) {B : Thickening S'}
    (q₁ : B ⟶ (changeBase S S' f g h).obj Y₁) (q₂ : B ⟶ (changeBase S S' f g h).obj Y₂)
    (hq : q₁ ≫ (changeBase S S' f g h).map k₁ = q₂ ≫ (changeBase S S' f g h).map k₂)
    {y₁ : P.obj (op ((changeBase S S' f g h).obj Y₁))}
    {y₂ : P.obj (op ((changeBase S S' f g h).obj Y₂))}
    (hy : ∀ (Z : Thickening S) (m₁ : Z ⟶ Y₁) (m₂ : Z ⟶ Y₂), m₁ ≫ k₁ = m₂ ≫ k₂ →
      P.map ((changeBase S S' f g h).map m₁).op y₁ =
        P.map ((changeBase S S' f g h).map m₂).op y₂) :
    P.map q₁.op y₁ = P.map q₂.op y₂ := by
  obtain ⟨p, hp⟩ : ∃ p, q₁ ≫ (changeBase S S' f g h).map k₁ = p := ⟨_, rfl⟩
  have hp' : q₂ ≫ (changeBase S S' f g h).map k₂ = p := hq.symm.trans hp
  have hc : IsIso (ofSquareComparison p) := isIso_ofSquareComparison p
  have key := hy _ (ofSquareLift k₁ p q₁ hp) (ofSquareLift k₂ p q₂ hp')
    ((ofSquareLift_comp k₁ p q₁ hp).trans (ofSquareLift_comp k₂ p q₂ hp').symm)
  rw [changeBase_map_ofSquareLift, changeBase_map_ofSquareLift] at key
  have hgoal : P.map (ofSquareComparison p).op (P.map q₁.op y₁) =
      P.map (ofSquareComparison p).op (P.map q₂.op y₂) := by
    simpa only [op_comp, Functor.map_comp, types_comp_apply] using key
  exact (P.mapIso (asIso (ofSquareComparison p)).op).toEquiv.injective hgoal

end Thickening

open Thickening

/-- **Change of divided power base turns compatible families of sections into compatible
families.**  A commuting square over the image of an object rebases to a commuting square over
that object, and the comparison morphism of the rebased vertex is an isomorphism. -/
theorem changeBase_compatiblePreserving :
    CompatiblePreserving.{t} (topology S') (changeBase S S' f g h) where
  compatible := by
    intro P Z T x hx Y₁ Y₂ W q₁ q₂ k₁ k₂ hk₁ hk₂ hq
    exact map_eq_of_changeBase_comm k₁ k₂ q₁ q₂ hq fun _ m₁ m₂ hm ↦ hx m₁ m₂ hk₁ hk₂ hm

/-- **Stacks Project, Tag 07IC.**  Change of divided power base is continuous for the big
crystalline Zariski topologies.  It suffices to check the Zariski covering families; such a
family maps to the family of the same thickenings over the image of the base, which is again
Zariski covering because being Cartesian and covering the ambient scheme do not involve the
structure maps to the divided power base and to `X`.  The sheaf condition then transfers because
change of base turns compatible families into compatible families. -/
@[stacks 07IC "continuity"]
instance changeBase_isContinuous :
    (changeBase S S' f g h).IsContinuous (topology S) (topology S') where
  op_comp_isSheaf_of_types G := by
    rw [topology_eq_coverage_toGrothendieck, Presieve.isSheaf_coverage]
    rintro B R ⟨E, rfl, hE⟩
    have hEF : IsZariskiCovering (E.map (changeBase S S' f g h)) := ⟨hE.1, hE.2⟩
    have hsheaf : Presieve.IsSheafFor G.obj
        ((E.map (changeBase S S' f g h)).presieve₀ :
          Presieve ((changeBase S S' f g h).obj B)) :=
      (Presieve.isSheafFor_iff_generate _).2
        ((isSheaf_iff_isSheaf_of_type _ _).1 G.property _
          (zariskiCovering_mem_topology S' (E.map (changeBase S S' f g h)) hEF))
    have hpreF : ((E.map (changeBase S S' f g h)).presieve₀ :
          Presieve ((changeBase S S' f g h).obj B)) =
        Presieve.ofArrows (fun i ↦ (changeBase S S' f g h).obj (E.X i))
          (fun i ↦ (changeBase S S' f g h).map (E.f i)) := rfl
    have hpre : ((E.presieve₀ : Presieve B)) = Presieve.ofArrows E.X E.f := rfl
    rw [hpreF, Presieve.isSheafFor_arrows_iff] at hsheaf
    rw [hpre, Presieve.isSheafFor_arrows_iff]
    intro x hx
    exact hsheaf x fun i j W q₁ q₂ hq ↦
      map_eq_of_changeBase_comm (E.f i) (E.f j) q₁ q₂ hq fun Z m₁ m₂ hm ↦ hx i j Z m₁ m₂ hm

/-- **Change of divided power base preserves the structure presheaf of the big crystalline
site.**  The structure presheaf sends an object to the ring of global sections of its ambient
divided power scheme and a morphism to the induced map, and change of base changes neither. -/
theorem changeBase_op_comp_crisRing :
    (changeBase S S' f g h).op ⋙ crisRing S' = crisRing S := rfl

/-- **The comparison map of structure sheaves for change of divided power base.**  The
restriction of `𝒪_{Y/S'}` along change of base is `𝒪_{X/S}`, so the comparison map is the
identity. -/
def changeBaseStructureHom (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    crystallineStructureSheaf S ⟶
      ((changeBase S S' f g h).sheafPushforwardContinuous RingCat.{u} (topology S)
        (topology S')).obj (crystallineStructureSheaf S') :=
  ⟨𝟙 _⟩

/-- **The pullback of sheaves of modules along change of divided power base.**  Change of base is
continuous, so the inverse image of the induced morphism of topoi is restriction along it; and
the comparison map of structure sheaves is the identity, so no tensor product is needed and the
pullback of a sheaf of `𝒪_{Y/S'}`-modules is its restriction, a sheaf of `𝒪_{X/S}`-modules whose
sections over `(U, T, δ)` are the sections of the original module over the image of
`(U, T, δ)`. -/
noncomputable def changeBaseModulePullback (S S' : GlobalCrystallineSituation.{u})
    (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    SheafOfModules.{u} (crystallineStructureSheaf S') ⥤
      SheafOfModules.{u} (crystallineStructureSheaf S) :=
  SheafOfModules.pushforward (changeBaseStructureHom S S' f g h)

/-- **The crystal condition read with the comparison maps of presheaves of modules.**  A sheaf of
`𝒪_{X/S}`-modules on the big crystalline site satisfies it when for every morphism
`f : (U, T, δ) ⟶ (U', T', δ')` of the site the comparison map `c_f : f^* E_{T'} ⟶ E_T` of
*presheaves* of `𝒪_T`-modules is an isomorphism.

This is **not** part (3) of [Stacks, Tag 07IS], which reads the comparison maps at sheaf level and
is strictly weaker; that condition is
`Crystalline.GlobalCrystallineSituation.IsSheafCrystal`, and
`Crystalline.GlobalCrystallineSituation.isSheafCrystal_of_isCrystal` is the one implication
between the two that holds.  See the module documentation. -/
def IsCrystal {S : GlobalCrystallineSituation.{u}}
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) : Prop :=
  ∀ (A B : Thickening S) (k : A ⟶ B),
    IsIso (Thickening.moduleComparison (M.val : PresheafOfModules.{u} (crisRing S)) k)

/-- **The presheaf-level crystal condition together with finite local freeness**: a sheaf of
`𝒪_{X/S}`-modules on the big crystalline site all of whose comparison maps of presheaves of
modules are isomorphisms and which is finite locally free, that is, every object of the site has a
covering family on whose members the restricted module is a finite direct sum of copies of the
structure sheaf.

This is **not** the *crystal in finite locally free modules* of [Stacks, Tag 07IU], which asks
instead for a crystal in quasi-coherent modules that is finite locally free; that notion is
`Crystalline.GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal` below, and it is
the one `Crystalline.FCrystal` carries.  The condition here implies that one, finite local freeness
already giving quasi-coherence, and is not implied by it; neither implication is assembled in Lean.
See the module documentation. -/
structure IsFiniteLocallyFreeCrystal {S : GlobalCrystallineSituation.{u}}
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) : Prop where
  /-- All comparison maps are isomorphisms. -/
  isCrystal : IsCrystal M
  /-- The module is finite locally free. -/
  isFiniteLocallyFree : SheafOfModules.IsFiniteLocallyFreeOnSite M

/-- **Stacks Project, Tag 07IU.**  A *crystal in finite locally free modules* on the big
crystalline site: a sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)` which is a crystal in quasi-coherent
modules — that is, quasi-coherent, condition (1) of [Stacks, Tag 07IT] — and is finite locally
free, every object of the site having a covering on whose members the restricted module is a
finite free module over the restricted structure sheaf.

This is the condition [Stacks, Tag 07N3] builds its F-crystal on, so it is stated here, upstream
of `Crystalline.FCrystal`; the small-site form of the same condition and what either form gives
through [Stacks, Tag 07IT] are in
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.FiniteLocallyFreeCrystal`. -/
@[stacks 07IU "crystals in finite locally free modules on the big site CRIS(X/S), with the crystal
  in quasi-coherent modules taken as condition (1) of Stacks 07IT"]
structure IsFiniteLocallyFreeQuasicoherentCrystal {S : GlobalCrystallineSituation.{u}}
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) : Prop where
  /-- The module is quasi-coherent, which is what it is for it to be a crystal in quasi-coherent
  modules. -/
  isQuasicoherentOnSite : M.IsQuasicoherentOnSite
  /-- The module is finite locally free. -/
  isFiniteLocallyFree : SheafOfModules.IsFiniteLocallyFreeOnSite M

end Crystalline.GlobalCrystallineSituation

namespace Crystalline.FCrystalSituation

open GlobalCrystallineSituation

variable (T : FCrystalSituation.{u})

/-- The Frobenius endofunctor of the big crystalline category is cocontinuous. -/
instance frobeniusChangeBase_isCocontinuous :
    (frobeniusChangeBase T).IsCocontinuous (topology T.global) (topology T.global) :=
  changeBase_isCocontinuous

/-- The Frobenius endofunctor of the big crystalline category is continuous. -/
instance frobeniusChangeBase_isContinuous :
    (frobeniusChangeBase T).IsContinuous (topology T.global) (topology T.global) :=
  changeBase_isContinuous

/-- **The inverse image of the Frobenius morphism of crystalline topoi is restriction along the
Frobenius endofunctor of the big crystalline category.**  The Frobenius endofunctor is both
cocontinuous and continuous, so the sheafification in the inverse image of the induced morphism
of topoi is unnecessary.  This is what identifies `(F_X)_cris^{-1}` with plain restriction, and
hence `(F_X)_cris^*` on modules with
`Crystalline.FCrystalSituation.frobeniusModulePullback`. -/
noncomputable def crystallineFrobeniusInverseImageIso :
    (crystallineFrobenius T).inverseImage ≅
      (frobeniusChangeBase T).sheafPushforwardContinuous (Type (u + 1))
        (topology T.global) (topology T.global) :=
  (frobeniusChangeBase T).sheafPullbackCocontinuousIsoSheafPushforwardContinuous
    (Type (u + 1)) (topology T.global) (topology T.global)

/-- **The Frobenius pullback `(F_X)_cris^*` of sheaves of `𝒪_{X/S}`-modules.**  It is the pullback
of sheaves of modules along the Frobenius endofunctor of the big crystalline category, that is,
the restriction of a sheaf of modules along that endofunctor: the sections of `(F_X)_cris^* E`
over `(U, T, δ)` are the sections of `E` over `(U, T, δ)` with its structure maps composed with
`Spec(σ)` and with the absolute Frobenius of `X`. -/
noncomputable def frobeniusModulePullback :
    SheafOfModules.{u} (crystallineStructureSheaf T.global) ⥤
      SheafOfModules.{u} (crystallineStructureSheaf T.global) :=
  changeBaseModulePullback T.global T.global T.specSigma T.frobenius
    T.toClosedFiber_comp_closedFiberMap_specSigma

end Crystalline.FCrystalSituation

namespace Crystalline

open GlobalCrystallineSituation

/-- **Stacks Project, Tag 07N3.**  An *F-crystal on `X/S` relative to `σ`*: a crystal in finite
locally free `𝒪_{X/S}`-modules `E` together with a map `F_E : (F_X)_cris^* E ⟶ E`.

The crystal in finite locally free modules is the notion of [Stacks, Tag 07IU],
`Crystalline.GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal`: quasi-coherence
— condition (1) of [Stacks, Tag 07IT], the form in which this library reads the source's "crystal
in quasi-coherent modules" — together with finite local freeness.  It is **not** the stronger
`Crystalline.GlobalCrystallineSituation.IsFiniteLocallyFreeCrystal`, which reads the crystal
condition with the comparison maps of presheaves of modules; see the module documentation. -/
@[stacks 07N3 "F-crystal"]
structure FCrystal (T : FCrystalSituation.{u}) where
  /-- The underlying sheaf of `𝒪_{X/S}`-modules `E`. -/
  crystal : SheafOfModules.{u} (crystallineStructureSheaf T.global)
  /-- It is a crystal in finite locally free modules, [Stacks, Tag 07IU]. -/
  isFiniteLocallyFreeQuasicoherentCrystal : IsFiniteLocallyFreeQuasicoherentCrystal crystal
  /-- The Frobenius structure `F_E : (F_X)_cris^* E ⟶ E`. -/
  frobenius : T.frobeniusModulePullback.obj crystal ⟶ crystal

/-- **Stacks Project, Tag 07N3.**  An F-crystal is *nondegenerate* when there are an integer
`i ≥ 0` and a map `V : E ⟶ (F_X)_cris^* E` with `V ∘ F_E = p ^ i`, the composite being taken
diagrammatically as `F_E ≫ V`, an endomorphism of `(F_X)_cris^* E`, and the scalar `p ^ i` acting
through the `ℕ`-action on morphisms. -/
@[stacks 07N3 "nondegenerate"]
def FCrystal.Nondegenerate {T : FCrystalSituation.{u}} (E : FCrystal T) : Prop :=
  ∃ (i : ℕ) (V : E.crystal ⟶ T.frobeniusModulePullback.obj E.crystal),
    E.frobenius ≫ V = (T.global.p ^ i) • 𝟙 (T.frobeniusModulePullback.obj E.crystal)

end Crystalline

end
