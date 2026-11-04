module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeTwist
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SubbundleTwist
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Bundle
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Scheme
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.ChernClassesOfRank
import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank
import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.PullbackStable
import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
import StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Tautological
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Clause (3)(a) of Stacks Section 45.12, and the tautological sequence it carries

Clause (3)(a) of the standing situation of Stacks Section 45.12 (Tag 0FI4) reads: for `X` in `𝒞`
and `ℰ` a finite locally free `𝒪_X`-module, the projection `p : 𝐏(ℰ) ⟶ X` is a morphism of `𝒞`.
It is a **closure property** of the category `𝒞`: the scheme `𝐏(ℰ)`, its projection, its twist
`𝒪_{𝐏(ℰ)}(1)` and its tautological sequence are all *constructed* — `Stacks.Chow.bundle` and the
declarations around it — and what the clause adds is only that the result of that construction
lies in `𝒞`.

`Stacks.WeilCohomology.BundleObject` is that clause, and nothing more: an object of `𝒞` whose
scheme is identified with `Stacks.Chow.bundle ℰ` and a morphism of `𝒞` which is the projection
read through that identification. Everything else about the projective bundle is then **derived**:
the pieces are built here, and `Stacks.WeilCohomology.BundleObject.toBundleDatum` assembles them
into a `Stacks.WeilCohomology.BundleDatum` in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.Situation`, where that structure is
defined.

## Main definitions

* `Stacks.WeilCohomology.IsBundleObject`: the identification of the scheme of an object of `𝒞`
  with `𝐏(ℰ)`, under which a given morphism of `𝒞` is the projection.
* `Stacks.WeilCohomology.BundleObject`: **clause (3)(a)** — an object of `𝒞` identified with
  `𝐏(ℰ)` together with its projection as a morphism of `𝒞`.
* `Stacks.WeilCohomology.BundleObject.twist`, `quot`, `flat_map_proj` and
  `isFiniteLocallyFreeOfRank_kernel_quot`: the twist, the tautological surjection, the flatness of
  the projection and the rank of the kernel, each **derived** from clause (3)(a). These are the
  pieces `Stacks.WeilCohomology.BundleObject.toBundleDatum` assembles.

## What is derived, and from what

`Stacks.WeilCohomology.BundleObject.toBundleDatum` takes the four data of `BundleObject` — an
object `b` of `𝒞`, a morphism `p : b ⟶ X` of `𝒞`, an isomorphism `e : S(b) ≅ 𝐏(ℰ)` and the
identity `e ≫ π = S(p)` — and produces every remaining field of
`Stacks.WeilCohomology.BundleDatum`:

* the **twist** is `e^*𝒪_{𝐏(ℰ)}(1)`, invertible by `Stacks.Modules.isInvertible_pullback` read
  through `Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`, which
  exchanges the two Tag 01CS spellings of invertibility;
* the **tautological surjection** is `Stacks.ProjectiveBundleSplitting.tautologicalMap` pulled
  back along `e`, read through the comparison
  `S(p)^*ℰ ≅ e^*π^*ℰ` that `AlgebraicGeometry.Scheme.Modules.pullbackComp` and
  `AlgebraicGeometry.Scheme.Modules.pullbackCongr` assemble out of `e ≫ π = S(p)`. It is an
  epimorphism by `Stacks.ProjectiveBundleSplitting.epi_tautologicalMap` together with
  `Stacks.ProjectiveBundleSplitting.shortExact_map_pullback_of_epi_isInvertible`, which is
  pullback stability of the kernel sequence of an invertible quotient along an *arbitrary*
  morphism and so needs no flatness of `e`;
* the **kernel** is the categorical kernel of that surjection, so the sequence is short exact by
  `CategoryTheory.ShortComplex.exact_kernel` with nothing to transport;
* the **rank of the kernel** is `r` by
  `Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred`,
  whose source rank is `n + 1` for an arbitrary `n` — in particular `r = 0` is covered, which is
  the case `ℰ` invertible, where `𝒪_{𝐏(ℰ)}(1)` is the pullback of `ℰ` and the kernel vanishes.
  That case is reached: the total Chern class of a single invertible module is read there;
* **flatness of the projection** is `Stacks.Chow.flat_bundleProj_ofRank` — which holds for a
  module of *any* constant rank, the rank-zero bundle being empty — composed with the flatness of
  the isomorphism `e`.

So the only thing `BundleObject` asserts is the closure property clause (3)(a) states.

## References

* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 02N4](https://stacks.math.columbia.edu/tag/02N4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v₁ w

namespace Stacks.WeilCohomology

/-! ### Clause (3)(a) -/

/-- **The identification of an object of `𝒞` with the projective bundle `𝐏(ℰ)`**: the constant
rank `r + 1` of `ℰ`, an isomorphism of the scheme of the object with the constructed
`Stacks.Chow.bundle ℰ`, and the requirement that the given morphism of `𝒞` is the projection of
the bundle read through it.

The rank is a field rather than a parameter so that
`Stacks.WeilCohomology.BundleObject` is indexed by `ℰ` and `r` alone, exactly as
`Stacks.WeilCohomology.BundleDatum` is. With the finite local freeness carried as a parameter
instead, every projection out of a variable of that structure drags the parameter along, and
instance search inside the standing situation of Section 45.12 — which forms `Pic` of the scheme
of the bundle — unfolds `Stacks.Chow.bundle` through the symmetric algebra to a relative `Proj`
and does not terminate. -/
structure IsBundleObject {C : Type w} [Category.{v₁} C] (S : C ⥤ Scheme.{u}) (X : C)
    (E : (S.obj X).Modules) (r : ℕ) (b : C) (p : b ⟶ X) where
  /-- `ℰ` is finite locally free of rank `r + 1`. -/
  rank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)
  /-- The scheme of the object of `𝒞` is `𝐏(ℰ)`. -/
  iso : S.obj b ≅ @Stacks.Chow.bundle (S.obj X) E
    (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
      (hM := rank))
  /-- The morphism of `𝒞` is the projection of the bundle, read through that identification. -/
  iso_hom_comp_bundleProj :
    iso.hom ≫ @Stacks.Chow.bundleProj (S.obj X) E
        (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
          (hM := rank)) =
      S.map p

/-- **Clause (3)(a) of the source's category: the projection of a projective bundle is a morphism
of `𝒞`.** For an object `X` of `𝒞` and an `ℰ` of constant rank `r + 1` on it, this is an object of
`𝒞` whose scheme is `𝐏(ℰ)` — the constructed `Stacks.Chow.bundle ℰ` — together with the
projection as a morphism of `𝒞`.

Because `𝒞` is presented as an indexing functor `S : 𝒞 ⥤ Scheme` rather than as a subcategory of
schemes, "whose scheme is `𝐏(ℰ)`" is an isomorphism `S(b) ≅ 𝐏(ℰ)` and not an equality, exactly as
for `Stacks.WeilCohomology.ClopenSubobject`; and `proj` is required to be the projection of the
bundle read through it.

This is the **whole** of what the source assumes about `𝐏(ℰ)`: the twist, the tautological
sequence, the rank of its kernel and the flatness of the projection are all consequences, and are
derived in `Stacks.WeilCohomology.BundleObject.toBundleDatum`. -/
structure BundleObject {C : Type w} [Category.{v₁} C] (S : C ⥤ Scheme.{u}) (X : C)
    (E : (S.obj X).Modules) (r : ℕ) where
  /-- The projective bundle, as an object of `𝒞`. -/
  bundle : C
  /-- Its projection `𝐏(ℰ) ⟶ X`, a morphism of `𝒞`. -/
  proj : bundle ⟶ X
  /-- Its scheme is `𝐏(ℰ)` and `proj` is the projection of the bundle. -/
  isBundle : IsBundleObject S X E r bundle proj

namespace BundleObject

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}} {X : C}
  {E : (S.obj X).Modules} {r : ℕ}

/-- `ℰ` is finite locally free. -/
theorem isFiniteLocallyFree (B : BundleObject S X E r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
    (hM := B.isBundle.rank)

/-- `ℰ` is finite locally free of rank `r + 1`. -/
theorem rank (B : BundleObject S X E r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1) :=
  B.isBundle.rank

/-- The identification of the scheme of the object of `𝒞` with `𝐏(ℰ)`. -/
def iso (B : BundleObject S X E r) :
    S.obj B.bundle ≅ @Stacks.Chow.bundle (S.obj X) E B.isFiniteLocallyFree :=
  B.isBundle.iso

/-- The morphism of `𝒞` is the projection of the bundle. -/
theorem iso_hom_comp_bundleProj (B : BundleObject S X E r) :
    B.iso.hom ≫ @Stacks.Chow.bundleProj (S.obj X) E B.isFiniteLocallyFree = S.map B.proj :=
  B.isBundle.iso_hom_comp_bundleProj

/-- **The tautological invertible module `𝒪_{𝐏(ℰ)}(1)` on the object of `𝒞`**, which is
`Stacks.Chow.bundleTwist` read through the identification of that object with `𝐏(ℰ)`. -/
def twist (B : BundleObject S X E r) : (S.obj B.bundle).Modules :=
  (Scheme.Modules.pullback B.iso.hom).obj
    (@Stacks.Chow.bundleTwist (S.obj X) E B.isFiniteLocallyFree)

/-- The twist is invertible: `Stacks.Chow.isInvertible_bundleTwist` and the invertibility of a
pullback. -/
theorem twist_isInvertible (B : BundleObject S X E r) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj B.bundle).presheaf
      (S.obj B.bundle).ringCatSheaf.2 B.twist :=
  have := B.isFiniteLocallyFree
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp
    (@Stacks.Modules.isInvertible_pullback _ _ B.iso.hom _
      ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
        _ _ _).mpr (Stacks.Chow.isInvertible_bundleTwist E)))

/-- The twist, written out. This is how it is *defined*; the equation is recorded because
`twist` is sealed below, and the derivations of clauses (3)(b) and (3)(c) need to see through
it. -/
theorem twist_eq (B : BundleObject S X E r) :
    B.twist = (Scheme.Modules.pullback B.iso.hom).obj
      (@Stacks.Chow.bundleTwist (S.obj X) E B.isFiniteLocallyFree) := rfl

/-- **The comparison `S(p)^*ℳ ≅ e^*π^*ℳ`** that `e ≫ π = S(p)` induces, for any module `ℳ` on the
base: pullback is a
pseudofunctor, so `e^*π^*` is `(e ≫ π)^*` up to
`AlgebraicGeometry.Scheme.Modules.pullbackComp`, and
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` rewrites `e ≫ π` to `S(p)`. -/
def pullObjIso (B : BundleObject S X E r) (M : (S.obj X).Modules) :
    (Scheme.Modules.pullback (S.map B.proj)).obj M ≅
      (Scheme.Modules.pullback B.iso.hom).obj
        ((Scheme.Modules.pullback
          (@Stacks.Chow.bundleProj (S.obj X) E B.isFiniteLocallyFree)).obj M) :=
  ((Scheme.Modules.pullbackComp B.iso.hom
      (@Stacks.Chow.bundleProj (S.obj X) E B.isFiniteLocallyFree) ≪≫
    Scheme.Modules.pullbackCongr B.iso_hom_comp_bundleProj).app M).symm

/-- **The tautological surjection `S(p)^*ℰ ⟶ 𝒪_{𝐏(ℰ)}(1)` on the object of `𝒞`**:
`Stacks.ProjectiveBundleSplitting.tautologicalMap` pulled back along the identification, read
through `Stacks.WeilCohomology.BundleObject.pullObjIso`. -/
def quot (B : BundleObject S X E r) :
    (Scheme.Modules.pullback (S.map B.proj)).obj E ⟶ B.twist :=
  haveI := B.isFiniteLocallyFree
  (B.pullObjIso E).hom ≫ (Scheme.Modules.pullback B.iso.hom).map
    (Stacks.ProjectiveBundleSplitting.tautologicalMap E (Stacks.Chow.bundlePieces E))

/-- **The tautological surjection is an epimorphism.** It is one on `𝐏(ℰ)` by
`Stacks.ProjectiveBundleSplitting.epi_tautologicalMap`, and it stays one after pullback along the
identification by
`Stacks.ProjectiveBundleSplitting.shortExact_map_pullback_of_epi_isInvertible`, which is pullback
stability of the kernel sequence of an invertible quotient along an *arbitrary* morphism — so no
flatness of the identification is used, only that it is a morphism. -/
@[ega "II 4.1.6" "special case",
  sga "5 VII 8.4.1" "partial",
  sga "6 VI 1.9" "(E)",
  sga "6 VI 5.1" "partial"]
theorem epi_quot (B : BundleObject S X E r) : Epi B.quot := by
  have := B.isFiniteLocallyFree
  have : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  have hepi : Epi (Stacks.ProjectiveBundleSplitting.tautologicalMap E
      (Stacks.Chow.bundlePieces E)) :=
    Stacks.ProjectiveBundleSplitting.epi_tautologicalMap E (Stacks.Chow.bundlePieces E)
  have hmap : Epi ((Scheme.Modules.pullback B.iso.hom).map
      (Stacks.ProjectiveBundleSplitting.tautologicalMap E (Stacks.Chow.bundlePieces E))) :=
    (Stacks.ProjectiveBundleSplitting.shortExact_map_pullback_of_epi_isInvertible B.iso.hom
      (Stacks.ProjectiveBundleSplitting.tautologicalMap E (Stacks.Chow.bundlePieces E)) hepi
      (Stacks.Chow.isInvertible_bundleTwist E)).epi_g
  have hcomp : Epi ((B.pullObjIso E).hom ≫ (Scheme.Modules.pullback B.iso.hom).map
      (Stacks.ProjectiveBundleSplitting.tautologicalMap E (Stacks.Chow.bundlePieces E))) :=
    @epi_comp _ _ _ _ _ _ inferInstance _ hmap
  exact hcomp

/-- **The projection is flat.** `Stacks.Chow.flat_bundleProj_ofRank` is flatness of the
projection of the projective bundle of a module of *any* constant rank; the morphism of `𝒞` is
that projection precomposed with an isomorphism. -/
theorem flat_map_proj (B : BundleObject S X E r) : Flat (S.map B.proj) := by
  have := B.isFiniteLocallyFree
  have := B.rank
  have : Flat (@Stacks.Chow.bundleProj (S.obj X) E B.isFiniteLocallyFree) :=
    Stacks.Chow.flat_bundleProj_ofRank E (r + 1)
  rw [← B.iso_hom_comp_bundleProj]
  infer_instance

/-- **The kernel of the tautological surjection is finite locally free of rank `r`.** It is taken
to be the *categorical* kernel, so nothing has to be transported along the identification of the
object of `𝒞` with `𝐏(ℰ)`. The rank is
`Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred`,
which reads the rank of `S(p)^*ℰ` off `AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback` and
covers `r = 0`. -/
theorem isFiniteLocallyFreeOfRank_kernel_quot (B : BundleObject S X E r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (kernel B.quot) r :=
  have := B.isFiniteLocallyFree
  have := B.rank
  Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred
    B.quot B.epi_quot B.twist_isInvertible r
    (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (S.map B.proj) E (r + 1))

end BundleObject

/-! ### Clause (3)(b) -/

/-- **Clause (3)(b) of the source's category: for `f : X' ⟶ X` in `𝒞`, the induced morphism
`𝐏(f^*ℰ) ⟶ 𝐏(ℰ)` is a morphism of `𝒞`.**

This is a *closure* property, like clause (3)(a), and that is all it says. The induced morphism of
schemes is the constructed `Stacks.Chow.bundleBaseChangeHom`; `map_eq` requires the morphism of
`𝒞` to be it, read through the two identifications of clause (3)(a). `comp_proj` is "over `f`",
which the source has for free — its `𝒞` is a subcategory of schemes, so a morphism of `𝒞` is
determined by its morphism of schemes — but which has to be said when `𝒞` is presented by an
indexing functor `S`, exactly as for `Stacks.WeilCohomology.ClopenSubobject`.

What the source's clause does **not** say, and what used to be assumed alongside it, is that this
morphism carries `c₁^A(𝒪_{𝐏(ℰ)}(1))` to `c₁^A(𝒪_{𝐏(f^*ℰ)}(1))`. That is a consequence:
`Stacks.WeilCohomology.BundleObject.nonempty_pullback_twist_of_isBundleCompare` produces the
isomorphism `(S g)^*𝒪_{𝐏(ℰ)}(1) ≅ 𝒪_{𝐏(f^*ℰ)}(1)` from the base change of the twist, and
condition (3) then gives the equation of first Chern classes. -/
structure IsBundleCompare {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}} {X X' : C}
    (f : X' ⟶ X) {E : (S.obj X).Modules} {E' : (S.obj X').Modules} {r : ℕ}
    (B : BundleObject S X E r) (B' : BundleObject S X' E' r)
    (e : (Scheme.Modules.pullback (S.map f)).obj E ≅ E')
    (g : B'.bundle ⟶ B.bundle) : Prop where
  /-- The morphism of `𝒞` lies over `f`. -/
  comp_proj : g ≫ B.proj = B'.proj ≫ f
  /-- Its morphism of schemes is the base-change morphism `𝐏(f^*ℰ) ⟶ 𝐏(ℰ)`, read through the
  identifications of clause (3)(a). -/
  map_eq : S.map g ≫ B.iso.hom =
    B'.iso.hom ≫ @Stacks.Chow.bundleBaseChangeHom (S.obj X) (S.obj X') (S.map f) E
      B.isFiniteLocallyFree E' B'.isFiniteLocallyFree e.symm

namespace BundleObject

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}} {X X' : C}
  {E : (S.obj X).Modules} {E' : (S.obj X').Modules} {r : ℕ}

/-- **The base change of the twist at the base-change morphism**:
`Stacks.Chow.bundleBaseChange` produces the comparison at
`(bundleBaseChangeIso).hom ≫ pullback.snd`, and `Stacks.Chow.bundleBaseChangeIso_hom_snd` says
that morphism is `Stacks.Chow.bundleBaseChangeHom`. -/
theorem nonempty_pullback_bundleTwist_bundleBaseChangeHom (f : X' ⟶ X)
    (B : BundleObject S X E r) (B' : BundleObject S X' E' r)
    (e : (Scheme.Modules.pullback (S.map f)).obj E ≅ E') :
    haveI := B.isFiniteLocallyFree
    haveI := B'.isFiniteLocallyFree
    Nonempty ((Scheme.Modules.pullback
        (Stacks.Chow.bundleBaseChangeHom (S.map f) E E' e.symm)).obj
          (Stacks.Chow.bundleTwist E) ≅ Stacks.Chow.bundleTwist E') :=
  have := B.isFiniteLocallyFree
  have := B'.isFiniteLocallyFree
  ⟨((Scheme.Modules.pullbackCongr
      (Stacks.Chow.bundleBaseChangeIso_hom_snd (S.map f) E E' e.symm)).app
        (Stacks.Chow.bundleTwist E)).symm ≪≫
    (Stacks.Chow.bundleBaseChange (S.map f) E E' e.symm).twistIso⟩

/-- A twist pulls back along `g` to the next one, if `g` is `q` read through the identifications
and `q` pulls the twist of `𝐏(ℰ)` back to the twist of `𝐏(ℰ')`. -/
private theorem nonempty_pullback_twist_of_map_eq {X X' : C} {E : (S.obj X).Modules}
    {E' : (S.obj X').Modules} {r r' : ℕ} (B : BundleObject S X E r) (B' : BundleObject S X' E' r')
    (g : B'.bundle ⟶ B.bundle)
    (q : @Stacks.Chow.bundle (S.obj X') E' B'.isFiniteLocallyFree ⟶
      @Stacks.Chow.bundle (S.obj X) E B.isFiniteLocallyFree)
    (h : S.map g ≫ B.iso.hom = B'.iso.hom ≫ q)
    (φ : Nonempty ((Scheme.Modules.pullback q).obj
      (@Stacks.Chow.bundleTwist (S.obj X) E B.isFiniteLocallyFree) ≅
        @Stacks.Chow.bundleTwist (S.obj X') E' B'.isFiniteLocallyFree)) :
    Nonempty ((Scheme.Modules.pullback (S.map g)).obj B.twist ≅ B'.twist) := by
  obtain ⟨φ⟩ := φ
  rw [B.twist_eq, B'.twist_eq]
  exact ⟨(Scheme.Modules.pullbackComp (S.map g) B.iso.hom).app _ ≪≫
    (Scheme.Modules.pullbackCongr h).app _ ≪≫
    ((Scheme.Modules.pullbackComp B'.iso.hom q).app _).symm ≪≫
    (Scheme.Modules.pullback B'.iso.hom).mapIso φ⟩

/-- **The twist of `𝐏(ℰ)` pulls back along the clause-(3)(b) morphism to the twist of
`𝐏(f^*ℰ)`.**

This is the fact that used to be assumed alongside clause (3)(b). It is derived: the morphism of
schemes is the base-change morphism, by `IsBundleCompare.map_eq`; the twist of `𝐏(ℰ)` pulls back
along *that* to the twist of `𝐏(f^*ℰ)`, by the base change of the twist; and the two
identifications of clause (3)(a) are carried along by the pseudofunctoriality of pullback,
`AlgebraicGeometry.Scheme.Modules.pullbackComp` with
`AlgebraicGeometry.Scheme.Modules.pullbackCongr`. -/
theorem nonempty_pullback_twist_of_isBundleCompare (f : X' ⟶ X)
    (B : BundleObject S X E r) (B' : BundleObject S X' E' r)
    (e : (Scheme.Modules.pullback (S.map f)).obj E ≅ E') (g : B'.bundle ⟶ B.bundle)
    (h : IsBundleCompare f B B' e g) :
    Nonempty ((Scheme.Modules.pullback (S.map g)).obj B.twist ≅ B'.twist) := by
  have := B.isFiniteLocallyFree
  have := B'.isFiniteLocallyFree
  exact nonempty_pullback_twist_of_map_eq B B' g _ h.map_eq
    (nonempty_pullback_bundleTwist_bundleBaseChangeHom f B B' e)

end BundleObject

/-! ### Clause (3)(c) -/

/-- **Clause (3)(c) of the source's category: for a surjection `ℰ ⟶ 𝓕` of finite locally free
modules, the induced closed immersion `𝐏(𝓕) ⟶ 𝐏(ℰ)` is a morphism of `𝒞`.**

As with clause (3)(b), this is a *closure* property and says nothing else. The induced morphism of
schemes is the constructed `Stacks.Chow.GenuineChern.bundleEmbedding`, a closed immersion by
`Stacks.Chow.GenuineChern.isClosedImmersion_bundleEmbedding`; `map_eq` requires the morphism of
`𝒞` to be it, read through the two identifications of clause (3)(a), and `comp_proj` is "over
`X`", which has to be said because `𝒞` is presented by an indexing functor.

What the source does **not** assume here, and what used to be assumed alongside the clause, is
that this morphism carries `c₁^A(𝒪_{𝐏(ℰ)}(1))` to `c₁^A(𝒪_{𝐏(𝓕)}(1))`. That is
`Stacks.WeilCohomology.BundleObject.nonempty_pullback_twist_of_isBundleEmbedding`, from
`Stacks.Chow.GenuineChern.bundleEmbeddingTwistIso`. -/
structure IsBundleEmbedding {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}} {X : C}
    (T : ShortComplex (S.obj X).Modules) (hT : T.ShortExact) {r : ℕ}
    (B : BundleObject S X T.X₂ (r + 1)) (B' : BundleObject S X T.X₃ r)
    (i : B'.bundle ⟶ B.bundle) : Prop where
  /-- The morphism of `𝒞` lies over `X`. -/
  comp_proj : i ≫ B.proj = B'.proj
  /-- Its morphism of schemes is the induced closed immersion `𝐏(𝓕) ⟶ 𝐏(ℰ)`, read through the
  identifications of clause (3)(a). -/
  map_eq : S.map i ≫ B.iso.hom =
    B'.iso.hom ≫ @Stacks.Chow.GenuineChern.bundleEmbedding (S.obj X) T.X₂ T.X₃
      B.isFiniteLocallyFree B'.isFiniteLocallyFree T.g hT.epi_g

namespace BundleObject

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}} {X : C} {r : ℕ}

/-- **The twist of `𝐏(ℰ)` pulls back along the clause-(3)(c) morphism to the twist of `𝐏(𝓕)`.**

This is one of the two facts the old `exists_divisorDatum` assumed alongside clause (3)(c), and it
is a consequence: the morphism of schemes is the induced closed immersion, by
`IsBundleEmbedding.map_eq`, and the twist pulls back along *that* to the twist by
`Stacks.Chow.GenuineChern.bundleEmbeddingTwistIso`; the two clause-(3)(a) identifications are
carried along by `AlgebraicGeometry.Scheme.Modules.pullbackComp` with
`AlgebraicGeometry.Scheme.Modules.pullbackCongr`. -/
theorem nonempty_pullback_twist_of_isBundleEmbedding
    (T : ShortComplex (S.obj X).Modules) (hT : T.ShortExact)
    (B : BundleObject S X T.X₂ (r + 1)) (B' : BundleObject S X T.X₃ r)
    (i : B'.bundle ⟶ B.bundle) (h : IsBundleEmbedding T hT B B' i) :
    Nonempty ((Scheme.Modules.pullback (S.map i)).obj B.twist ≅ B'.twist) := by
  have := B.isFiniteLocallyFree
  have := B'.isFiniteLocallyFree
  have := hT.epi_g
  exact nonempty_pullback_twist_of_map_eq B B' i _ h.map_eq
    ⟨Stacks.Chow.GenuineChern.bundleEmbeddingTwistIso T.g⟩

end BundleObject

/-! ### Sealing the construction

The constructed pieces of the projective bundle are **sealed** once
`Stacks.WeilCohomology.BundleObject.toBundleDatum` has been assembled out of them.

They are built from `Stacks.Chow.bundleTwist`, which unfolds through the symmetric algebra to the
relative `Proj` of a graded module sheaf. Left reducible, instance search inside the standing
situation of Section 45.12 — where a tuple of classes is multiplied by powers of
`c₁^A(𝒪_P(1))` — unfolds that chain while looking for the ring structure on `A(𝐏(ℰ))` and does
not terminate. Nothing downstream needs the bodies: the tautological datum is reached through
the fields of `Stacks.WeilCohomology.BundleDatum`, and the `toBundleDatum_*` equations above are
the only identifications anything asks for, and are already proved.

`Stacks.WeilCohomology.BundleObject.twistClass` is **not** sealed: unfolding it stops at the
sealed `twist` after one step, and leaving it transparent is what makes the twist class of the
constructed datum and the twist class of the object the same term by `rfl`. -/

attribute [irreducible] BundleObject.iso BundleObject.pullObjIso BundleObject.twist
  BundleObject.quot

end Stacks.WeilCohomology

end
