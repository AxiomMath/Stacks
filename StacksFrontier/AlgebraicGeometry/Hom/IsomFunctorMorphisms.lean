module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Hom.HomFunctorMorphisms
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsom

/-!
# Morphisms from an algebraic space into the relative Isom functor

In the relative Hom situation of Stacks 08JT — a morphism `f : X ⟶ base` of algebraic spaces
over a scheme `S` of a big fppf site and two quasi-coherent `𝒪_X`-modules `F`, `G` — the
functor `Isom(F, G)` of Stacks 08K7 is the subfunctor of `Hom(F, G)` cut out by invertibility.
Read as a presheaf on the whole big fppf site of `S` it sends a scheme `V` to the set of
*pairs* `(h, u)` of a morphism `h : V ⟶ base` and an *isomorphism* `u : F_V ⟶ G_V` of the
modules pulled back to `X ×_{base, h} V`.  Stacks 0D3T identifies the morphisms of fppf
sheaves from an algebraic space `T` into that presheaf with the pairs of the same shape at
`T`:

`Mor(T, Isom(F, G)) = {(h, u) | h : T ⟶ base, u : F_T ⟶ G_T an isomorphism}`,

the subscript `T` now meaning pullback to the algebraic space `X ×_{base, h} T`.

This is the argument of the source, which is a reduction to Stacks 0D3S: both sides of the
identification are subsets of the two sides of the identification
`Mor(T, Hom(F, G)) = {(h, u)}` of Stacks 0D3S, and what has to be checked is that those
subsets correspond.  Everything about Stacks 0D3S itself is imported from
`StacksFrontier.AlgebraicGeometry.Hom.HomFunctorMorphisms`; what is proved here is the
correspondence of the subsets, whose two halves are the stability of invertibility under
pullback and its descent along a scheme atlas of `T`.

## Main definitions

* `AlgebraicGeometry.Space.HomSituation.toSpaceModuleHom`: a homomorphism over an algebraic
  space over the base, read as the homomorphism of base-changed modules that it is, and
  `AlgebraicGeometry.Space.HomSituation.IsIsomOverAt`: invertibility of such a homomorphism.
* `AlgebraicGeometry.Space.HomSituation.isomSubpresheaf` and
  `AlgebraicGeometry.Space.HomSituation.isomSitePresheaf`: **`Isom(F, G)` read as a presheaf
  on the big fppf site of `S`**, as a subfunctor of the Hom presheaf
  `AlgebraicGeometry.Space.HomSituation.homSitePresheaf` of Stacks 0D3S and as a presheaf.
  Its sections over a scheme `V` are the pairs `(h, u)` with `u` invertible.
* `AlgebraicGeometry.Space.HomSituation.isomMorToHom` and
  `AlgebraicGeometry.Space.HomSituation.baseOfIsomMor`: a morphism of presheaves
  `T ⟶ Isom(F, G)` read as a morphism `T ⟶ Hom(F, G)`, and the morphism `T ⟶ base` it lies
  over.
* `AlgebraicGeometry.Space.HomSituation.EtaleReverseHomDescent`: the fullness clause of
  Stacks 04W8 for the *reversed* pair of modules, taken as a parameter here and proved as
  `AlgebraicGeometry.Space.HomSituation.etaleReverseHomDescent`; see the implementation notes.
* `AlgebraicGeometry.Space.HomSituation.isomMorOfSpaceIsom`: **the morphism of presheaves
  `T ⟶ Isom(F, G)` determined by a pair `(h, u)` with `u` invertible**, which is the
  construction `AlgebraicGeometry.Space.HomSituation.morOfSpaceHom` of Stacks 0D3S together
  with the invertibility of the pair it cuts out at every scheme-valued point.
* `AlgebraicGeometry.Space.HomSituation.isomMorOver` and
  `AlgebraicGeometry.Space.HomSituation.isomMorOverEquiv`: the morphism of presheaves over a
  fixed `h : T ⟶ base` determined by an isomorphism over `h`, and **the identification of
  Stacks 0D3T over `h`** it gives.
* `CategoryTheory.Subfunctor.liftOfMem`: a morphism into a presheaf whose values lie in a
  subfunctor, read as a morphism into that subfunctor.

## Main results

* `CategoryTheory.Functor.conjHom_eq_conjHom_of_inv` and
  `CategoryTheory.Functor.isIso_of_isIso_conjHom`: conjugation by a comparison of a functor
  with a composite carries a two-sided inverse to a two-sided inverse, hence agrees on the
  inverse of a morphism it agrees on; and a morphism whose conjugate has a conjugate inverse
  is invertible as soon as conjugation is injective.  These are the two abstract facts the
  descent of invertibility rests on.
* `AlgebraicGeometry.Space.HomSituation.spaceConjHom_injective`: **pullback of homomorphisms
  of *any* two modules along a surjective étale morphism of algebraic spaces over the base is
  injective**, the faithfulness clause of Stacks 04W8 for the one-member étale covering of
  base changes.  This is `AlgebraicGeometry.Space.HomSituation.homOverSpaceMap_injective` of
  Stacks 0D3S for an arbitrary pair of modules, which is what the descent of invertibility
  needs: it is applied at the pairs `(F, F)` and `(G, G)`.
* `AlgebraicGeometry.Space.HomSituation.isIsomOverAt_homOverSpaceMap`: **invertibility is
  stable under pullback** along a morphism of algebraic spaces over the base, which is what
  makes `isomSubpresheaf` a subfunctor.
* `AlgebraicGeometry.Space.HomSituation.isIsomOverAt_of_isIsomOverAt_homOverSpaceMap` and
  `AlgebraicGeometry.Space.HomSituation.isIsomOverAt_of_chart`: **invertibility descends along
  a surjective étale morphism of algebraic spaces over the base** admitting a kernel pair, and
  along the morphism of base changes cut out by a scheme atlas of `T`.
* `AlgebraicGeometry.Space.HomSituation.baseOfIsomMor_isomMorOfSpaceIsom`: **the first
  component of the pair is recovered from the morphism of presheaves** — the morphism to the
  base underlying `isomMorOfSpaceIsom (h, u)` is `h`.
* `AlgebraicGeometry.Space.HomSituation.bijective_isomMorOver`: **for a fixed `h : T ⟶ base`
  the map `u ↦ isomMorOfSpaceIsom (h, u)` is a bijection from the isomorphisms
  `u : F_T ⟶ G_T` onto the morphisms of presheaves `T ⟶ Isom(F, G)` lying over `h`.**

## Implementation notes

**How Stacks 0D3T is split here**, and how it rests on Stacks 0D3S.  The two sides of
Stacks 0D3T are cut out of the two sides of Stacks 0D3S: on the right by invertibility of the
second component, on the left by the subfunctor `isomSubpresheaf` of the Hom presheaf.  This
file proves the two halves: `baseOfIsomMor_isomMorOfSpaceIsom`, that the first component is
recovered, and `bijective_isomMorOver`, that for a fixed first component the invertible second
components correspond bijectively to the morphisms of presheaves into `Isom(F, G)` lying over
it, the latter for parameters `hc`, `hd`, `hd'`.  The complete identification, with those
parameters supplied by the library, is
`AlgebraicGeometry.Space.HomSituation.bijective_isomMorOfSpaceIsom` in
`StacksFrontier.AlgebraicGeometry.Hom.IsomFunctorMorphismsEquiv`, which carries the tag.

Both directions of the correspondence of the subsets go through the one point of substance.
Forwards, the pair cut out at a scheme-valued point of `T` by an invertible `u` is invertible,
because the inverse image of an isomorphism is an isomorphism.  Backwards, a morphism of
presheaves into `Isom(F, G)` cuts out an invertible pair at a scheme atlas `U ⟶ T` of
Stacks 0262, and the homomorphism over `h` that Stacks 0D3S produces from it has to be shown
invertible: that is invertibility descending along the one-member étale covering `X_U ⟶ X_T`
of base changes.  The injectivity of the identification is inherited from Stacks 0D3S with
nothing to add, the inclusion of a subfunctor being a monomorphism.

**Descent of invertibility is descent of the inverse, and costs no new input.**  An
isomorphism is a homomorphism with a two-sided inverse, so once the inverse of the pulled-back
homomorphism is known to descend, the two equations defining it descend with it: they are
equations between homomorphisms over `T`, and pullback of homomorphisms is injective by
`AlgebraicGeometry.Space.HomSituation.spaceConjHom_injective`, which is unconditional.  What
is carried is therefore only the *existence* of the descended inverse, and that is the
fullness clause of Stacks 04W8 again — for the pair `(G, F)` rather than for `(F, G)`, since
the inverse goes the other way.  It is a parameter here,
`AlgebraicGeometry.Space.HomSituation.EtaleReverseHomDescent`, which is
`AlgebraicGeometry.Space.HomSituation.EtaleHomDescent` of Stacks 0D3S verbatim with the two
modules exchanged, written with `CategoryTheory.Functor.conjHom` rather than with
`AlgebraicGeometry.Space.HomSituation.homOverSpaceMap` so that no second Hom situation has to
be introduced to state it.  Nothing about quasi-coherence of the base-changed modules is
needed, in contrast to the route through the fpqc descent of Stacks 08K8.

The compatibility that the carried clause asks of the inverse — that its two pullbacks along a
kernel pair of the atlas agree — is *proved*, not assumed: the two pullbacks of the
homomorphism itself agree, by functoriality of pullback and the kernel-pair relation, and a
two-sided inverse is unique.  That is
`CategoryTheory.Functor.conjHom_eq_conjHom_of_inv`.

**Morphisms of sheaves are morphisms of presheaves, and the source is lifted**, exactly as for
Stacks 0D3S: the homomorphisms of `𝒪`-modules on an algebraic space form a `Type (u + 1)`, so
`isomSitePresheaf` is a presheaf of `Type (u + 1)` while the functor of points of an algebraic
space is a presheaf of `Type u`, and the morphisms of Stacks 0D3T are morphisms out of
`T.obj ⋙ uliftFunctor`.  Morphisms of presheaves between presheaves that happen to be sheaves
are the morphisms of the category of sheaves, so nothing is lost by not bundling either side as
an object of `Sheaf`; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Hom.HomFunctorMorphisms`, whose convention this is.

**Two readings of `Isom(F, G)`.**  `AlgebraicGeometry.Space.HomSituation.isomFunctor` of
Stacks 08K7 is indexed by the test *schemes over the base*, while `isomSitePresheaf` is indexed
by the schemes of the big fppf site of `S`, a section carrying the morphism to the base as
part of its data; the second is the first read as a presheaf on the site, which is the reading
the left-hand side of Stacks 0D3T needs.  Both are cut out of the corresponding reading of
`Hom(F, G)` by invertibility of the homomorphism, and the predicate is the same one in both
cases up to the index: `AlgebraicGeometry.Space.HomSituation.IsIsomAt` of Stacks 08K8 for the
first, `AlgebraicGeometry.Space.HomSituation.IsIsomOverAt` here for the second, each saying
that the base-changed homomorphism is an isomorphism.

**The four performance disciplines of Stacks 0D3S are observed here too.**  Every statement
about invertibility is phrased through the accessor
`AlgebraicGeometry.Space.HomSituation.toSpaceModuleHom` rather than by an inline ascription,
`AlgebraicGeometry.Space.HomSituation.spaceHomAt` being a `def` and not an `abbrev`; the two
facts about conjugation with content are stated over abstract categories, so that the concrete
Hom set is never unfolded at the point of use; the pair cut out at a scheme-valued point is
put into explicit `⟨b, α⟩` form before any comparison; and the goals about morphisms of
algebraic spaces over the base are closed by explicit rewriting.  The carried clause is stated
with `CategoryTheory.Functor.conjHom` at explicitly given comparisons for the same reason that
`AlgebraicGeometry.Space.HomSituation.isIsomAt_homMap_iff` is.

**The coherence `hc`.**  `AlgebraicGeometry.Space.ModulePushforwardCoherence` is what makes
pullback of homomorphisms functorial at all, and is a parameter of every functor here; the
library supplies it as `AlgebraicGeometry.Space.modulePushforwardCoherence`, at which the
complete identification `bijective_isomMorOfSpaceIsom` is stated.

## References

* [Stacks Project, Tag 0D3T](https://stacks.math.columbia.edu/tag/0D3T)
* [Stacks Project, Tag 0D3S](https://stacks.math.columbia.edu/tag/0D3S)
* [Stacks Project, Tag 08K7](https://stacks.math.columbia.edu/tag/08K7)
* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- Conjugation carries a composite to the composite of the conjugates. -/
private theorem conjHom_comp_eq {C : Type*} {D₁ : Type*} {D₂ : Type*}
    [Category* C] [Category* D₁] [Category* D₂]
    {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {K₁ K₂ K₃ : C}
    (a : P₁.obj K₁ ⟶ P₁.obj K₂) (b : P₁.obj K₂ ⟶ P₁.obj K₃) :
    conjHom e (a ≫ b) = conjHom e a ≫ conjHom e b := by
  simp [conjHom]

/-- Conjugation carries an identity to the identity. -/
private theorem conjHom_id_eq {C : Type*} {D₁ : Type*} {D₂ : Type*}
    [Category* C] [Category* D₁] [Category* D₂]
    {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {K : C} :
    conjHom e (𝟙 (P₁.obj K)) = 𝟙 (P₂.obj K) := by
  simp [conjHom]

/-- **Conjugation agrees on a two-sided inverse as soon as it agrees on the morphism.**  Let
`e₁ : P₂ ≅ P₁ ⋙ L₁` and `e₂ : P₂ ≅ P₁ ⋙ L₂` be two comparisons of one and the same pair of
functors and let `y` be a two-sided inverse of `x`.  Conjugation carries composites to
composites and identities to identities, so `conjHom e₁ y` is a two-sided inverse of
`conjHom e₁ x` and `conjHom e₂ y` is one of `conjHom e₂ x`; if the two conjugates of `x`
agree, the uniqueness of a two-sided inverse makes the two conjugates of `y` agree.

This is the compatibility that the descent of an inverse along a covering asks for: the two
pullbacks of the inverse along a kernel pair agree because the two pullbacks of the morphism
do. -/
theorem conjHom_eq_conjHom_of_inv {C : Type*} {D₁ : Type*} {D₂ : Type*}
    [Category* C] [Category* D₁] [Category* D₂]
    {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L₁ : D₁ ⥤ D₂} {L₂ : D₁ ⥤ D₂}
    (e₁ : P₂ ≅ P₁ ⋙ L₁) (e₂ : P₂ ≅ P₁ ⋙ L₂) {M N : C}
    (x : P₁.obj M ⟶ P₁.obj N) (y : P₁.obj N ⟶ P₁.obj M)
    (hxy : x ≫ y = 𝟙 (P₁.obj M)) (hyx : y ≫ x = 𝟙 (P₁.obj N))
    (h : conjHom e₁ x = conjHom e₂ x) : conjHom e₁ y = conjHom e₂ y := by
  have k₁ : conjHom e₁ y ≫ conjHom e₁ x = 𝟙 (P₂.obj N) := by
    rw [← conjHom_comp_eq e₁ y x, hyx, conjHom_id_eq]
  have k₂ : conjHom e₂ x ≫ conjHom e₂ y = 𝟙 (P₂.obj M) := by
    rw [← conjHom_comp_eq e₂ x y, hxy, conjHom_id_eq]
  calc conjHom e₁ y = conjHom e₁ y ≫ 𝟙 (P₂.obj M) := (Category.comp_id _).symm
    _ = conjHom e₁ y ≫ conjHom e₂ x ≫ conjHom e₂ y := by rw [k₂]
    _ = (conjHom e₁ y ≫ conjHom e₁ x) ≫ conjHom e₂ y := by rw [← h, Category.assoc]
    _ = conjHom e₂ y := by rw [k₁, Category.id_comp]

/-- **A morphism whose conjugate is invertible by a conjugate is invertible.**  If `γ` is a
morphism in the other direction whose conjugate is a two-sided inverse of the conjugate of
`α`, and conjugation is injective on the two Hom sets of endomorphisms, then `γ` is itself a
two-sided inverse of `α`: conjugation carries the two equations to the two equations it has to
prove, and injectivity brings them back.

The statement is over abstract categories on purpose, as for
`CategoryTheory.Functor.conjHom_injective`: a consumer applies it to a comparison it has
already named, so the unifier is never asked to compare the concrete Hom sets. -/
theorem isIso_of_isIso_conjHom {C : Type*} {D₁ : Type*} {D₂ : Type*}
    [Category* C] [Category* D₁] [Category* D₂]
    {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {M N : C}
    (hinjM : Function.Injective (conjHom e (M := M) (N := M)))
    (hinjN : Function.Injective (conjHom e (M := N) (N := N)))
    {α : P₁.obj M ⟶ P₁.obj N} {γ : P₁.obj N ⟶ P₁.obj M}
    (h₁ : conjHom e α ≫ conjHom e γ = 𝟙 (P₂.obj M))
    (h₂ : conjHom e γ ≫ conjHom e α = 𝟙 (P₂.obj N)) : IsIso α := by
  refine ⟨⟨γ, hinjM ?_, hinjN ?_⟩⟩
  · rw [conjHom_comp_eq, h₁, conjHom_id_eq]
  · rw [conjHom_comp_eq, h₂, conjHom_id_eq]

end CategoryTheory.Functor

namespace CategoryTheory.Subfunctor

universe w

/-- **A morphism into a presheaf whose values lie in a subfunctor factors through it.**  The
components of the factorisation are the components of the given morphism, read as elements of
the subsets; naturality is the naturality of the given morphism, the subfunctor acting by the
restriction maps of the ambient presheaf. -/
def liftOfMem {C : Type*} [Category* C] {F : C ⥤ Type w} (G : Subfunctor F) {P : C ⥤ Type w}
    (v : P ⟶ F) (hv : ∀ (U : C) (x : P.obj U), v.app U x ∈ G.obj U) : P ⟶ G.toFunctor where
  app U := TypeCat.ofHom fun x => ⟨v.app U x, hv U x⟩
  naturality _ _ i := ConcreteCategory.hom_ext _ _ fun x =>
    Subtype.ext (NatTrans.naturality_apply v i x)

/-- The factorisation of a morphism through a subfunctor is a factorisation: composing it with
the inclusion gives the morphism back. -/
@[simp]
theorem liftOfMem_ι {C : Type*} [Category* C] {F : C ⥤ Type w} (G : Subfunctor F)
    {P : C ⥤ Type w} (v : P ⟶ F) (hv : ∀ (U : C) (x : P.obj U), v.app U x ∈ G.obj U) :
    G.liftOfMem v hv ≫ G.ι = v :=
  NatTrans.ext (funext fun _ => ConcreteCategory.hom_ext _ _ fun _ => rfl)

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

universe u

namespace HomSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (s : HomSituation B S hS)

/-! ### Invertibility of a homomorphism over an algebraic space over the base -/

/-- A homomorphism over an algebraic space `T` over the base, read as the homomorphism
`F_T ⟶ G_T` of base-changed modules that it is.  The two are the same by definition; the
accessor exists so that no statement below asks the unifier to unfold
`AlgebraicGeometry.Space.HomSituation.spaceHomAt`. -/
def toSpaceModuleHom {T : Over s.base} (α : s.spaceHomAt T) :
    (modulePullback B S hS (overProjection s.f T)).obj s.F ⟶
      (modulePullback B S hS (overProjection s.f T)).obj s.G :=
  α

/-- **The invertible homomorphisms over an algebraic space over the base.**  A homomorphism
`α` over `T` is invertible when the `𝒪_{X_T}`-module homomorphism `F_T ⟶ G_T` that it is, is
an isomorphism. -/
def IsIsomOverAt {T : Over s.base} (α : s.spaceHomAt T) : Prop :=
  IsIso (s.toSpaceModuleHom α)

/-- A homomorphism over an algebraic space over the base is invertible exactly when it is an
isomorphism of the base-changed modules.  This is the definition, recorded so that a consumer
need not unfold it. -/
theorem isIsomOverAt_iff {T : Over s.base} (α : s.spaceHomAt T) :
    s.IsIsomOverAt α ↔ IsIso (s.toSpaceModuleHom α) :=
  Iff.rfl

/-- **Pullback of a homomorphism is conjugation of the module homomorphism.**  This is the
definition of `AlgebraicGeometry.Space.HomSituation.homOverSpaceMap`, recorded at the level of
module homomorphisms so that invertibility can be read off from it. -/
theorem toSpaceModuleHom_homOverSpaceMap {U T : Over s.base} (g : U ⟶ T)
    (α : s.spaceHomAt T) :
    s.toSpaceModuleHom (s.homOverSpaceMap g α) =
      Functor.conjHom (s.spaceBaseChangeComparison g) (s.toSpaceModuleHom α) :=
  rfl

/-- **Pullback of homomorphisms of any two modules along a surjective étale morphism of
algebraic spaces over the base is injective.**  This is the faithfulness clause of Stacks 04W8
for the one-member étale covering `X_U ⟶ X_T` of the base changes, and it is unconditional: a
homomorphism of `𝒪`-modules is determined by its inverse images along an étale covering, by
`AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering`.

`AlgebraicGeometry.Space.HomSituation.homOverSpaceMap_injective` is the case of the two modules
of the situation.  The descent of invertibility below needs the cases `(F, F)` and `(G, G)` as
well, which is why the statement is over an arbitrary pair; injectivity is read off the
abstract comparison `AlgebraicGeometry.Space.HomSituation.spaceBaseChangeComparison` through
`CategoryTheory.Functor.conjHom_injective`, so the concrete Hom set is never unfolded. -/
theorem spaceConjHom_injective {U T : Over s.base} (g : U ⟶ T)
    (hsurj : IsSurjective B S hS g.left.hom) (hetale : IsEtale B S hS g.left.hom)
    (M N : Modules.{u, u} B S hS s.X.1 s.X.2) :
    Function.Injective
      (Functor.conjHom (s.spaceBaseChangeComparison g) (M := M) (N := N)) := by
  have hcov := s.isEtaleCovering_overBaseChangeMap g hsurj hetale
  refine Functor.conjHom_injective (M := M) (N := N) (s.spaceBaseChangeComparison g)
    fun α β hαβ => ?_
  exact QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering B S hS
    (fun _ : PUnit.{u + 1} => overBaseChange s.f U) (fun _ => overBaseChangeMap s.f g) hcov
    α β fun _ => hαβ

/-- **Invertibility of a pullback is invertibility of the inverse image.**  The pullback of a
homomorphism along a morphism `g : U ⟶ T` of algebraic spaces over the base is its inverse
image along `X_U ⟶ X_T`, read through the comparison of the two base changes; since that
comparison is an isomorphism of functors, the pullback is invertible exactly when the inverse
image is. -/
theorem isIsomOverAt_homOverSpaceMap_iff {U T : Over s.base} (g : U ⟶ T)
    (α : s.spaceHomAt T) :
    s.IsIsomOverAt (s.homOverSpaceMap g α) ↔
      IsIso ((modulePullback B S hS (overBaseChangeMap s.f g)).map
        (s.toSpaceModuleHom α)) := by
  rw [s.isIsomOverAt_iff (s.homOverSpaceMap g α), s.toSpaceModuleHom_homOverSpaceMap g α]
  exact Functor.isIso_conjHom_iff
    (L := modulePullback B S hS (overBaseChangeMap s.f g)) (M := s.F) (N := s.G)
    (s.spaceBaseChangeComparison g) (s.toSpaceModuleHom α)

/-- **Invertibility is stable under pullback along a morphism of algebraic spaces over the
base.**  The inverse image of an isomorphism is an isomorphism, so the pullback of an
invertible homomorphism is invertible. -/
theorem isIsomOverAt_homOverSpaceMap {U T : Over s.base} (g : U ⟶ T) {α : s.spaceHomAt T}
    (hα : s.IsIsomOverAt α) : s.IsIsomOverAt (s.homOverSpaceMap g α) := by
  rw [s.isIsomOverAt_homOverSpaceMap_iff g α]
  have := (s.isIsomOverAt_iff α).mp hα
  infer_instance

/-! ### Descent of invertibility along a surjective étale morphism -/

/-- **The fullness clause of Stacks 04W8 for the reversed pair of modules.**  Along a
surjective étale morphism `g : U ⟶ T` of algebraic spaces over the base, a homomorphism
`w : G_U ⟶ F_U` whose two pullbacks along a kernel pair of `g` agree is the pullback of a
homomorphism `G_T ⟶ F_T`.

This is `AlgebraicGeometry.Space.HomSituation.EtaleHomDescent` with the two modules exchanged,
and it is a parameter here for the same reason: it is descent of homomorphisms of
quasi-coherent modules along the one-member étale covering `X_U ⟶ X_T` of base changes, which
is proved downstream, in `StacksFrontier.AlgebraicGeometry.Hom.IsomFunctorMorphismsEquiv`, as
`AlgebraicGeometry.Space.HomSituation.etaleReverseHomDescent`.  It is the *only* input the
descent of invertibility needs: the reverse direction is where an inverse lives, and the two
equations making it an inverse are then proved, not assumed.

Pullback is written as `CategoryTheory.Functor.conjHom` of
`AlgebraicGeometry.Space.HomSituation.spaceBaseChangeComparison`, which is what
`AlgebraicGeometry.Space.HomSituation.homOverSpaceMap` is, so that stating the clause needs no
second Hom situation with the two modules exchanged. -/
structure EtaleReverseHomDescent : Prop where
  /-- Descent of a homomorphism `G_U ⟶ F_U` over a chart which is invariant under a kernel
  pair. -/
  exists_conjHom_eq : ∀ {U T : Over s.base} (g : U ⟶ T),
    IsSurjective B S hS g.left.hom → IsEtale B S hS g.left.hom →
    ∀ {R : Over s.base} (p q : R ⟶ U),
      IsPullback p.left.hom q.left.hom g.left.hom g.left.hom →
      ∀ w : (modulePullback B S hS (overProjection s.f U)).obj s.G ⟶
        (modulePullback B S hS (overProjection s.f U)).obj s.F,
        Functor.conjHom (s.spaceBaseChangeComparison p) w =
            Functor.conjHom (s.spaceBaseChangeComparison q) w →
          ∃ α : (modulePullback B S hS (overProjection s.f T)).obj s.G ⟶
            (modulePullback B S hS (overProjection s.f T)).obj s.F,
            Functor.conjHom (s.spaceBaseChangeComparison g) α = w

/-- **Invertibility descends along a surjective étale morphism of algebraic spaces over the
base admitting a kernel pair.**  Let `g : U ⟶ T` be surjective and étale, let `(p, q)` be a
kernel pair of `g`, and let `α` be a homomorphism over `T` whose pullback along `g` is
invertible.  Then `α` is invertible.

The two pullbacks along the kernel pair of the pullback of `α` agree, pullback of
homomorphisms being functorial, so the two pullbacks of its *inverse* agree by
`CategoryTheory.Functor.conjHom_eq_conjHom_of_inv`; the carried clause `hd` then descends that
inverse to a homomorphism `γ : G_T ⟶ F_T`, and `γ` is a two-sided inverse of `α` because its
two composites with `α` have the same pullbacks along `g` as the two identities and pullback is
injective by `AlgebraicGeometry.Space.HomSituation.spaceConjHom_injective`.  That last step is
`CategoryTheory.Functor.isIso_of_isIso_conjHom`. -/
theorem isIsomOverAt_of_isIsomOverAt_homOverSpaceMap (hc : ModulePushforwardCoherence B S hS)
    (hd : s.EtaleReverseHomDescent) {U T : Over s.base} (g : U ⟶ T)
    (hsurj : IsSurjective B S hS g.left.hom) (hetale : IsEtale B S hS g.left.hom)
    {R : Over s.base} (p q : R ⟶ U)
    (hpb : IsPullback p.left.hom q.left.hom g.left.hom g.left.hom)
    (α : s.spaceHomAt T) (hα : s.IsIsomOverAt (s.homOverSpaceMap g α)) :
    s.IsIsomOverAt α := by
  have hpq : p ≫ g = q ≫ g :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hpb.w)
  have hiso : IsIso (Functor.conjHom (s.spaceBaseChangeComparison g)
      (s.toSpaceModuleHom α)) := by
    rw [← s.toSpaceModuleHom_homOverSpaceMap g α]
    exact hα
  have hA : Functor.conjHom (s.spaceBaseChangeComparison p)
        (Functor.conjHom (s.spaceBaseChangeComparison g) (s.toSpaceModuleHom α)) =
      Functor.conjHom (s.spaceBaseChangeComparison q)
        (Functor.conjHom (s.spaceBaseChangeComparison g) (s.toSpaceModuleHom α)) := by
    have h₁ := s.homOverSpaceMap_comp hc p g α
    have h₂ := s.homOverSpaceMap_comp hc q g α
    have h₃ : s.homOverSpaceMap (p ≫ g) α = s.homOverSpaceMap (q ≫ g) α := by rw [hpq]
    rw [h₁, h₂] at h₃
    exact h₃
  have hcompat := Functor.conjHom_eq_conjHom_of_inv (s.spaceBaseChangeComparison p)
    (s.spaceBaseChangeComparison q)
    (Functor.conjHom (s.spaceBaseChangeComparison g) (s.toSpaceModuleHom α))
    (inv (Functor.conjHom (s.spaceBaseChangeComparison g) (s.toSpaceModuleHom α)))
    (IsIso.hom_inv_id _) (IsIso.inv_hom_id _) hA
  obtain ⟨γ, hγ⟩ := hd.exists_conjHom_eq g hsurj hetale p q hpb _ hcompat
  have h₁ : Functor.conjHom (s.spaceBaseChangeComparison g) (s.toSpaceModuleHom α) ≫
      Functor.conjHom (s.spaceBaseChangeComparison g) γ = 𝟙 _ := by
    rw [hγ]
    exact IsIso.hom_inv_id _
  have h₂ : Functor.conjHom (s.spaceBaseChangeComparison g) γ ≫
      Functor.conjHom (s.spaceBaseChangeComparison g) (s.toSpaceModuleHom α) = 𝟙 _ := by
    rw [hγ]
    exact IsIso.inv_hom_id _
  exact Functor.isIso_of_isIso_conjHom (s.spaceBaseChangeComparison g)
    (s.spaceConjHom_injective g hsurj hetale s.F s.F)
    (s.spaceConjHom_injective g hsurj hetale s.G s.G) h₁ h₂

/-- **Invertibility descends along the morphism of base changes cut out by a scheme atlas.**
Let `a : U ⟶ T` be a scheme atlas of `T` which is surjective and étale after every
representable base change, let `x` be the corresponding scheme-valued point of `T`, and let
`α` be a homomorphism over `h : T ⟶ base` whose pullback along the induced morphism
`X_U ⟶ X_T` is invertible.  Then `α` is invertible.

The atlas has a represented kernel pair by Stacks 0262, in the form of
`AlgebraicGeometry.Space.exists_kernelPair_of_etale_atlas`, and the two projections of that
kernel pair are morphisms of algebraic spaces over the base; the descent is then
`AlgebraicGeometry.Space.HomSituation.isIsomOverAt_of_isIsomOverAt_homOverSpaceMap`. -/
theorem isIsomOverAt_of_chart (hc : ModulePushforwardCoherence B S hS)
    (hd : s.EtaleReverseHomDescent) {T : AlgebraicSpaces B S hS} (h : T ⟶ s.base)
    {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ T.1}
    (hasurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    {x : T.1.obj (Opposite.op U)} (hx : yonedaEquiv.symm x = a)
    (α : s.spaceHomAt (Over.mk h))
    (hα : s.IsIsomOverAt (s.homOverSpaceMap (s.pointOver h x) α)) : s.IsIsomOverAt α := by
  have hL : (s.pointOver h x).left.hom = a := hx
  have hasurj' : IsSurjective B S hS (s.pointOver h x).left.hom := by
    rw [hL]
    exact isSurjective_of_presheafSurjective B S hS a hasurj
  have haetale' : IsEtale B S hS (s.pointOver h x).left.hom := by
    rw [hL]
    exact (isEtale_iff_presheaf_of_yoneda B S hS a).2 haetale
  obtain ⟨R, σ, τ, hR⟩ := exists_kernelPair_of_etale_atlas B S hS a haetale
  have hστ : (schemeSpaceFunctor B S hS).map τ ≫ pointSpaceMap (T := T) x =
      (schemeSpaceFunctor B S hS).map σ ≫ pointSpaceMap (T := T) x := by
    refine ObjectProperty.hom_ext _ ?_
    change yoneda.map τ ≫ yonedaEquiv.symm x = yoneda.map σ ≫ yonedaEquiv.symm x
    rw [hx, hR.w]
  have hq : (schemeSpaceFunctor B S hS).map τ ≫ (pointSpaceMap (T := T) x ≫ h) =
      (schemeSpaceFunctor B S hS).map σ ≫ (pointSpaceMap (T := T) x ≫ h) := by
    rw [← Category.assoc, ← Category.assoc, hστ]
  obtain ⟨q, hqleft⟩ : ∃ q : (Over.mk ((schemeSpaceFunctor B S hS).map σ ≫
        (pointSpaceMap (T := T) x ≫ h)) : Over s.base) ⟶
        Over.mk (pointSpaceMap (T := T) x ≫ h),
      q.left = (schemeSpaceFunctor B S hS).map τ :=
    ⟨Over.homMk ((schemeSpaceFunctor B S hS).map τ) hq, rfl⟩
  have hpb : IsPullback
      (HomOver.restrictMap s σ (pointSpaceMap (T := T) x ≫ h)).left.hom q.left.hom
      (s.pointOver h x).left.hom (s.pointOver h x).left.hom := by
    rw [hqleft, hL]
    change IsPullback (yoneda.map σ) (yoneda.map τ) a a
    exact hR
  exact s.isIsomOverAt_of_isIsomOverAt_homOverSpaceMap hc hd (s.pointOver h x) hasurj'
    haetale' (HomOver.restrictMap s σ (pointSpaceMap (T := T) x ≫ h)) q hpb α hα

/-! ### The Isom functor as a presheaf on the big fppf site -/

/-- **Stacks 08K7 on the big fppf site.**  The relative Isom functor `Isom(F, G)` as a
subfunctor of the Hom presheaf of Stacks 0D3S: a section over a scheme `V` of the site is a
pair `(h, u)` of a morphism `h : V ⟶ base` and a homomorphism `u : F_V ⟶ G_V` which is an
*isomorphism*.

It is a subfunctor because invertibility is stable under pullback,
`AlgebraicGeometry.Space.HomSituation.isIsomOverAt_homOverSpaceMap`. -/
def isomSubpresheaf (hc : ModulePushforwardCoherence B S hS) :
    Subfunctor (s.homSitePresheaf hc) where
  obj V := {z : (s.homSitePresheaf hc).obj V | s.IsIsomOverAt (show s.HomOver V.unop from z).hom}
  map {V W} i z hz := by
    change s.IsIsomOverAt (HomOver.restrict s (show s.HomOver V.unop from z) i.unop).hom
    rw [HomOver.restrict_hom]
    exact s.isIsomOverAt_homOverSpaceMap _ hz

/-- **Stacks 08K7 on the big fppf site.**  The relative Isom functor `Isom(F, G)` read as a
presheaf on the big fppf site of `S`: a section over a scheme `V` is a morphism `V ⟶ base`
together with an isomorphism `F_V ⟶ G_V` of the modules pulled back to `X ×_{base} V`, and
restriction pulls back both.  Its inclusion into the Hom presheaf of Stacks 0D3S is
`CategoryTheory.Subfunctor.ι`. -/
def isomSitePresheaf (hc : ModulePushforwardCoherence B S hS) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  (s.isomSubpresheaf hc).toFunctor

/-- A section of the Isom presheaf over a scheme of the site is an invertible section of the
Hom presheaf there. -/
theorem isomSitePresheaf_obj (hc : ModulePushforwardCoherence B S hS)
    (V : (BigFppfOver B S hS)ᵒᵖ) :
    (s.isomSitePresheaf hc).obj V = {z : s.HomOver V.unop // s.IsIsomOverAt z.hom} :=
  rfl

/-- **A morphism of presheaves `T ⟶ Isom(F, G)`, read as a morphism `T ⟶ Hom(F, G)`**, by
composing with the inclusion of the subfunctor.  This is the inclusion of the left-hand side of
Stacks 0D3T into the left-hand side of Stacks 0D3S. -/
def isomMorToHom (hc : ModulePushforwardCoherence B S hS) {T : AlgebraicSpaces B S hS}
    (v : T.1 ⋙ uliftFunctor.{u + 1, u} ⟶ s.isomSitePresheaf hc) :
    T.1 ⋙ uliftFunctor.{u + 1, u} ⟶ s.homSitePresheaf hc :=
  v ≫ (s.isomSubpresheaf hc).ι

/-- **The morphism to the base underlying a morphism of presheaves into the Isom presheaf**:
the morphism to the base underlying the morphism into the Hom presheaf it is. -/
def baseOfIsomMor (hc : ModulePushforwardCoherence B S hS) {T : AlgebraicSpaces B S hS}
    (v : T.1 ⋙ uliftFunctor.{u + 1, u} ⟶ s.isomSitePresheaf hc) : T ⟶ s.base :=
  s.baseOfMor hc (s.isomMorToHom hc v)

/-- The pair that a morphism of presheaves into the Isom presheaf cuts out at a scheme-valued
point is the pair the underlying morphism into the Hom presheaf cuts out, and it is
invertible. -/
theorem isIsomOverAt_morApp_isomMorToHom (hc : ModulePushforwardCoherence B S hS)
    {T : AlgebraicSpaces B S hS} (v : T.1 ⋙ uliftFunctor.{u + 1, u} ⟶ s.isomSitePresheaf hc)
    {V : (BigFppfOver B S hS)ᵒᵖ} (x : T.1.obj V) :
    s.IsIsomOverAt (s.morApp hc (s.isomMorToHom hc v) x).hom :=
  (ConcreteCategory.hom (v.app V) (ULift.up x)).2

/-! ### The identification of Stacks 0D3T -/

/-- **The morphism of presheaves `T ⟶ Isom(F, G)` determined by a pair `(h, u)` at an
algebraic space with `u` invertible.**  It is the morphism `T ⟶ Hom(F, G)` of Stacks 0D3S,
which sends a scheme-valued point `a` of `T` to the pair `(h ∘ a, a^*u)`, together with the
invertibility of `a^*u`; that invertibility is the stability of
`AlgebraicGeometry.Space.HomSituation.isIsomOverAt_homOverSpaceMap`, and the factorisation
through the subfunctor is `CategoryTheory.Subfunctor.liftOfMem`. -/
def isomMorOfSpaceIsom (hc : ModulePushforwardCoherence B S hS)
    {T : AlgebraicSpaces B S hS} (h : T ⟶ s.base) (u : s.spaceHomAt (Over.mk h))
    (hu : s.IsIsomOverAt u) :
    T.1 ⋙ uliftFunctor.{u + 1, u} ⟶ s.isomSitePresheaf hc :=
  (s.isomSubpresheaf hc).liftOfMem (s.morOfSpaceHom hc ⟨h, u⟩) fun V y => by
    change s.IsIsomOverAt (s.homOverOfPair (⟨h, u⟩ : s.SpaceHomPair T) y.down).hom
    rw [s.homOverOfPair_eq_mk h u y.down]
    exact s.isIsomOverAt_homOverSpaceMap (s.pointOver h y.down) hu

/-- The morphism into the Hom presheaf underlying the morphism of presheaves of an invertible
pair is the morphism of presheaves of that pair of Stacks 0D3S. -/
@[simp]
theorem isomMorToHom_isomMorOfSpaceIsom (hc : ModulePushforwardCoherence B S hS)
    {T : AlgebraicSpaces B S hS} (h : T ⟶ s.base) (u : s.spaceHomAt (Over.mk h))
    (hu : s.IsIsomOverAt u) :
    s.isomMorToHom hc (s.isomMorOfSpaceIsom hc h u hu) =
      s.morOfSpaceHom hc (⟨h, u⟩ : s.SpaceHomPair T) :=
  (s.isomSubpresheaf hc).liftOfMem_ι _ _

/-- **The morphism to the base is recovered from the morphism of presheaves into the Isom
presheaf**: for a pair `(h, u)` with `u` invertible the morphism underlying
`isomMorOfSpaceIsom (h, u)` is `h`.  This is the half of Stacks 0D3T that needs no descent,
and it is inherited from the corresponding half of Stacks 0D3S,
`AlgebraicGeometry.Space.HomSituation.baseOfMor_morOfSpaceHom`, the two left-hand sides being
compared through the inclusion of the subfunctor. -/
theorem baseOfIsomMor_isomMorOfSpaceIsom (hc : ModulePushforwardCoherence B S hS)
    {T : AlgebraicSpaces B S hS} (h : T ⟶ s.base) (u : s.spaceHomAt (Over.mk h))
    (hu : s.IsIsomOverAt u) :
    s.baseOfIsomMor hc (s.isomMorOfSpaceIsom hc h u hu) = h := by
  rw [baseOfIsomMor, s.isomMorToHom_isomMorOfSpaceIsom hc h u hu]
  exact s.baseOfMor_morOfSpaceHom hc ⟨h, u⟩

/-- **The morphism of presheaves `T ⟶ Isom(F, G)` over a fixed `h : T ⟶ base` determined by an
isomorphism `u : F_T ⟶ G_T`.**  It is
`AlgebraicGeometry.Space.HomSituation.isomMorOfSpaceIsom` of the pair `(h, u)`, together with
the proof that it lies over `h`; that proof is
`AlgebraicGeometry.Space.HomSituation.baseOfIsomMor_isomMorOfSpaceIsom`. -/
def isomMorOver (hc : ModulePushforwardCoherence B S hS) {T : AlgebraicSpaces B S hS}
    (h : T ⟶ s.base) (p : {u : s.spaceHomAt (Over.mk h) // s.IsIsomOverAt u}) :
    {v : T.1 ⋙ uliftFunctor.{u + 1, u} ⟶ s.isomSitePresheaf hc //
      s.baseOfIsomMor hc v = h} :=
  ⟨s.isomMorOfSpaceIsom hc h p.1 p.2, s.baseOfIsomMor_isomMorOfSpaceIsom hc h p.1 p.2⟩

/-- **The second component of the pair is determined by the morphism of presheaves.**  The
inclusion of the Isom presheaf into the Hom presheaf is a monomorphism, so two isomorphisms
over `h` giving the same morphism into `Isom(F, G)` give the same morphism into `Hom(F, G)`;
they therefore agree by the corresponding half of Stacks 0D3S,
`AlgebraicGeometry.Space.HomSituation.injective_morOver`, which uses only the faithfulness
clause of Stacks 04W8 and needs no descent hypothesis. -/
theorem injective_isomMorOver (hc : ModulePushforwardCoherence B S hS)
    {T : AlgebraicSpaces B S hS} (h : T ⟶ s.base) :
    Function.Injective (s.isomMorOver hc h) := by
  intro p p' e
  have e₁ : s.isomMorOfSpaceIsom hc h p.1 p.2 = s.isomMorOfSpaceIsom hc h p'.1 p'.2 :=
    congrArg Subtype.val e
  have e₂ : s.morOfSpaceHom hc (⟨h, p.1⟩ : s.SpaceHomPair T) =
      s.morOfSpaceHom hc ⟨h, p'.1⟩ := by
    rw [← s.isomMorToHom_isomMorOfSpaceIsom hc h p.1 p.2,
      ← s.isomMorToHom_isomMorOfSpaceIsom hc h p'.1 p'.2, isomMorToHom, isomMorToHom, e₁]
  exact Subtype.ext (s.injective_morOver hc h (Subtype.ext e₂))

/-- **Every morphism of presheaves `T ⟶ Isom(F, G)` lying over `h` comes from an isomorphism
over `h`.**  The underlying morphism into `Hom(F, G)` comes from a homomorphism `u` over `h` by
the corresponding half of Stacks 0D3S,
`AlgebraicGeometry.Space.HomSituation.surjective_morOver`, and what remains is that `u` is
invertible.  At a scheme atlas of `T` the pair that the morphism cuts out is invertible, by the
very fact that the morphism goes into the Isom presheaf, and that pair is the pullback of `u`
along the induced morphism of base changes; so `u` is invertible by
`AlgebraicGeometry.Space.HomSituation.isIsomOverAt_of_chart`.  The two morphisms of presheaves
then agree because their composites with the inclusion of the subfunctor do, that inclusion
being a monomorphism. -/
theorem surjective_isomMorOver (hc : ModulePushforwardCoherence B S hS)
    (hd : s.EtaleHomDescent) (hd' : s.EtaleReverseHomDescent)
    {T : AlgebraicSpaces B S hS} (h : T ⟶ s.base) :
    Function.Surjective (s.isomMorOver hc h) := by
  rintro ⟨v, hv⟩
  obtain ⟨U, a, hasurj, haetale⟩ := T.property.exists_atlas
  obtain ⟨x, hx⟩ : ∃ x : T.1.obj (Opposite.op U), yonedaEquiv.symm x = a :=
    ⟨yonedaEquiv a, Equiv.symm_apply_apply _ _⟩
  obtain ⟨u, hu⟩ := s.surjective_morOver hc hd h ⟨s.isomMorToHom hc v, hv⟩
  have hmor : s.morOfSpaceHom hc (⟨h, u⟩ : s.SpaceHomPair T) = s.isomMorToHom hc v :=
    congrArg Subtype.val hu
  have hpt : s.homOverOfPair (⟨h, u⟩ : s.SpaceHomPair T) x =
      s.morApp hc (s.isomMorToHom hc v) x := by
    rw [← s.morApp_morOfSpaceHom hc (⟨h, u⟩ : s.SpaceHomPair T) x, hmor]
  have hchart : s.IsIsomOverAt (s.homOverSpaceMap (s.pointOver h x) u) := by
    have hiso := s.isIsomOverAt_morApp_isomMorToHom hc v x
    rw [← hpt, s.homOverOfPair_eq_mk h u x] at hiso
    exact hiso
  have hu' : s.IsIsomOverAt u :=
    s.isIsomOverAt_of_chart hc hd' h hasurj haetale hx u hchart
  refine ⟨⟨u, hu'⟩, Subtype.ext ?_⟩
  refine (cancel_mono (s.isomSubpresheaf hc).ι).mp ?_
  change s.isomMorToHom hc (s.isomMorOfSpaceIsom hc h u hu') = s.isomMorToHom hc v
  rw [s.isomMorToHom_isomMorOfSpaceIsom hc h u hu']
  exact hmor

/-- **Stacks 0D3T, the fibres of the identification.**  For a fixed morphism `h : T ⟶ base` of
algebraic spaces over `S`, the assignment `u ↦ isomMorOfSpaceIsom (h, u)` is a *bijection* from
the isomorphisms `u : F_T ⟶ G_T` of the two modules pulled back to `X ×_{base, h} T` onto the
morphisms of presheaves `T ⟶ Isom(F, G)` lying over `h`.

Together with `AlgebraicGeometry.Space.HomSituation.baseOfIsomMor_isomMorOfSpaceIsom`, which
recovers the first component, this is the identification
`Mor(T, Isom(F, G)) = {(h, u) | h : T ⟶ base, u : F_T ⟶ G_T an isomorphism}` of Stacks 0D3T.

This is the argument of the source: both sides are cut out of the two sides of Stacks 0D3S, and
what is checked is that the subsets correspond.  Injectivity is inherited from Stacks 0D3S and
is unconditional beyond the coherence `hc`.  Surjectivity needs, beyond the hypothesis `hd` of
Stacks 0D3S, that invertibility descends along the covering of base changes cut out by a scheme
atlas of `T`, which is the same fullness clause of Stacks 04W8 for the reversed pair of
modules, the parameter `hd'`.  All three parameters are proved in the library, and the complete
identification at them is `AlgebraicGeometry.Space.HomSituation.bijective_isomMorOfSpaceIsom`. -/
theorem bijective_isomMorOver (hc : ModulePushforwardCoherence B S hS)
    (hd : s.EtaleHomDescent) (hd' : s.EtaleReverseHomDescent)
    {T : AlgebraicSpaces B S hS} (h : T ⟶ s.base) :
    Function.Bijective (s.isomMorOver hc h) :=
  ⟨s.injective_isomMorOver hc h, s.surjective_isomMorOver hc hd hd' h⟩

/-- **The identification of Stacks 0D3T over a fixed morphism to the base**, as an equivalence:
the isomorphisms `F_T ⟶ G_T` are the morphisms of presheaves `T ⟶ Isom(F, G)` lying over `h`.
Its forward direction is the source's construction
`AlgebraicGeometry.Space.HomSituation.isomMorOfSpaceIsom`, and it is an equivalence by
`AlgebraicGeometry.Space.HomSituation.bijective_isomMorOver`. -/
def isomMorOverEquiv (hc : ModulePushforwardCoherence B S hS) (hd : s.EtaleHomDescent)
    (hd' : s.EtaleReverseHomDescent) {T : AlgebraicSpaces B S hS} (h : T ⟶ s.base) :
    {u : s.spaceHomAt (Over.mk h) // s.IsIsomOverAt u} ≃
      {v : T.1 ⋙ uliftFunctor.{u + 1, u} ⟶ s.isomSitePresheaf hc //
        s.baseOfIsomMor hc v = h} :=
  Equiv.ofBijective (s.isomMorOver hc h) (s.bijective_isomMorOver hc hd hd' h)

end HomSituation

end AlgebraicGeometry.Space

end
