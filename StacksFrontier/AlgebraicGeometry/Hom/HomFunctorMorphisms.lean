module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHom
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.HomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Morphisms from an algebraic space into the relative Hom functor

In the relative Hom situation of Stacks 08JT — a morphism `f : X ⟶ base` of algebraic spaces
over a scheme `S` of a big fppf site and two quasi-coherent `𝒪_X`-modules `F`, `G` — the
functor `Hom(F, G)` of Stacks 08JT is a functor on the schemes over `base`.  Read as a presheaf
on the whole big fppf site of `S` it sends a scheme `V` to the set of *pairs* `(h, u)` of a
morphism `h : V ⟶ base` and a homomorphism `u : F_V ⟶ G_V` of the modules pulled back to
`X ×_{base, h} V`.  Stacks 0D3S identifies the morphisms of fppf sheaves from an algebraic
space `T` into that presheaf with the pairs of the same shape at `T`:

`Mor(T, Hom(F, G)) = {(h, u) | h : T ⟶ base, u : F_T ⟶ G_T}`,

the subscript `T` now meaning pullback to the algebraic space `X ×_{base, h} T`.

## Main definitions

* `AlgebraicGeometry.Space.pointSpaceMap`: the morphism of algebraic spaces determined by a
  scheme-valued point of an algebraic space.
* `AlgebraicGeometry.Space.HomSituation.spaceHomAt`: `Hom_{𝒪_{X_T}}(F_T, G_T)` for an
  algebraic space `T` over the base, and
  `AlgebraicGeometry.Space.HomSituation.homOverSpaceMap` the pullback of such a homomorphism
  along a morphism of algebraic spaces over the base.
* `AlgebraicGeometry.Space.HomSituation.homOverSpaceFunctor`: **the relative Hom functor of
  Stacks 08JT indexed by the algebraic spaces over the base**, of which the Hom functor on the
  test schemes is the restriction.
* `AlgebraicGeometry.Space.HomSituation.HomOver`: **the pair `(h, u)` of Stacks 0D3S at a
  scheme of the big fppf site**, with `HomOver.restrict` its restriction along a morphism of
  schemes.
* `AlgebraicGeometry.Space.HomSituation.homSitePresheaf`: **`Hom(F, G)` read as a presheaf on
  the big fppf site of `S`**, whose sections over a scheme are those pairs.
* `AlgebraicGeometry.Space.HomSituation.homSitePresheafToBase`: the canonical morphism to the
  base, which forgets the homomorphism.
* `AlgebraicGeometry.Space.HomSituation.SpaceHomPair`: **the pair `(h, u)` of Stacks 0D3S at an
  algebraic space** — the right-hand side of the identification of Stacks 0D3S.
* `AlgebraicGeometry.Space.HomSituation.morOfSpaceHom`: **the morphism of presheaves
  `T ⟶ Hom(F, G)` determined by such a pair**, which sends a scheme-valued point `a` of `T` to
  the pair `(h ∘ a, a^*u)`.  This is the construction the source gives for the inverse of the
  identification of Stacks 0D3S.
* `AlgebraicGeometry.Space.HomSituation.baseOfMor`: **the morphism `T ⟶ base` underlying a
  morphism of presheaves `T ⟶ Hom(F, G)`**, obtained by composing with the canonical morphism
  to the base.
* `AlgebraicGeometry.Space.HomSituation.EtaleHomDescent`: the fullness clause of Stacks 04W8
  for the relative Hom functor over the algebraic spaces over the base, proved for every Hom
  situation by `AlgebraicGeometry.Space.HomSituation.etaleHomDescent`.
* `AlgebraicGeometry.Space.HomSituation.morOver` and
  `AlgebraicGeometry.Space.HomSituation.morOverEquiv`: the morphism of presheaves over a fixed
  `h : T ⟶ base` determined by a homomorphism over `h`, and **the identification of
  Stacks 0D3S over `h`** it gives.

## Main results

* `AlgebraicGeometry.Space.HomSituation.homOverSpaceMap_id` and `…_comp`: pullback of
  homomorphisms over the algebraic spaces over the base is functorial, which is what makes
  `homSitePresheaf` a presheaf.
* `AlgebraicGeometry.Space.HomSituation.homOverOfPair_restrict` and
  `AlgebraicGeometry.Space.HomSituation.morApp_restrict`: the pair at a scheme-valued point is
  compatible with restriction, in the two directions needed.
* `AlgebraicGeometry.Space.HomSituation.morApp_toBase`: the pair that a morphism of presheaves
  cuts out at a scheme-valued point `a` lies over `baseOfMor v ∘ a`.
* `AlgebraicGeometry.Space.HomSituation.baseOfMor_morOfSpaceHom`: **the first component of the
  pair is recovered from the morphism of presheaves** — the morphism to the base underlying
  `morOfSpaceHom (h, u)` is `h`.  This is the half of the identification of Stacks 0D3S that
  needs no descent, and it is proved outright.
* `AlgebraicGeometry.Space.HomSituation.homOverSpaceMap_injective`: **pullback of
  homomorphisms along a surjective étale morphism of algebraic spaces over the base is
  injective** — the faithfulness clause of Stacks 04W8 for the one-member étale covering of
  base changes, proved outright — and
  `AlgebraicGeometry.Space.HomSituation.homOver_eq_of_restrict_eq`, the resulting
  separatedness of the Hom presheaf along a surjective étale morphism of schemes.
* `AlgebraicGeometry.Space.exists_pointCover`: a scheme-valued point of an algebraic space is
  covered by a surjective étale scheme atlas, the atlas being relatively representable.
* `AlgebraicGeometry.Space.HomSituation.bijective_morOver`: **for a fixed `h : T ⟶ base` the
  map `u ↦ morOfSpaceHom (h, u)` is a bijection onto the morphisms of presheaves lying
  over `h`** — the fibres of the identification of Stacks 0D3S.

## Implementation notes

**How Stacks 0D3S is assembled.**  Stacks 0D3S asserts an identification
`Mor(T, Hom(F, G)) = {(h, u)}`.  This file supplies both sides of it — the morphisms of
presheaves on the left, the pairs `SpaceHomPair` on the right — the map from right to left
(`morOfSpaceHom`) and the map `baseOfMor` recovering the first component on the left, and
proves the two steps the identification is made of: `baseOfMor_morOfSpaceHom`, that the first
component is recovered, and `bijective_morOver`, that for a fixed first component the second
components correspond bijectively to the morphisms of presheaves lying over it.  The
identification itself, `AlgebraicGeometry.Space.HomSituation.bijective_morOfSpaceHom`, is in
`StacksFrontier/AlgebraicGeometry/Hom/HomFunctorEtaleDescent.lean`.

The second step is the descent step of the source's proof.  Injectivity is faithfulness of
descent of homomorphisms of modules along the covering `X_U ⟶ X_T` of base changes cut out by
a scheme atlas `U ⟶ T` of Stacks 0262, which is
`AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering`.
Surjectivity is fullness of that descent, which is named here as
`AlgebraicGeometry.Space.HomSituation.EtaleHomDescent` and proved for every Hom situation by
`AlgebraicGeometry.Space.HomSituation.etaleHomDescent` in
`StacksFrontier/AlgebraicGeometry/Hom/HomFunctorEtaleDescent.lean`.  The route takes
the first component through the projection to the base rather than by descent, so it does not
use the sheaf property of `Hom(F, G)` (Stacks 08JV).

**Pairs are compared in explicit form.**  A pair is a structure whose second field is typed
through the first, so two pairs are compared heterogeneously; and the unifier, faced with two
Hom sets over two morphisms to the base that are equal but not syntactically so, tries
congruence, fails on the second fields, and then unfolds the Hom set to homomorphisms of
sheaves of modules.  Every comparison below therefore puts the pairs into explicit
`⟨b, α⟩` form first — `AlgebraicGeometry.Space.HomSituation.HomOver.restrict_eq_mk`,
`…homOverOfPair_eq_mk`, `…HomOver.exists_mk_eq` — so that the two morphisms to the base are
*syntactically* equal, and only then applies
`AlgebraicGeometry.Space.HomSituation.HomOver.hom_eq_of_mk_eq`.  For the same reason an
intermediate heterogeneous equality is always bound with `have` before it is used, never
elaborated against an expected type, and the goals about morphisms of algebraic spaces over
the base are closed by explicit rewriting rather than by `simp`.

**The pair is a structure, not a dependent sum.**  `HomOver` and `SpaceHomPair` are structures
with a `toBase` field and a homomorphism typed through it, which is the idiom of
`AlgebraicGeometry.Space.HilbertFamilyOver` for the Hilbert functor of Stacks 0CZY and of the
quotient functor of Stacks 09TR; equality of two of them is `HomOver.ext`, heterogeneous in the
second field because its type depends on the first.  All functoriality of `homSitePresheaf` is
deduced from the single transport lemma
`AlgebraicGeometry.Space.HomSituation.homOverSpaceMap_heq` and its one-sided form
`…homOverSpaceMap_heq_left`.

**Why the sections live one universe up, and the source is lifted.**  The homomorphisms of
`𝒪`-modules on an algebraic space form a `Type (u + 1)`, so `homSitePresheaf` is a presheaf of
`Type (u + 1)` while the functor of points of an algebraic space is a presheaf of `Type u`.
The morphisms of Stacks 0D3S are therefore morphisms out of `T.obj ⋙ uliftFunctor`, exactly as
`AlgebraicGeometry.Space.hilbertPresheafToBase` lifts the base for the same reason.  Morphisms
of presheaves between presheaves that happen to be sheaves are the morphisms of the category of
sheaves, so nothing is lost by not bundling either side as an object of `Sheaf`; this is the
convention of `StacksFrontier.AlgebraicGeometry.Spaces.Presentation` throughout.

**Pullback of homomorphisms is factored through an abstract comparison.**
`AlgebraicGeometry.Space.HomSituation.homOverSpaceMap` is `CategoryTheory.Functor.conjHom` of
`AlgebraicGeometry.Space.HomSituation.spaceBaseChangeComparison`, a named isomorphism, and its
two functoriality laws are read off the functor laws of `homOverSpaceFunctor` rather than
proved in place; `spaceHomAt` is a `def` and not an `abbrev`.  Both choices are the ones
`StacksFrontier.AlgebraicGeometry.Quot.RelativeHom` documents and are forced by the same cost:
with the Hom set reducible the unifier unfolds it to the underlying homomorphisms of sheaves of
modules and compares those structurally, which does not terminate within the heartbeat limit.
Injectivity of that pullback is likewise read off the comparison, through
`CategoryTheory.Functor.conjHom_injective`, which is stated over abstract categories so that
the concrete Hom set is never unfolded.

**The coherence `hc`.**  `AlgebraicGeometry.Space.ModulePushforwardCoherence` is what makes
pullback of homomorphisms functorial at all.  It is not an assumption:
`AlgebraicGeometry.Space.modulePushforwardCoherence` inhabits it with no hypothesis, which is
what `AlgebraicGeometry.Space.HomSituation.homOverSpaceFunctor` uses.  The statements below
which still take it as `hc` take it for uniformity with
`AlgebraicGeometry.Space.HomSituation.homFunctor`, whose interface is unchanged, and nothing
depends on which inhabitant is supplied.

**Quasi-coherence** of the two modules is standing data of the situation and is not used below:
the homomorphisms are taken in all `𝒪`-modules, as in
`StacksFrontier.AlgebraicGeometry.Quot.RelativeHom`.

## References

* [Stacks Project, Tag 0D3S](https://stacks.math.columbia.edu/tag/0D3S)
* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 0CZY](https://stacks.math.columbia.edu/tag/0CZY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- **Conjugation by a comparison is injective as soon as the further functor is injective on
the Hom set.**  The two ends of `CategoryTheory.Functor.conjHom` are isomorphisms and cancel.

The statement is over abstract categories on purpose: a consumer applies it to a comparison it
has already named, so the unifier is never asked to compare the concrete Hom sets, which for
homomorphisms of sheaves of modules it does structurally. -/
theorem conjHom_injective {C : Type*} {D₁ : Type*} {D₂ : Type*}
    [Category* C] [Category* D₁] [Category* D₂]
    {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {M N : C}
    (hL : ∀ α β : P₁.obj M ⟶ P₁.obj N, L.map α = L.map β → α = β) :
    Function.Injective (conjHom e (M := M) (N := N)) := by
  have key : ∀ γ : P₁.obj M ⟶ P₁.obj N,
      e.inv.app M ≫ conjHom e γ ≫ e.hom.app N = L.map γ := by
    intro γ
    simp [conjHom]
  intro α β hαβ
  refine hL α β ?_
  rw [← key α, ← key β, hαβ]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe u

/-! ### Scheme-valued points as morphisms of algebraic spaces -/

section Points

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The morphism of algebraic spaces `V ⟶ T` determined by a scheme-valued point of `T` at a
scheme `V` of the big fppf site. -/
def pointSpaceMap {T : AlgebraicSpaces B S hS} {V : BigFppfOver B S hS}
    (x : T.1.obj (Opposite.op V)) : (schemeSpaceFunctor B S hS).obj V ⟶ T :=
  ObjectProperty.homMk (yonedaEquiv.symm x)

/-- The morphism of a point is the morphism it corresponds to under Yoneda. -/
theorem pointSpaceMap_hom {T : AlgebraicSpaces B S hS} {V : BigFppfOver B S hS}
    (x : T.1.obj (Opposite.op V)) :
    (pointSpaceMap (T := T) x).hom = yonedaEquiv.symm x := rfl

/-- The point of an algebraic space underlying the morphism of a point is that point. -/
@[simp]
theorem pointSpaceMap_yonedaEquiv {T : AlgebraicSpaces B S hS} {V : BigFppfOver B S hS}
    (p : (schemeSpaceFunctor B S hS).obj V ⟶ T) :
    pointSpaceMap (T := T) (yonedaEquiv p.hom) = p :=
  ObjectProperty.hom_ext _ (Equiv.symm_apply_apply _ _)

/-- The morphism of a restricted point is the morphism of the point, precomposed with the
morphism of schemes. -/
theorem pointSpaceMap_naturality {T : AlgebraicSpaces B S hS} {V V' : (BigFppfOver B S hS)ᵒᵖ}
    (g : V ⟶ V') (x : T.1.obj V) :
    pointSpaceMap (T := T) (T.1.map g x) =
      (schemeSpaceFunctor B S hS).map g.unop ≫ pointSpaceMap (T := T) x := by
  refine ObjectProperty.hom_ext _ ?_
  have h : T.1.map g (yonedaEquiv (yonedaEquiv.symm x)) =
      yonedaEquiv (yoneda.map g.unop ≫ yonedaEquiv.symm x) :=
    yonedaEquiv_naturality (yonedaEquiv.symm x) g.unop
  rw [Equiv.apply_symm_apply] at h
  exact (congrArg yonedaEquiv.symm h).trans (Equiv.symm_apply_apply _ _)

/-- A restricted scheme-valued point, read through Yoneda. -/
theorem map_point_eq {T : AlgebraicSpaces B S hS} {V V' : BigFppfOver B S hS}
    (x : T.1.obj (Opposite.op V)) (g : V' ⟶ V) :
    T.1.map g.op x = yonedaEquiv (yoneda.map g ≫ yonedaEquiv.symm x) := by
  rw [← yonedaEquiv_naturality (yonedaEquiv.symm x) g, Equiv.apply_symm_apply]

/-- **A scheme-valued point of an algebraic space is covered by a surjective étale scheme
atlas.**  Given an atlas `a : U ⟶ T` which is surjective and étale after every representable
base change and a point `y : V ⟶ T`, the fibre product `V ×_T U` is represented by a scheme
`P` of the site, because the atlas is relatively representable; the projection `P ⟶ V` is
again surjective and étale, and `y` restricted to `P` factors through the atlas.

This is the form in which a statement proved at one chart of an algebraic space is transported
to every scheme-valued point of it. -/
theorem exists_pointCover {T : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS}
    {a : yoneda.obj U ⟶ T.1}
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    {V : BigFppfOver B S hS} (y : yoneda.obj V ⟶ T.1) :
    ∃ (P : BigFppfOver B S hS) (π : P ⟶ V) (ρ : P ⟶ U),
      IsSurjective B S hS (yoneda.map π) ∧ IsEtale B S hS (yoneda.map π) ∧
        yoneda.map ρ ≫ a = yoneda.map π ≫ y := by
  refine ⟨hetale.rep.pullback y, hetale.rep.snd y, yoneda.preimage (hetale.rep.fst y),
    isSurjective_yoneda_map B S hS _ (hsurj.property_snd y),
    (isEtale_iff_presheaf_of_yoneda B S hS _).2
      ((presheaf_yoneda_map_etale_iff B S hS _).2 (hetale.property_snd y)), ?_⟩
  rw [yoneda.map_preimage]
  exact (hetale.rep.isPullback y).w

end Points

namespace HomSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (s : HomSituation B S hS)

/-! ### The relative Hom functor indexed by the algebraic spaces over the base -/

/-- The set of homomorphisms `F_T ⟶ G_T` for an algebraic space `T` over the base, the two
modules being pulled back along the projection `X ×_{base} T ⟶ X`. -/
def spaceHomAt (T : Over s.base) : Type (u + 1) :=
  moduleHomOverObj s.F s.G ((overBaseChangeFunctor s.f).obj T)

/-- The set of homomorphisms over an algebraic space over the base is the set of homomorphisms
of the two pulled-back modules. -/
theorem spaceHomAt_eq (T : Over s.base) :
    s.spaceHomAt T =
      ((modulePullback B S hS (overProjection s.f T)).obj s.F ⟶
        (modulePullback B S hS (overProjection s.f T)).obj s.G) :=
  rfl

/-- **The relative Hom functor of Stacks 08JT, indexed by the algebraic spaces over the
base.**  Its value at `T ⟶ base` is `Hom_{𝒪_{X_T}}(F_T, G_T)` and its action is pullback of
homomorphisms.  The relative Hom functor on the test *schemes* over the base is this one
restricted along the inclusion of those into the algebraic spaces over the base.

The pseudofunctoriality of the direct images of Stacks 03LU, which makes pullback of
homomorphisms functorial, is supplied by `AlgebraicGeometry.Space.modulePushforwardCoherence`
and so is not a hypothesis. -/
@[stacks 08JT "the Hom functor indexed by the algebraic spaces over the base"]
def homOverSpaceFunctor : (Over s.base)ᵒᵖ ⥤ Type (u + 1) :=
  (overBaseChangeFunctor s.f).op ⋙
    moduleHomOver (modulePushforwardCoherence B S hS) s.F s.G

/-- The comparison of the base change to `U` with the base change to `T` followed by the
inverse image along `X_U ⟶ X_T`, as an isomorphism of the two inverse-image functors. -/
def spaceBaseChangeComparison {U T : Over s.base} (g : U ⟶ T) :
    modulePullback B S hS (overProjection s.f U) ≅
      modulePullback B S hS (overProjection s.f T) ⋙
        modulePullback B S hS (overBaseChangeMap s.f g) :=
  modulePullbackTriangle B S hS (overBaseChangeMap_comp_projection s.f g)

/-- The comparison is the one the base change over `X` of the algebraic spaces over the base
provides. -/
theorem spaceBaseChangeComparison_eq {U T : Over s.base} (g : U ⟶ T) :
    s.spaceBaseChangeComparison g =
      modulePullbackTriangle B S hS (Over.w ((overBaseChangeFunctor s.f).map g)) :=
  rfl

/-- Pullback of a homomorphism `F_T ⟶ G_T` along a morphism `U ⟶ T` of algebraic spaces over
the base, as a function. -/
def homOverSpaceMap {U T : Over s.base} (g : U ⟶ T) (α : s.spaceHomAt T) : s.spaceHomAt U :=
  Functor.conjHom (s.spaceBaseChangeComparison g) α

/-- Pullback of homomorphisms is conjugation by the comparison of the two base changes. -/
theorem homOverSpaceMap_def {U T : Over s.base} (g : U ⟶ T) :
    s.homOverSpaceMap g = Functor.conjHom (s.spaceBaseChangeComparison g) :=
  rfl

/-- Pullback of a homomorphism is the action of the relative Hom functor over the algebraic
spaces.

The coherence is not used: the functor supplies its own, by
`AlgebraicGeometry.Space.modulePushforwardCoherence`.  It is still bound, under the name
`_hc`, so that the signature matches the two functoriality laws deduced from this lemma. -/
theorem homOverSpaceMap_eq_map (_hc : ModulePushforwardCoherence B S hS) {U T : Over s.base}
    (g : U ⟶ T) :
    s.homOverSpaceFunctor.map g.op = TypeCat.ofHom (s.homOverSpaceMap g) := by
  rw [s.homOverSpaceMap_def g, s.spaceBaseChangeComparison_eq g]
  rfl

/-- **Pullback of homomorphisms along the identity is the identity.** -/
theorem homOverSpaceMap_id (hc : ModulePushforwardCoherence B S hS) (T : Over s.base)
    (α : s.spaceHomAt T) : s.homOverSpaceMap (𝟙 T) α = α := by
  have h : TypeCat.ofHom (s.homOverSpaceMap (𝟙 T)) =
      𝟙 (s.homOverSpaceFunctor.obj (Opposite.op T)) := by
    rw [← s.homOverSpaceMap_eq_map hc]
    exact s.homOverSpaceFunctor.map_id (Opposite.op T)
  have h2 : ConcreteCategory.hom (TypeCat.ofHom (s.homOverSpaceMap (𝟙 T))) α =
      ConcreteCategory.hom (𝟙 (s.homOverSpaceFunctor.obj (Opposite.op T))) α := by
    rw [h]
    rfl
  exact h2

/-- **Pullback of homomorphisms is compatible with composition.** -/
theorem homOverSpaceMap_comp (hc : ModulePushforwardCoherence B S hS) {V U T : Over s.base}
    (g : V ⟶ U) (h : U ⟶ T) (α : s.spaceHomAt T) :
    s.homOverSpaceMap (g ≫ h) α = s.homOverSpaceMap g (s.homOverSpaceMap h α) := by
  have h' : TypeCat.ofHom (s.homOverSpaceMap (g ≫ h)) =
      TypeCat.ofHom (s.homOverSpaceMap h) ≫ TypeCat.ofHom (s.homOverSpaceMap g) := by
    rw [← s.homOverSpaceMap_eq_map hc, ← s.homOverSpaceMap_eq_map hc,
      ← s.homOverSpaceMap_eq_map hc]
    exact s.homOverSpaceFunctor.map_comp h.op g.op
  have h2 : ConcreteCategory.hom (TypeCat.ofHom (s.homOverSpaceMap (g ≫ h))) α =
      ConcreteCategory.hom (TypeCat.ofHom (s.homOverSpaceMap h) ≫
        TypeCat.ofHom (s.homOverSpaceMap g)) α := by
    rw [h']
  exact h2

/-- **Pullback of homomorphisms transported along equalities of algebraic spaces over the
base.**  This is the one transport lemma from which every compatibility below is deduced: the
set of homomorphisms over an algebraic space over the base depends on its structure morphism,
so two restrictions along morphisms that agree only after such an equality are compared
heterogeneously. -/
theorem homOverSpaceMap_heq {U T U' T' : Over s.base} (g : U ⟶ T) (g' : U' ⟶ T')
    (hU : U = U') (hT : T = T') (hg : g ≫ eqToHom hT = eqToHom hU ≫ g')
    (α : s.spaceHomAt T) (α' : s.spaceHomAt T') (hα : α ≍ α') :
    s.homOverSpaceMap g α ≍ s.homOverSpaceMap g' α' := by
  subst hU
  subst hT
  obtain rfl := eq_of_heq hα
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hg
  subst hg
  rfl

/-- Pullback of homomorphisms transported along an equality of the sources only. -/
theorem homOverSpaceMap_heq_left {U U' T : Over s.base} (g : U ⟶ T) (g' : U' ⟶ T)
    (hU : U = U') (hg : g = eqToHom hU ≫ g') (α : s.spaceHomAt T) :
    s.homOverSpaceMap g α ≍ s.homOverSpaceMap g' α := by
  subst hU
  simp only [eqToHom_refl, Category.id_comp] at hg
  subst hg
  rfl

/-! ### Pullback of homomorphisms along a surjective étale morphism is injective -/

/-- **The base change of a surjective étale morphism of algebraic spaces over the base is a
one-member étale covering of the base changes.**  The square of the base changes is cartesian
by `AlgebraicGeometry.Space.isPullback_overBaseChangeMap`, and both surjectivity on points
(Stacks 03MH) and étaleness (Stacks 0466) are stable under base change. -/
theorem isEtaleCovering_overBaseChangeMap {U T : Over s.base} (g : U ⟶ T)
    (hsurj : IsSurjective B S hS g.left.hom) (hetale : IsEtale B S hS g.left.hom) :
    IsEtaleCovering B S hS (fun _ : PUnit.{u + 1} => (overBaseChange s.f U).1)
      (fun _ => (overBaseChangeMap s.f g).hom) where
  target_isAlgebraicSpace := (overBaseChange s.f T).property
  source_isAlgebraicSpace _ := (overBaseChange s.f U).property
  etale _ :=
    isEtale_of_isPullback B S hS (overInclusion s.f U) (overBaseChangeMap s.f g) g.left
      (overInclusion s.f T) (isPullback_overBaseChangeMap s.f g).flip hetale
  jointly_surjective :=
    (isJointlySurjective_const_iff B S hS (overBaseChangeMap s.f g).hom).2
      (isSurjective_of_isPullback B S hS (isPullback_overBaseChangeMap s.f g).flip hsurj)

/-- **Pullback of homomorphisms along a surjective étale morphism of algebraic spaces over the
base is injective.**  This is the faithfulness half of Stacks 04W8 for the one-member étale
covering `X_U ⟶ X_T` of the base changes, and it is unconditional: a homomorphism of
`𝒪`-modules is determined by its inverse images along an étale covering, by
`AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering`.

Injectivity is read off the abstract comparison
`AlgebraicGeometry.Space.HomSituation.spaceBaseChangeComparison` through
`CategoryTheory.Functor.conjHom_injective`, so the concrete Hom set is never unfolded. -/
theorem homOverSpaceMap_injective {U T : Over s.base} (g : U ⟶ T)
    (hsurj : IsSurjective B S hS g.left.hom) (hetale : IsEtale B S hS g.left.hom) :
    Function.Injective (s.homOverSpaceMap g) := by
  have hcov := s.isEtaleCovering_overBaseChangeMap g hsurj hetale
  refine Functor.conjHom_injective (M := s.F) (N := s.G) (s.spaceBaseChangeComparison g)
    fun α β hαβ => ?_
  exact QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering B S hS
    (fun _ : PUnit.{u + 1} => overBaseChange s.f U) (fun _ => overBaseChangeMap s.f g) hcov
    α β fun _ => hαβ

/-! ### The Hom functor as a presheaf on the big fppf site -/

/-- **The pair `(h, u)` of Stacks 0D3S at a scheme of the big fppf site**: a morphism from the
scheme to the base, read as a morphism of algebraic spaces, together with a homomorphism of the
two modules pulled back to the resulting base change.

This is the shape of `AlgebraicGeometry.Space.HilbertFamilyOver` for the Hilbert functor and of
the quotient functor's families over the schemes of the site. -/
structure HomOver (V : BigFppfOver B S hS) where
  /-- The morphism to the base the homomorphism lies over. -/
  toBase : (schemeSpaceFunctor B S hS).obj V ⟶ s.base
  /-- The homomorphism of the two modules base changed along it. -/
  hom : s.spaceHomAt (Over.mk toBase)

namespace HomOver

/-- Two pairs over a scheme of the site agree as soon as the morphisms to the base agree and
the homomorphisms agree over that.  The homomorphism is typed through the morphism to the base,
so its equality is heterogeneous. -/
theorem ext {V : BigFppfOver B S hS} {a b : s.HomOver V} (hbase : a.toBase = b.toBase)
    (hhom : a.hom ≍ b.hom) : a = b := by
  obtain ⟨ab, ah⟩ := a
  obtain ⟨bb, bh⟩ := b
  dsimp only at hbase
  subst hbase
  exact congrArg (fun y => (⟨ab, y⟩ : s.HomOver V)) (eq_of_heq hhom)

/-- Equal pairs over a scheme of the site have the same homomorphism, heterogeneously. -/
theorem hom_heq {V : BigFppfOver B S hS} {a b : s.HomOver V} (hab : a = b) : a.hom ≍ b.hom := by
  cases hab
  rfl

/-- The morphism of algebraic spaces over the base induced by a morphism of schemes of the site
and a morphism from the target to the base. -/
def restrictMap {V V' : BigFppfOver B S hS} (g : V' ⟶ V)
    (b : (schemeSpaceFunctor B S hS).obj V ⟶ s.base) :
    (Over.mk ((schemeSpaceFunctor B S hS).map g ≫ b) : Over s.base) ⟶ Over.mk b :=
  Over.homMk ((schemeSpaceFunctor B S hS).map g) rfl

/-- Restriction of a pair along a morphism of schemes of the site: both components are pulled
back. -/
def restrict {V V' : BigFppfOver B S hS} (x : s.HomOver V) (g : V' ⟶ V) : s.HomOver V' where
  toBase := (schemeSpaceFunctor B S hS).map g ≫ x.toBase
  hom := s.homOverSpaceMap (restrictMap s g x.toBase) x.hom

@[simp]
theorem restrict_toBase {V V' : BigFppfOver B S hS} (x : s.HomOver V) (g : V' ⟶ V) :
    (restrict s x g).toBase = (schemeSpaceFunctor B S hS).map g ≫ x.toBase := rfl

theorem restrict_hom {V V' : BigFppfOver B S hS} (x : s.HomOver V) (g : V' ⟶ V) :
    (restrict s x g).hom = s.homOverSpaceMap (restrictMap s g x.toBase) x.hom := rfl

/-- Restriction along the identity is the identity. -/
theorem restrict_id (hc : ModulePushforwardCoherence B S hS) (V : BigFppfOver B S hS)
    (x : s.HomOver V) : restrict s x (𝟙 V) = x := by
  have h₀ : (schemeSpaceFunctor B S hS).map (𝟙 V) ≫ x.toBase = x.toBase := by simp
  refine ext s h₀ ?_
  rw [restrict_hom]
  refine HEq.trans (homOverSpaceMap_heq_left s (restrictMap s (𝟙 V) x.toBase)
    (𝟙 (Over.mk x.toBase)) (congrArg Over.mk h₀)
    (Over.OverMorphism.ext (by simp [restrictMap])) x.hom) ?_
  exact heq_of_eq (homOverSpaceMap_id s hc _ x.hom)

/-- Restriction along a composite is the composite of the restrictions. -/
theorem restrict_comp (hc : ModulePushforwardCoherence B S hS)
    {V V' V'' : BigFppfOver B S hS} (g : V' ⟶ V) (h : V'' ⟶ V') (x : s.HomOver V) :
    restrict s (restrict s x g) h = restrict s x (h ≫ g) := by
  have h₀ : (schemeSpaceFunctor B S hS).map h ≫ (schemeSpaceFunctor B S hS).map g ≫ x.toBase =
      (schemeSpaceFunctor B S hS).map (h ≫ g) ≫ x.toBase := by simp
  refine ext s h₀ ?_
  rw [restrict_hom, restrict_hom, restrict_hom]
  refine HEq.trans ?_ (HEq.symm (homOverSpaceMap_heq_left s
    (restrictMap s (h ≫ g) x.toBase)
    (restrictMap s h ((schemeSpaceFunctor B S hS).map g ≫ x.toBase) ≫ restrictMap s g x.toBase)
    (congrArg Over.mk h₀.symm) (Over.OverMorphism.ext (by simp [restrictMap]))
    x.hom))
  exact heq_of_eq (homOverSpaceMap_comp s hc _ _ x.hom).symm

/-- Restriction of a pair, written out as a pair.  Stated over an abstract morphism to the
base and an abstract homomorphism, so that rewriting with it puts an equation of pairs in a
shape whose two morphisms to the base are *syntactically* equal; that is what lets
`AlgebraicGeometry.Space.HomSituation.HomOver.hom_eq_of_mk_eq` compare the two homomorphisms
without the unifier ever unfolding the Hom set. -/
theorem restrict_eq_mk {V V' : BigFppfOver B S hS}
    (b : (schemeSpaceFunctor B S hS).obj V ⟶ s.base) (α : s.spaceHomAt (Over.mk b))
    (g : V' ⟶ V) :
    restrict s ⟨b, α⟩ g =
      ⟨(schemeSpaceFunctor B S hS).map g ≫ b, s.homOverSpaceMap (restrictMap s g b) α⟩ :=
  rfl

/-- **Two pairs with one and the same morphism to the base have equal homomorphisms as soon as
the pairs are equal.**  Both homomorphisms live in the Hom set over that one morphism, so no
transport is involved; the morphism to the base is abstract, which is what keeps the comparison
of the two Hom sets a comparison of two applications of the same function. -/
theorem hom_eq_of_mk_eq {V : BigFppfOver B S hS}
    {b : (schemeSpaceFunctor B S hS).obj V ⟶ s.base} {α β : s.spaceHomAt (Over.mk b)}
    (e : (⟨b, α⟩ : s.HomOver V) = ⟨b, β⟩) : α = β :=
  eq_of_heq (hom_heq s e)

/-- A pair lying over a given morphism to the base *is* that morphism paired with a
homomorphism over it.  This replaces a pair by an explicit pair, which is what lets the two
lemmas above apply to it. -/
theorem exists_mk_eq {V : BigFppfOver B S hS} (z : s.HomOver V)
    {b : (schemeSpaceFunctor B S hS).obj V ⟶ s.base} (hb : z.toBase = b) :
    ∃ α : s.spaceHomAt (Over.mk b), z = ⟨b, α⟩ := by
  obtain ⟨zb, zh⟩ := z
  dsimp only at hb
  subst hb
  exact ⟨zh, rfl⟩

end HomOver

/-- **Two restrictions of one pair along two morphisms of schemes with a common source have
equal homomorphisms as soon as the two restrictions are equal.**  The two homomorphisms are
typed through the two composites to the base, which differ, so they are compared
heterogeneously.

The pairs are put in explicit form before the comparison for the reason
`AlgebraicGeometry.Space.HomSituation.HomOver.restrict_eq_mk` records. -/
theorem homOverSpaceMap_heq_of_restrict_eq {V R : BigFppfOver B S hS}
    (b : (schemeSpaceFunctor B S hS).obj V ⟶ s.base) (α : s.spaceHomAt (Over.mk b))
    (σ τ : R ⟶ V)
    (e : HomOver.restrict s ⟨b, α⟩ σ = HomOver.restrict s ⟨b, α⟩ τ) :
    s.homOverSpaceMap (HomOver.restrictMap s σ b) α ≍
      s.homOverSpaceMap (HomOver.restrictMap s τ b) α := by
  rw [HomOver.restrict_eq_mk, HomOver.restrict_eq_mk] at e
  have h := HomOver.hom_heq s e
  exact h

/-- **A pair over a scheme of the site is determined by its restriction along a surjective
étale morphism of schemes.**  The two morphisms to the base being equal, the two homomorphisms
live in one Hom set, and pullback along the induced surjective étale morphism `X_{V'} ⟶ X_V`
of base changes is injective by
`AlgebraicGeometry.Space.HomSituation.homOverSpaceMap_injective`. -/
theorem homOver_eq_of_restrict_eq {V V' : BigFppfOver B S hS} (π : V' ⟶ V)
    (hsurj : IsSurjective B S hS (yoneda.map π)) (hetale : IsEtale B S hS (yoneda.map π))
    {z z' : s.HomOver V} (hbase : z.toBase = z'.toBase)
    (h : HomOver.restrict s z π = HomOver.restrict s z' π) : z = z' := by
  obtain ⟨zb, zh⟩ := z
  obtain ⟨zb', zh'⟩ := z'
  dsimp only at hbase
  subst hbase
  rw [HomOver.restrict_eq_mk, HomOver.restrict_eq_mk] at h
  exact HomOver.ext s rfl (heq_of_eq (s.homOverSpaceMap_injective
    (HomOver.restrictMap s π zb) hsurj hetale (HomOver.hom_eq_of_mk_eq s h)))

/-- **Stacks 0D3S.**  The relative Hom functor `Hom(F, G)` read as a presheaf on the big fppf
site of `S`: a section over a scheme `V` is a morphism `V ⟶ base` together with a homomorphism
`F_V ⟶ G_V` of the modules pulled back to `X ×_{base} V`, and restriction pulls back both.

The sections live one universe above the site because the homomorphisms of `𝒪`-modules on an
algebraic space do. -/
def homSitePresheaf (hc : ModulePushforwardCoherence B S hS) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) where
  obj V := s.HomOver V.unop
  map g := TypeCat.ofHom fun x => HomOver.restrict s x g.unop
  map_id V := by
    apply ConcreteCategory.hom_ext
    intro x
    exact HomOver.restrict_id s hc V.unop x
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (HomOver.restrict_comp s hc g.unop h.unop x).symm

/-- **Stacks 0D3S.**  The canonical morphism from the Hom presheaf to the base, which forgets
the homomorphism and keeps the morphism to the base.  Its target is the universe lift of the
base for the reason the sections live one universe up. -/
def homSitePresheafToBase (hc : ModulePushforwardCoherence B S hS) :
    s.homSitePresheaf hc ⟶ s.base.1 ⋙ uliftFunctor.{u + 1, u} where
  app V := TypeCat.ofHom fun x => ULift.up (yonedaEquiv x.toBase.hom)
  naturality := by
    intro V V' g
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (yonedaEquiv_naturality x.toBase.hom g.unop).symm

/-! ### The pair at an algebraic space, and the morphism of presheaves it determines -/

/-- **The pair `(h, u)` of Stacks 0D3S at an algebraic space**: a morphism `h : T ⟶ base` of
algebraic spaces over `S` together with a homomorphism `u : F_T ⟶ G_T` of the two modules
pulled back to `X ×_{base, h} T`. -/
structure SpaceHomPair (T : AlgebraicSpaces B S hS) where
  /-- The morphism to the base. -/
  toBase : T ⟶ s.base
  /-- The homomorphism of the two base-changed modules. -/
  hom : s.spaceHomAt (Over.mk toBase)

/-- The morphism of algebraic spaces over the base given by a scheme-valued point of an
algebraic space over the base. -/
def pointOver {T : AlgebraicSpaces B S hS} (h : T ⟶ s.base) {V : BigFppfOver B S hS}
    (x : T.1.obj (Opposite.op V)) :
    (Over.mk (pointSpaceMap (T := T) x ≫ h) : Over s.base) ⟶ Over.mk h :=
  Over.homMk (pointSpaceMap (T := T) x) rfl

/-- The pair at a scheme-valued point of `T` cut out by a pair at the algebraic space `T`: the
point `a` goes to `(h ∘ a, a^*u)`, which is the assignment the source gives for the inverse
construction of Stacks 0D3S. -/
def homOverOfPair {T : AlgebraicSpaces B S hS} (p : s.SpaceHomPair T)
    {V : BigFppfOver B S hS} (x : T.1.obj (Opposite.op V)) : s.HomOver V :=
  ⟨pointSpaceMap (T := T) x ≫ p.toBase, s.homOverSpaceMap (s.pointOver p.toBase x) p.hom⟩

/-- The pair cut out at a scheme-valued point, written out as a pair, for a pair at the
algebraic space given in explicit form. -/
theorem homOverOfPair_eq_mk {T : AlgebraicSpaces B S hS} (b : T ⟶ s.base)
    (α : s.spaceHomAt (Over.mk b)) {V : BigFppfOver B S hS} (x : T.1.obj (Opposite.op V)) :
    s.homOverOfPair ⟨b, α⟩ x =
      ⟨pointSpaceMap (T := T) x ≫ b, s.homOverSpaceMap (s.pointOver b x) α⟩ :=
  rfl

/-- Restricting a scheme-valued point and taking the pair of a pair at the algebraic space
commute. -/
theorem homOverOfPair_restrict (hc : ModulePushforwardCoherence B S hS)
    {T : AlgebraicSpaces B S hS} (p : s.SpaceHomPair T) {V V' : (BigFppfOver B S hS)ᵒᵖ}
    (g : V ⟶ V') (x : T.1.obj V) :
    (⟨pointSpaceMap (T := T) (T.1.map g x) ≫ p.toBase,
        s.homOverSpaceMap (s.pointOver p.toBase (T.1.map g x)) p.hom⟩ : s.HomOver V'.unop) =
      HomOver.restrict s ⟨pointSpaceMap (T := T) x ≫ p.toBase,
        s.homOverSpaceMap (s.pointOver p.toBase x) p.hom⟩ g.unop := by
  have hb : pointSpaceMap (T := T) (T.1.map g x) ≫ p.toBase =
      (schemeSpaceFunctor B S hS).map g.unop ≫ pointSpaceMap (T := T) x ≫ p.toBase := by
    rw [pointSpaceMap_naturality g x, Category.assoc]
  have hU : (Over.mk (pointSpaceMap (T := T) (T.1.map g x) ≫ p.toBase) : Over s.base) =
      Over.mk ((schemeSpaceFunctor B S hS).map g.unop ≫ pointSpaceMap (T := T) x ≫ p.toBase) :=
    congrArg Over.mk hb
  have hg : s.pointOver p.toBase (T.1.map g x) =
      eqToHom hU ≫ (HomOver.restrictMap s g.unop (pointSpaceMap (T := T) x ≫ p.toBase) ≫
        s.pointOver p.toBase x) := by
    refine Over.OverMorphism.ext ?_
    simp only [Over.comp_left, HomOver.restrictMap, pointOver, Over.homMk_left,
      Over.eqToHom_left, eqToHom_refl, Category.id_comp]
    exact pointSpaceMap_naturality g x
  have h1 := homOverSpaceMap_heq_left s (s.pointOver p.toBase (T.1.map g x))
    (HomOver.restrictMap s g.unop (pointSpaceMap (T := T) x ≫ p.toBase) ≫
      s.pointOver p.toBase x) hU hg p.hom
  refine HomOver.ext s hb ?_
  rw [HomOver.restrict_hom]
  exact HEq.trans h1 (heq_of_eq (homOverSpaceMap_comp s hc
    (HomOver.restrictMap s g.unop (pointSpaceMap (T := T) x ≫ p.toBase))
    (s.pointOver p.toBase x) p.hom))

/-- Restricting a scheme-valued point and taking the pair commute, stated for a morphism of
schemes of the site rather than for its opposite. -/
theorem homOverOfPair_map_eq_restrict (hc : ModulePushforwardCoherence B S hS)
    {T : AlgebraicSpaces B S hS} (p : s.SpaceHomPair T) {V V' : BigFppfOver B S hS}
    (g : V' ⟶ V) (x : T.1.obj (Opposite.op V)) :
    s.homOverOfPair p (T.1.map g.op x) = HomOver.restrict s (s.homOverOfPair p x) g :=
  s.homOverOfPair_restrict hc p g.op x

/-- **The morphism of presheaves `T ⟶ Hom(F, G)` determined by a pair `(h, u)` at an algebraic
space.**  A scheme-valued point `a` of `T` is sent to the pair `(h ∘ a, a^*u)`. -/
def morOfSpaceHom (hc : ModulePushforwardCoherence B S hS) {T : AlgebraicSpaces B S hS}
    (p : s.SpaceHomPair T) : T.1 ⋙ uliftFunctor.{u + 1, u} ⟶ s.homSitePresheaf hc where
  app V := TypeCat.ofHom fun x => s.homOverOfPair p x.down
  naturality := fun V V' g => by
    apply ConcreteCategory.hom_ext
    intro y
    obtain ⟨x⟩ := y
    exact s.homOverOfPair_restrict hc p g x

/-! ### The morphism to the base underlying a morphism of presheaves -/

/-- The pair at a scheme-valued point of `T` cut out by a morphism of presheaves into the Hom
presheaf. -/
def morApp (hc : ModulePushforwardCoherence B S hS) {T : AlgebraicSpaces B S hS}
    (v : T.1 ⋙ uliftFunctor.{u + 1, u} ⟶ s.homSitePresheaf hc)
    {V : (BigFppfOver B S hS)ᵒᵖ} (x : T.1.obj V) : s.HomOver V.unop :=
  ConcreteCategory.hom (v.app V) (ULift.up x)

/-- Restriction commutes with taking the pair at a scheme-valued point. -/
theorem morApp_restrict (hc : ModulePushforwardCoherence B S hS)
    {T : AlgebraicSpaces B S hS} (v : T.1 ⋙ uliftFunctor.{u + 1, u} ⟶ s.homSitePresheaf hc)
    {V V' : (BigFppfOver B S hS)ᵒᵖ} (g : V ⟶ V') (x : T.1.obj V) :
    s.morApp hc v (T.1.map g x) = HomOver.restrict s (s.morApp hc v x) g.unop := by
  have h : ConcreteCategory.hom
        ((T.1 ⋙ uliftFunctor.{u + 1, u}).map g ≫ v.app V') (ULift.up x) =
      ConcreteCategory.hom (v.app V ≫ (s.homSitePresheaf hc).map g) (ULift.up x) := by
    rw [v.naturality g]
  exact h

/-- Restriction commutes with taking the pair at a scheme-valued point, stated for a morphism
of schemes of the site rather than for its opposite. -/
theorem morApp_map_eq_restrict (hc : ModulePushforwardCoherence B S hS)
    {T : AlgebraicSpaces B S hS} (v : T.1 ⋙ uliftFunctor.{u + 1, u} ⟶ s.homSitePresheaf hc)
    {V V' : BigFppfOver B S hS} (g : V' ⟶ V) (x : T.1.obj (Opposite.op V)) :
    s.morApp hc v (T.1.map g.op x) = HomOver.restrict s (s.morApp hc v x) g :=
  s.morApp_restrict hc v g.op x

/-- The pair that the morphism of presheaves of a pair at the algebraic space cuts out at a
scheme-valued point is the pair at that point. -/
theorem morApp_morOfSpaceHom (hc : ModulePushforwardCoherence B S hS)
    {T : AlgebraicSpaces B S hS} (p : s.SpaceHomPair T) {V : (BigFppfOver B S hS)ᵒᵖ}
    (x : T.1.obj V) : s.morApp hc (s.morOfSpaceHom hc p) x = s.homOverOfPair p x :=
  rfl

/-- **Two morphisms of presheaves into the Hom presheaf agree as soon as they cut out the same
pair at every scheme-valued point.** -/
theorem mor_ext (hc : ModulePushforwardCoherence B S hS) {T : AlgebraicSpaces B S hS}
    {v v' : T.1 ⋙ uliftFunctor.{u + 1, u} ⟶ s.homSitePresheaf hc}
    (h : ∀ (V : BigFppfOver B S hS) (x : T.1.obj (Opposite.op V)),
      s.morApp hc v x = s.morApp hc v' x) :
    v = v' :=
  NatTrans.ext (funext fun V => ConcreteCategory.hom_ext _ _ fun y => by
    obtain ⟨x⟩ := y
    exact h V.unop x)

/-- **The morphism to the base underlying a morphism of presheaves into the Hom presheaf.**  It
is the composite with `AlgebraicGeometry.Space.HomSituation.homSitePresheafToBase`, read as a
morphism of algebraic spaces; no descent is involved. -/
def baseOfMor (hc : ModulePushforwardCoherence B S hS) {T : AlgebraicSpaces B S hS}
    (v : T.1 ⋙ uliftFunctor.{u + 1, u} ⟶ s.homSitePresheaf hc) : T ⟶ s.base :=
  ObjectProperty.homMk
    { app := fun V => TypeCat.ofHom fun x => yonedaEquiv (s.morApp hc v x).toBase.hom
      naturality := fun V V' g => by
        apply ConcreteCategory.hom_ext
        intro x
        change yonedaEquiv (s.morApp hc v (T.1.map g x)).toBase.hom =
          ConcreteCategory.hom (s.base.1.map g) (yonedaEquiv (s.morApp hc v x).toBase.hom)
        rw [morApp_restrict s hc v g x]
        change yonedaEquiv
            ((schemeSpaceFunctor B S hS).map g.unop ≫ (s.morApp hc v x).toBase).hom =
          ConcreteCategory.hom (s.base.1.map g) (yonedaEquiv (s.morApp hc v x).toBase.hom)
        exact (yonedaEquiv_naturality (s.morApp hc v x).toBase.hom g.unop).symm }

/-- The pair at a scheme-valued point lies over the morphism to the base that the morphism of
presheaves determines. -/
theorem morApp_toBase (hc : ModulePushforwardCoherence B S hS) {T : AlgebraicSpaces B S hS}
    (v : T.1 ⋙ uliftFunctor.{u + 1, u} ⟶ s.homSitePresheaf hc)
    {V : (BigFppfOver B S hS)ᵒᵖ} (x : T.1.obj V) :
    (s.morApp hc v x).toBase = pointSpaceMap (T := T) x ≫ s.baseOfMor hc v := by
  refine ObjectProperty.hom_ext _ (yonedaEquiv.injective ?_)
  rw [show (pointSpaceMap (T := T) x ≫ s.baseOfMor hc v).hom =
      (pointSpaceMap (T := T) x).hom ≫ (s.baseOfMor hc v).hom from rfl]
  exact congrArg (fun y => yonedaEquiv (s.morApp hc v y).toBase.hom)
    (Equiv.apply_symm_apply yonedaEquiv x).symm

/-- **The morphism to the base is recovered from the morphism of presheaves**: for a pair
`(h, u)` the morphism underlying `morOfSpaceHom (h, u)` is `h`, for any inhabitant `hc` of the
coherence data.  This is the step of Stacks 0D3S that needs no descent; the identification
itself is `AlgebraicGeometry.Space.HomSituation.bijective_morOfSpaceHom`. -/
theorem baseOfMor_morOfSpaceHom (hc : ModulePushforwardCoherence B S hS)
    {T : AlgebraicSpaces B S hS} (p : s.SpaceHomPair T) :
    s.baseOfMor hc (s.morOfSpaceHom hc p) = p.toBase := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V =>
    ConcreteCategory.hom_ext _ _ fun x => ?_))
  change yonedaEquiv (pointSpaceMap (T := T) x ≫ p.toBase).hom =
    ConcreteCategory.hom (p.toBase.hom.app V) x
  rw [show (pointSpaceMap (T := T) x ≫ p.toBase).hom =
      (pointSpaceMap (T := T) x).hom ≫ p.toBase.hom from rfl]
  exact congrArg (fun y => ConcreteCategory.hom (p.toBase.hom.app V) y)
    (Equiv.apply_symm_apply yonedaEquiv x)

/-! ### The identification of Stacks 0D3S -/

/-- **The fullness clause of Stacks 04W8 for the relative Hom functor over the algebraic
spaces over the base.**  Along a surjective étale morphism `g : U ⟶ T` of algebraic spaces
over the base, a homomorphism `w : F_U ⟶ G_U` whose two restrictions along a kernel pair of
`g` agree is the restriction of a homomorphism `F_T ⟶ G_T`.

This is descent of homomorphisms of modules along the one-member étale covering `X_U ⟶ X_T` of
base changes, which is the fullness half of Stacks 04W8 for that covering; the faithfulness half
is `AlgebraicGeometry.Space.HomSituation.homOverSpaceMap_injective`.  Every Hom situation
satisfies it: `AlgebraicGeometry.Space.HomSituation.etaleHomDescent`, in
`StacksFrontier/AlgebraicGeometry/Hom/HomFunctorEtaleDescent.lean`, proves it by identifying the
kernel pair of `g` with the fibre product of the covering with itself.  It is named here so that
the descent step below can be stated in this file, before that proof. -/
structure EtaleHomDescent : Prop where
  /-- Descent of a homomorphism over a chart which is invariant under a kernel pair. -/
  exists_homOverSpaceMap_eq : ∀ {U T : Over s.base} (g : U ⟶ T),
    IsSurjective B S hS g.left.hom → IsEtale B S hS g.left.hom →
    ∀ {R : Over s.base} (p q : R ⟶ U),
      IsPullback p.left.hom q.left.hom g.left.hom g.left.hom →
      ∀ w : s.spaceHomAt U, s.homOverSpaceMap p w = s.homOverSpaceMap q w →
        ∃ α : s.spaceHomAt T, s.homOverSpaceMap g α = w

/-- **The morphism of presheaves `T ⟶ Hom(F, G)` over a fixed `h : T ⟶ base` determined by a
homomorphism `u : F_T ⟶ G_T`.**  It is `AlgebraicGeometry.Space.HomSituation.morOfSpaceHom` of
the pair `(h, u)`, together with the proof that it lies over `h`; that proof is
`AlgebraicGeometry.Space.HomSituation.baseOfMor_morOfSpaceHom`. -/
def morOver (hc : ModulePushforwardCoherence B S hS) {T : AlgebraicSpaces B S hS}
    (h : T ⟶ s.base) (u : s.spaceHomAt (Over.mk h)) :
    {v : T.1 ⋙ uliftFunctor.{u + 1, u} ⟶ s.homSitePresheaf hc // s.baseOfMor hc v = h} :=
  ⟨s.morOfSpaceHom hc ⟨h, u⟩, s.baseOfMor_morOfSpaceHom hc ⟨h, u⟩⟩

/-- The point-morphism of an atlas point is surjective and étale when the atlas is. -/
private theorem pointOver_surjective_and_etale {T : AlgebraicSpaces B S hS} (h : T ⟶ s.base)
    {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ T.1}
    (hasurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    {x : T.1.obj (Opposite.op U)} (hx : yonedaEquiv.symm x = a) :
    IsSurjective B S hS (s.pointOver h x).left.hom ∧ IsEtale B S hS (s.pointOver h x).left.hom := by
  have hL : (s.pointOver h x).left.hom = a := hx
  rw [hL]
  exact ⟨isSurjective_of_presheafSurjective B S hS a hasurj,
    (isEtale_iff_presheaf_of_yoneda B S hS a).2 haetale⟩

/-- **The second component of the pair is determined by the morphism of presheaves.**  Two
homomorphisms over `h` giving the same morphism of presheaves give the same pair at a
surjective étale scheme atlas of `T`, hence agree, pullback along the induced covering
`X_U ⟶ X_T` being injective.  Only faithfulness of descent is used, so no descent hypothesis
is needed. -/
theorem injective_morOver (hc : ModulePushforwardCoherence B S hS)
    {T : AlgebraicSpaces B S hS} (h : T ⟶ s.base) : Function.Injective (s.morOver hc h) := by
  intro u u' e
  obtain ⟨U, a, hasurj, haetale⟩ := T.property.exists_atlas
  obtain ⟨x, hx⟩ := yonedaEquiv.symm.surjective a
  have e1 : s.morOfSpaceHom hc (⟨h, u⟩ : s.SpaceHomPair T) = s.morOfSpaceHom hc ⟨h, u'⟩ :=
    congrArg Subtype.val e
  have e2 : s.homOverOfPair (⟨h, u⟩ : s.SpaceHomPair T) x = s.homOverOfPair ⟨h, u'⟩ x :=
    congrArg (fun v => s.morApp hc v x) e1
  rw [s.homOverOfPair_eq_mk h u x, s.homOverOfPair_eq_mk h u' x] at e2
  have hae := s.pointOver_surjective_and_etale h hasurj haetale hx
  exact s.homOverSpaceMap_injective (s.pointOver h x) hae.1 hae.2 (HomOver.hom_eq_of_mk_eq s e2)

/-- **A morphism of presheaves lying over `h` comes from a homomorphism over `h` at a
surjective étale scheme atlas of `T`.**  The pair the morphism of presheaves cuts out at the
atlas point lies over the atlas, and its two restrictions along a kernel pair of the atlas
agree, that kernel pair being supplied by Stacks 0262; descent of homomorphisms along the
resulting covering of base changes then produces the homomorphism over `h`. -/
theorem exists_spaceHom_of_chart (hc : ModulePushforwardCoherence B S hS)
    (hd : s.EtaleHomDescent) {T : AlgebraicSpaces B S hS} (h : T ⟶ s.base)
    (v : T.1 ⋙ uliftFunctor.{u + 1, u} ⟶ s.homSitePresheaf hc) (hv : s.baseOfMor hc v = h)
    {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ T.1}
    (hasurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haetale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    {x : T.1.obj (Opposite.op U)} (hx : yonedaEquiv.symm x = a) :
    ∃ u : s.spaceHomAt (Over.mk h),
      s.homOverOfPair (⟨h, u⟩ : s.SpaceHomPair T) x = s.morApp hc v x := by
  have hae := s.pointOver_surjective_and_etale h hasurj haetale hx
  have hbase : (s.morApp hc v x).toBase = pointSpaceMap (T := T) x ≫ h := by
    rw [s.morApp_toBase hc v x, hv]
  obtain ⟨w, hw⟩ := HomOver.exists_mk_eq s (s.morApp hc v x) hbase
  obtain ⟨R, σ, τ, hR⟩ := exists_kernelPair_of_etale_atlas B S hS a haetale
  have hστ : T.1.map σ.op x = T.1.map τ.op x := by
    rw [map_point_eq, map_point_eq, hx, hR.w]
  have hστ' : (schemeSpaceFunctor B S hS).map τ ≫ pointSpaceMap (T := T) x =
      (schemeSpaceFunctor B S hS).map σ ≫ pointSpaceMap (T := T) x := by
    refine ObjectProperty.hom_ext _ ?_
    change yoneda.map τ ≫ yonedaEquiv.symm x = yoneda.map σ ≫ yonedaEquiv.symm x
    rw [hx, hR.w]
  have hq : (schemeSpaceFunctor B S hS).map τ ≫ (pointSpaceMap (T := T) x ≫ h) =
      (schemeSpaceFunctor B S hS).map σ ≫ (pointSpaceMap (T := T) x ≫ h) := by
    rw [← Category.assoc, ← Category.assoc, hστ']
  obtain ⟨q, hqleft⟩ : ∃ q : (Over.mk ((schemeSpaceFunctor B S hS).map σ ≫
        (pointSpaceMap (T := T) x ≫ h)) : Over s.base) ⟶
        Over.mk (pointSpaceMap (T := T) x ≫ h),
      q.left = (schemeSpaceFunctor B S hS).map τ :=
    ⟨Over.homMk ((schemeSpaceFunctor B S hS).map τ) hq, rfl⟩
  have hpb : IsPullback
      (HomOver.restrictMap s σ (pointSpaceMap (T := T) x ≫ h)).left.hom q.left.hom
      (s.pointOver h x).left.hom (s.pointOver h x).left.hom := by
    rw [hqleft, show (s.pointOver h x).left.hom = a from hx]
    change IsPullback (yoneda.map σ) (yoneda.map τ) a a
    exact hR
  have hres : HomOver.restrict s
        (⟨pointSpaceMap (T := T) x ≫ h, w⟩ : s.HomOver U) σ =
      HomOver.restrict s ⟨pointSpaceMap (T := T) x ≫ h, w⟩ τ := by
    rw [← hw, ← s.morApp_map_eq_restrict hc v σ x, ← s.morApp_map_eq_restrict hc v τ x, hστ]
  have hqheq : s.homOverSpaceMap q w ≍
      s.homOverSpaceMap (HomOver.restrictMap s τ (pointSpaceMap (T := T) x ≫ h)) w :=
    s.homOverSpaceMap_heq_left q
      (HomOver.restrictMap s τ (pointSpaceMap (T := T) x ≫ h))
      (congrArg Over.mk hq.symm)
      (Over.OverMorphism.ext (by
        rw [hqleft, Over.comp_left, Over.eqToHom_left, eqToHom_refl, Category.id_comp]
        rfl)) w
  have hσheq :=
    s.homOverSpaceMap_heq_of_restrict_eq (pointSpaceMap (T := T) x ≫ h) w σ τ hres
  have hheq : s.homOverSpaceMap (HomOver.restrictMap s σ (pointSpaceMap (T := T) x ≫ h)) w ≍
      s.homOverSpaceMap q w := hσheq.trans (HEq.symm hqheq)
  have hcompat := eq_of_heq hheq
  obtain ⟨u, hu⟩ := hd.exists_homOverSpaceMap_eq (s.pointOver h x) hae.1 hae.2
    (HomOver.restrictMap s σ (pointSpaceMap (T := T) x ≫ h)) q hpb w hcompat
  refine ⟨u, ?_⟩
  rw [s.homOverOfPair_eq_mk h u x, hu, hw]

/-- **Every morphism of presheaves lying over `h` comes from a homomorphism over `h`.**  The
homomorphism is produced at a surjective étale scheme atlas of `T` by
`AlgebraicGeometry.Space.HomSituation.exists_spaceHom_of_chart`; at an arbitrary scheme-valued
point of `T` the two pairs then agree because they agree after restriction to the cover of that
point by the atlas, which is
`AlgebraicGeometry.Space.exists_pointCover`, and a pair is determined by such a
restriction. -/
theorem surjective_morOver (hc : ModulePushforwardCoherence B S hS) (hd : s.EtaleHomDescent)
    {T : AlgebraicSpaces B S hS} (h : T ⟶ s.base) : Function.Surjective (s.morOver hc h) := by
  rintro ⟨v, hv⟩
  obtain ⟨U, a, hasurj, haetale⟩ := T.property.exists_atlas
  obtain ⟨x, hx⟩ := yonedaEquiv.symm.surjective a
  obtain ⟨u, hstep1⟩ := s.exists_spaceHom_of_chart hc hd h v hv hasurj haetale hx
  refine ⟨u, Subtype.ext (s.mor_ext hc (v := s.morOfSpaceHom hc ⟨h, u⟩) (v' := v)
    fun V z => ?_)⟩
  rw [s.morApp_morOfSpaceHom hc ⟨h, u⟩ z]
  obtain ⟨P, π, ρ, hπsurj, hπetale, hcomm⟩ :=
    exists_pointCover hasurj haetale (yonedaEquiv.symm z)
  have hptz : T.1.map π.op z = T.1.map ρ.op x := by
    rw [map_point_eq, map_point_eq, hx]
    exact congrArg yonedaEquiv hcomm.symm
  refine s.homOver_eq_of_restrict_eq π hπsurj hπetale ?_ ?_
  · rw [s.morApp_toBase hc v z, hv]
    rfl
  · calc HomOver.restrict s (s.homOverOfPair (⟨h, u⟩ : s.SpaceHomPair T) z) π
        = s.homOverOfPair (⟨h, u⟩ : s.SpaceHomPair T) (T.1.map π.op z) :=
          (s.homOverOfPair_map_eq_restrict hc _ π z).symm
      _ = s.homOverOfPair (⟨h, u⟩ : s.SpaceHomPair T) (T.1.map ρ.op x) := by rw [hptz]
      _ = HomOver.restrict s (s.homOverOfPair (⟨h, u⟩ : s.SpaceHomPair T) x) ρ :=
          s.homOverOfPair_map_eq_restrict hc _ ρ x
      _ = HomOver.restrict s (s.morApp hc v x) ρ := by rw [hstep1]
      _ = s.morApp hc v (T.1.map ρ.op x) := (s.morApp_map_eq_restrict hc v ρ x).symm
      _ = s.morApp hc v (T.1.map π.op z) := by rw [hptz]
      _ = HomOver.restrict s (s.morApp hc v z) π := s.morApp_map_eq_restrict hc v π z

/-- **The fibres of the identification of Stacks 0D3S.**  For a fixed morphism `h : T ⟶ base`
of algebraic spaces over `S`, the assignment `u ↦ morOfSpaceHom (h, u)` is a *bijection* from
the homomorphisms `u : F_T ⟶ G_T` of the two modules pulled back to `X ×_{base, h} T` onto the
morphisms of presheaves `T ⟶ Hom(F, G)` lying over `h`.

Injectivity is faithfulness of descent of homomorphisms of modules along the étale covering
`X_U ⟶ X_T` cut out by a scheme atlas `U ⟶ T` of Stacks 0262.  Surjectivity is fullness of that
descent, stated here for any proof `hd` of it; every Hom situation has one,
`AlgebraicGeometry.Space.HomSituation.etaleHomDescent`.  The identification
`Mor(T, Hom(F, G)) = {(h, u) | h : T ⟶ base, u : F_T ⟶ G_T}` of Stacks 0D3S that this gives is
`AlgebraicGeometry.Space.HomSituation.bijective_morOfSpaceHom`, in
`StacksFrontier/AlgebraicGeometry/Hom/HomFunctorEtaleDescent.lean`. -/
theorem bijective_morOver (hc : ModulePushforwardCoherence B S hS) (hd : s.EtaleHomDescent)
    {T : AlgebraicSpaces B S hS} (h : T ⟶ s.base) : Function.Bijective (s.morOver hc h) :=
  ⟨s.injective_morOver hc h, s.surjective_morOver hc hd h⟩

/-- **The identification of Stacks 0D3S over a fixed morphism to the base**, as an equivalence:
the homomorphisms `F_T ⟶ G_T` are the morphisms of presheaves `T ⟶ Hom(F, G)` lying over `h`.
Its forward direction is the source's construction
`AlgebraicGeometry.Space.HomSituation.morOfSpaceHom`, and it is an equivalence by
`AlgebraicGeometry.Space.HomSituation.bijective_morOver`. -/
def morOverEquiv (hc : ModulePushforwardCoherence B S hS) (hd : s.EtaleHomDescent)
    {T : AlgebraicSpaces B S hS} (h : T ⟶ s.base) :
    s.spaceHomAt (Over.mk h) ≃
      {v : T.1 ⋙ uliftFunctor.{u + 1, u} ⟶ s.homSitePresheaf hc // s.baseOfMor hc v = h} :=
  Equiv.ofBijective (s.morOver hc h) (s.bijective_morOver hc hd h)

end HomSituation

end AlgebraicGeometry.Space

end

