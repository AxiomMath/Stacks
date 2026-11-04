module

public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# Limit preservation of the relative Hom functor

In the standing data of Stacks 08JT — a morphism `f : X ⟶ base` of algebraic spaces over a
scheme `S` of a big fppf site and two quasi-coherent `𝒪_X`-modules `F`, `G` — the relative Hom
functor `Hom(F, G) : (Sch/base)ᵒᵖ ⥤ Sets` of
`StacksFrontier/AlgebraicGeometry/Quot/RelativeHom.lean` sends a test scheme `T` over the base to
`Hom_{𝒪_{X_T}}(F_T, G_T)`.  Stacks 08K4 asserts that this functor is *limit preserving* in the
sense of Stacks 049J, provided `F` is of finite presentation and `f` is quasi-compact and
quasi-separated: for every cofiltered inverse system of affine test schemes whose limit of
underlying schemes is the vertex `T`,

`Hom_{𝒪_{X_T}}(F_T, G_T) = colim_i Hom_{𝒪_{X_{T_i}}}(F_{T_i}, G_{T_i})`.

This file supplies the elementwise criterion for limit preservation, the *reduction step* of the
proof of Stacks 08K4 — limit preservation passes to a presheaf cut out as the equalizer of two
maps between limit-preserving presheaves — and the assertion of Stacks 08K4 itself.

## Main definitions

* `AlgebraicGeometry.Space.HomSituation.testSchemeFunctor`: the underlying-scheme functor on the
  test schemes over the base, which is the functor limit preservation is tested along.
* `AlgebraicGeometry.Space.HomSituation.IsLimitPreservingHom`: **Stacks 08K4**, the assertion
  that the relative Hom functor of a finitely presented module along a quasi-compact and
  quasi-separated morphism is limit preserving.

## Main results

* `AlgebraicGeometry.exists_eq_map_of_isColimit_mapCocone` and
  `AlgebraicGeometry.eventually_eq_of_isColimit_mapCocone`: the two elementwise consequences of a
  colimit presentation of the sections over the vertex of a cofiltered cone — every section comes
  from a stage, and two sections at a stage agreeing over the vertex agree at a later stage.
* `AlgebraicGeometry.nonempty_isColimit_mapCocone_of_exists_of_eventually_eq`: those two
  conditions are also sufficient.
* `AlgebraicGeometry.limitPreserving_of_isEqualizer`: **limit preservation passes to an
  equalizer.**  If `a : P ⟶ Q` is injective at every object, equalizes `b₁, b₂ : Q ⟶ R` and has
  for image exactly the sections equalized by them, and `Q` and `R` are limit preserving, then so
  is `P`.
* `AlgebraicGeometry.Space.HomSituation.isLimitPreservingHom_of_isEqualizer`: **Stacks 08K4
  reduced to an equalizer presentation of the relative Hom functor.**

## Implementation notes

**What remains open.**  `AlgebraicGeometry.Space.HomSituation.IsLimitPreservingHom` is reduced,
not proved.  The source argues in three steps.  Step one base changes the standing data to a
stage of the system, which is Stacks 08JW and is available as
`AlgebraicGeometry.Space.HomSituation.homFunctorBaseChange`; the base being affine, the source
`X` is then quasi-compact and quasi-separated.  Step two chooses an affine scheme surjective and
étale over `X` (Stacks 03H6) and an affine scheme surjective and étale over `U ×_X U`, which is
quasi-compact because `X` is quasi-separated, and presents `Hom(F, G)` through Stacks 08K3 as the
equalizer of the two maps between the Hom functors of those two charts.  Step three is the affine
case: for `R → A`, two `A`-modules and a directed system of `R`-algebras with colimit `C`, the
comparison `colim Hom_{A ⊗_R C_i}(M ⊗_R C_i, N ⊗_R C_i) → Hom_{A ⊗_R C}(M ⊗_R C, N ⊗_R C)` is
bijective when `M` is of finite presentation over `A`, which is Stacks 05LI.

Only step two's *formal* content is proved here, and it is proved in the generality it has:
`AlgebraicGeometry.limitPreserving_of_isEqualizer` is a statement about three presheaves of sets
on an arbitrary category over schemes, with no module, no chart and no finiteness hypothesis in
it, and it is where filtered colimits of sets commuting with the finite limit defining the
equalizer is used.  Producing the equalizer presentation from Stacks 08K3 — whose statement is
elementwise over a covering family rather than a presentation of presheaves — and the affine case
of Stacks 05LI are both left open; no hypothesis is carried for either, so the reduction theorem
asks for the presentation and the limit preservation of the two chart presheaves as data.

**Finite presentation and quasi-compactness are part of the assertion, not of the reduction.**
`AlgebraicGeometry.Space.HomSituation.IsLimitPreservingHom` carries the three hypotheses of
Stacks 08K4 as implications, so that it states exactly the source's lemma; the reduction theorem
does not use them, because they enter only in the two steps left open — quasi-compactness and
quasi-separatedness through the choice of charts in step two, and finite presentation through
Stacks 05LI in step three.

**Limit preservation is tested against the underlying-scheme functor.**  As in Stacks 049J the
indexing category is cofiltered with objects in `Type (max w w')` and morphisms in `Type w'`, the
cone is tested in the category of schemes rather than in the test schemes over the base, and both
the stages and the vertex are required to be affine.  The sections of the relative Hom functor
lie in `Type (u + 1)`, the module universe of `AlgebraicGeometry.Space.HomSituation` being the
universe of the structure rings.  The two indexing universes are left free, which is the stronger
assertion; the instance faithful to the source is `w = w' = u`, a directed set being small, and
it is the only one its step three can reach, because passing from the limit of the test schemes
to the colimit of their rings asks the indexing category to lie in the scheme universe.

## References

* [Stacks Project, Tag 08K4](https://stacks.math.columbia.edu/tag/08K4)
* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
* [Stacks Project, Tag 08JW](https://stacks.math.columbia.edu/tag/08JW)
* [Stacks Project, Tag 08K3](https://stacks.math.columbia.edu/tag/08K3)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 05LI](https://stacks.math.columbia.edu/tag/05LI)
* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w w' z y

namespace AlgebraicGeometry

/-! ### The elementwise criterion for a cofiltered colimit of sections -/

section Criterion

variable {C : Type z} [Category.{y} C] {I : Type w} [Category.{w'} I]
  (F : Cᵒᵖ ⥤ Type v) (D : I ⥤ C) (c : Cone D)

/-- A section over the vertex of a cone comes from a stage, read off a colimit presentation of
the sections over the vertex. -/
theorem exists_eq_map_of_isColimit_mapCocone (h : IsColimit (F.mapCocone c.op))
    (x : F.obj (op c.pt)) :
    ∃ (i : I) (y : F.obj (op (D.obj i))), F.map (c.π.app i).op y = x := by
  obtain ⟨i, y, hy⟩ := Types.jointly_surjective_of_isColimit h x
  exact ⟨i.unop, y, hy⟩

/-- Two sections at a stage whose restrictions to the vertex of a cofiltered cone agree already
agree at a later stage, read off a colimit presentation of the sections over the vertex. -/
theorem eventually_eq_of_isColimit_mapCocone [IsCofiltered I]
    (h : IsColimit (F.mapCocone c.op)) (i : I) (x y : F.obj (op (D.obj i)))
    (hxy : F.map (c.π.app i).op x = F.map (c.π.app i).op y) :
    ∃ (j : I) (f : j ⟶ i), F.map (D.map f).op x = F.map (D.map f).op y := by
  obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' h x y).mp hxy
  exact ⟨j.unop, f.unop, hf⟩

/-- The sections over the vertex of a cofiltered cone are the colimit of the sections at the
stages as soon as every section over the vertex comes from a stage and two sections at a stage
agreeing over the vertex agree at a later stage. -/
theorem nonempty_isColimit_mapCocone_of_exists_of_eventually_eq [IsCofiltered I]
    (hsurj : ∀ x : F.obj (op c.pt),
      ∃ (i : I) (y : F.obj (op (D.obj i))), F.map (c.π.app i).op y = x)
    (hinj : ∀ (i : I) (x y : F.obj (op (D.obj i))),
      F.map (c.π.app i).op x = F.map (c.π.app i).op y →
        ∃ (j : I) (f : j ⟶ i), F.map (D.map f).op x = F.map (D.map f).op y) :
    Nonempty (IsColimit (F.mapCocone c.op)) := by
  refine ⟨Types.FilteredColimit.isColimitOf' (D.op ⋙ F) (F.mapCocone c.op) ?_ ?_⟩
  · intro x
    obtain ⟨i, y, hy⟩ := hsurj x
    exact ⟨op i, y, hy.symm⟩
  · intro i x y hxy
    obtain ⟨j, f, hf⟩ := hinj i.unop x y hxy
    exact ⟨op j, f.op, hf⟩

end Criterion

/-! ### Limit preservation passes to an equalizer -/

/-- **Limit preservation passes to an equalizer.**  Let `a : P ⟶ Q` and `b₁, b₂ : Q ⟶ R` be
morphisms of presheaves of sets such that at every object `a` is injective, `a` equalizes `b₁`
and `b₂`, and every section of `Q` equalized by `b₁` and `b₂` is a section of `P`.  If `Q` and
`R` are limit preserving then so is `P`.

This is where filtered colimits of sets commuting with the finite limit defining an equalizer is
used, and it is the formal content of the reduction of Stacks 08K4 to an affine chart. -/
theorem limitPreserving_of_isEqualizer {C : Type z} [Category.{y} C] (toScheme : C ⥤ Scheme.{u})
    {P Q R : Cᵒᵖ ⥤ Type v} (a : P ⟶ Q) (b₁ b₂ : Q ⟶ R)
    (hinj : ∀ Z, Function.Injective (a.app Z))
    (hequalizes : ∀ (Z : Cᵒᵖ) (p : P.obj Z), b₁.app Z (a.app Z p) = b₂.app Z (a.app Z p))
    (hlift : ∀ (Z : Cᵒᵖ) (q : Q.obj Z), b₁.app Z q = b₂.app Z q → ∃ p, a.app Z p = q)
    (hQ : LimitPreserving.{u, v, w, w', z} toScheme Q)
    (hR : LimitPreserving.{u, v, w, w', z} toScheme R) :
    LimitPreserving.{u, v, w, w', z} toScheme P := by
  intro I _ _ D c hc hD hC
  obtain ⟨hQc⟩ := hQ I D c hc hD hC
  obtain ⟨hRc⟩ := hR I D c hc hD hC
  refine nonempty_isColimit_mapCocone_of_exists_of_eventually_eq P D c ?_ ?_
  · intro x
    obtain ⟨i, q, hq⟩ := exists_eq_map_of_isColimit_mapCocone Q D c hQc (a.app (op c.pt) x)
    have hb : R.map (c.π.app i).op (b₁.app (op (D.obj i)) q) =
        R.map (c.π.app i).op (b₂.app (op (D.obj i)) q) := by
      rw [← NatTrans.naturality_apply b₁ (c.π.app i).op q,
        ← NatTrans.naturality_apply b₂ (c.π.app i).op q, hq]
      exact hequalizes _ x
    obtain ⟨j, f, hf⟩ := eventually_eq_of_isColimit_mapCocone R D c hRc i
      (b₁.app (op (D.obj i)) q) (b₂.app (op (D.obj i)) q) hb
    obtain ⟨p, hp⟩ := hlift (op (D.obj j)) (Q.map (D.map f).op q) (by
      rw [NatTrans.naturality_apply b₁ (D.map f).op q,
        NatTrans.naturality_apply b₂ (D.map f).op q]
      exact hf)
    refine ⟨j, p, hinj (op c.pt) ?_⟩
    have h₁ : a.app (op c.pt) (P.map (c.π.app j).op p) =
        Q.map (c.π.app j).op (a.app (op (D.obj j)) p) :=
      NatTrans.naturality_apply a (c.π.app j).op p
    have h₂ : Q.map (c.π.app j).op (Q.map (D.map f).op q) = Q.map (c.π.app i).op q := by
      rw [← Functor.map_comp_apply, ← op_comp, c.w f]
    rw [h₁, hp, h₂, hq]
  · intro i x y hxy
    have h : Q.map (c.π.app i).op (a.app (op (D.obj i)) x) =
        Q.map (c.π.app i).op (a.app (op (D.obj i)) y) := by
      rw [← NatTrans.naturality_apply a (c.π.app i).op x,
        ← NatTrans.naturality_apply a (c.π.app i).op y, hxy]
    obtain ⟨j, f, hf⟩ := eventually_eq_of_isColimit_mapCocone Q D c hQc i
      (a.app (op (D.obj i)) x) (a.app (op (D.obj i)) y) h
    refine ⟨j, f, hinj (op (D.obj j)) ?_⟩
    rw [NatTrans.naturality_apply a (D.map f).op x,
      NatTrans.naturality_apply a (D.map f).op y]
    exact hf

/-! ### Stacks 08K4 -/

namespace Space.HomSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The underlying scheme of a test scheme over the base of the standing data of Stacks 08JT.
Limit preservation of the relative Hom functor is tested along this functor. -/
abbrev testSchemeFunctor (s : HomSituation B S hS) : s.SchemesOver ⥤ Scheme.{u} :=
  CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base ⋙ BigFppfOver.toScheme B S hS

/-- The assertion of Stacks 08K4, as a predicate: the relative Hom functor `Hom(F, G)` of
Stacks 08JT is limit preserving in the sense of Stacks 049J when the source module is of finite
presentation and the structure morphism is quasi-compact and quasi-separated — for every
cofiltered inverse system of affine test schemes over the base whose limit of underlying schemes
is the vertex, the homomorphisms of the base-changed modules over the vertex are the filtered
colimit of those over the stages.

This is a *statement*, not a theorem: it carries no `@[stacks 08K4]` attribute, because nothing
here proves it outright. What is proved is
`AlgebraicGeometry.Space.HomSituation.isLimitPreservingHom_of_isEqualizer`, which establishes it
from an equalizer presentation of the relative Hom functor. -/
def IsLimitPreservingHom (hc : ModulePushforwardCoherence B S hS)
    (s : HomSituation B S hS) : Prop :=
  s.F.IsFinitePresentationOnSite →
    Space.IsQuasiCompact B S hS s.f.hom → Space.IsQuasiSeparated B S hS s.f.hom →
      LimitPreserving.{u, u + 1, w, w', u + 1} s.testSchemeFunctor (s.homFunctor hc)

/-- **Stacks 08K4, reduced to an equalizer presentation of the relative Hom functor.**  The
relative Hom functor of Stacks 08JT is limit preserving as soon as it is cut out, at every test
scheme over the base, as the equalizer of two maps between limit-preserving presheaves.

Stacks 08K3 supplies such a presentation from an affine scheme surjective and étale over the
source and an affine scheme surjective and étale over its self-overlap, which exist because the
structure morphism is quasi-compact and quasi-separated (Stacks 03H6), the two presheaves being
the relative Hom functors of those charts; their limit preservation is the affine case, which is
Stacks 05LI.  Neither the presentation nor the affine case is proved here, so both are asked for
as data; accordingly the three hypotheses of Stacks 08K4 are not used. -/
@[stacks 08K4 "reduced to the equalizer presentation of Stacks 08K3; that presentation and the \
affine case, Stacks 05LI, are not proved"]
theorem isLimitPreservingHom_of_isEqualizer (hc : ModulePushforwardCoherence B S hS)
    (s : HomSituation B S hS) {Q R : (s.SchemesOver)ᵒᵖ ⥤ Type (u + 1)}
    (a : s.homFunctor hc ⟶ Q) (b₁ b₂ : Q ⟶ R)
    (hinj : ∀ T, Function.Injective (a.app T))
    (hequalizes : ∀ (T : (s.SchemesOver)ᵒᵖ) (α : (s.homFunctor hc).obj T),
      b₁.app T (a.app T α) = b₂.app T (a.app T α))
    (hlift : ∀ (T : (s.SchemesOver)ᵒᵖ) (q : Q.obj T),
      b₁.app T q = b₂.app T q → ∃ α, a.app T α = q)
    (hQ : LimitPreserving.{u, u + 1, w, w', u + 1} s.testSchemeFunctor Q)
    (hR : LimitPreserving.{u, u + 1, w, w', u + 1} s.testSchemeFunctor R) :
    IsLimitPreservingHom.{u, w, w'} hc s :=
  fun _ _ _ =>
    limitPreserving_of_isEqualizer s.testSchemeFunctor a b₁ b₂ hinj hequalizes hlift hQ hR

end Space.HomSituation

end AlgebraicGeometry

end
