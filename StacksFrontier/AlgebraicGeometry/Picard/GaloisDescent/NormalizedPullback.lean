module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison

/-!
# Normalising an isomorphism `L ≅ a^* L` along a morphism to the base

Let `p : V ⟶ W` be a morphism of schemes, let `a : W ⟶ W` and `b : V ⟶ V` have a common
composite with `p`, `p ≫ a = d = b ≫ p`, and let `L` be a module on `W` whose restriction
`p^* L` is trivialised, `t : p^* L ≅ 𝒪_V`. The square gives a comparison `a^* ⋙ p^* ≅ p^* ⋙ b^*`,
both composites being the pullback along the diagonal `d`, and hence a canonical isomorphism

`p^* L ≅ p^* (a^* L)`,

namely `t` followed by `b^*` applied to `t⁻¹` and read through the comparison. An isomorphism
`L ≅ a^* L` is *normalised* when its restriction along `p` is this one, and the point of the
construction is that normalised isomorphisms **compose**: the composite of the normalised
isomorphisms for `a` and `a'`, read through the comparison `a'^* ⋙ a^* ≅ (a ≫ a')^*`, is the
normalised isomorphism for `a ≫ a'`.

That is the cocycle condition of Galois descent. It is what makes a Galois-fixed invertible
module on a scheme with a rational point carry a descent datum: a fixed Picard class supplies
an isomorphism `ℒ ≅ f_σ^* ℒ` for each `σ` separately and nothing pins the family down, but each
member becomes unique once its restriction to the rational point is prescribed, and the
normalised family is then automatically a cocycle.

## Main definitions

* `Stacks.Picard.pullbackCompEq` — the comparison `g^* ⋙ f^* ≅ (f ≫ g)^*`, with the composite
  named by a morphism and an equation rather than written out.
* `Stacks.Picard.pullbackCommIso` — the comparison `a^* ⋙ p^* ≅ p^* ⋙ b^*` of a commuting
  square.
* `Stacks.Picard.normalizedIso` — the normalisation construction, for an arbitrary pair of
  endofunctors intertwined by a functor.
* `Stacks.Picard.twistNormalizedIso` — its value at a commuting square of pullbacks and a
  trivialisation of `p^* L`.

## Main results

* `Stacks.Picard.pullbackComp_hom_app_comp` and `Stacks.Picard.pullbackCompEq_assoc` — the
  associativity coherence of `AlgebraicGeometry.Scheme.Modules.pullbackComp`, read at a module.
* `Stacks.Picard.pullbackCommIso_mul` — two commuting squares with the same vertical edge
  compose to the square of the composites.
* `Stacks.Picard.normalizedIso_eq_of_comp` — **normalised isomorphisms compose.**
* `Stacks.Picard.twistNormalizedIso_mul` — the same at a commuting square of pullbacks, which
  is the form the Galois cocycle takes.

## Implementation notes

**Why the composites are named.** Mathlib's associativity coherence
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity` compares the pullback along
`f ≫ g ≫ h` with the pullback along `(f ≫ g) ≫ h` through an `eqToHom`. The two morphisms are
definitionally equal, so that `eqToHom` is definitionally an identity — which is how
`Stacks.Picard.pullbackComp_hom_app_comp` is stated with no `eqToHom` in it — but the two
*expressions* are different, and `rw` and `calc` reject a step whose two sides are only
definitionally of the same type. Carrying each composite as a morphism with an equation, as
`Stacks.Picard.pullbackCompEq` does, keeps every expression in the chain syntactically the
same, and is why `Stacks.Picard.pullbackCommIso_mul` is a short sequence of rewrites rather
than a transport.

**Why the normalisation is stated for arbitrary functors.** The only inputs
`Stacks.Picard.normalizedIso_eq_of_comp` uses are the compatibility of the two comparisons with
the composition of the endofunctors (`hA`) and the compatibility of the second with the
trivialisations (`he`). At a commuting square of pullbacks the first is
`Stacks.Picard.pullbackCommIso_mul` and the second is
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp_eq`, so neither is proved twice.

## References

* [Stacks Project, Tag 0CDT](https://stacks.math.columbia.edu/tag/0CDT)
* [Stacks Project, Tag 0CDR](https://stacks.math.columbia.edu/tag/0CDR)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules (pullbackComp pullbackCongr pullbackUnitIso)

universe u

namespace Stacks.Picard

/-! ### Coherence of the comparison of a composite of pullbacks -/

/-- **The associativity coherence of the pullback comparison**, read at a module: the two ways
of identifying `f^* g^* h^* M` with `(f ≫ g ≫ h)^* M` agree. -/
theorem pullbackComp_hom_app_comp {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (M : Z.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M) ≫
        (pullbackComp f (g ≫ h)).hom.app M =
      (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (pullbackComp (f ≫ g) h).hom.app M := by
  have hp := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g h) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp] at hp
  have key : (pullbackComp f (g ≫ h)).inv.app M ≫
      (Scheme.Modules.pullback f).map ((pullbackComp g h).inv.app M) ≫
        (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
          (pullbackComp (f ≫ g) h).hom.app M = 𝟙 _ := hp
  have step := congrArg (fun z => (pullbackComp f (g ≫ h)).hom.app M ≫ z) key
  simp only [Iso.hom_inv_id_app_assoc] at step
  have final : (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M) ≫
      (Scheme.Modules.pullback f).map ((pullbackComp g h).inv.app M) ≫
        (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
          (pullbackComp (f ≫ g) h).hom.app M =
      (pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (pullbackComp (f ≫ g) h).hom.app M := by
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  exact (congrArg
    (fun z => (Scheme.Modules.pullback f).map ((pullbackComp g h).hom.app M) ≫ z)
    step).symm.trans final

/-- The comparison identifying the composite of two pullbacks with the pullback along a
morphism equal to the composite. -/
def pullbackCompEq {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (fg : W ⟶ Y)
    (h : f ≫ g = fg) :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f ≅ Scheme.Modules.pullback fg :=
  pullbackComp f g ≪≫ pullbackCongr h

/-- At the composite `f ≫ g` itself, `pullbackCompEq` is the comparison `pullbackComp f g`. -/
theorem pullbackCompEq_rfl {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) :
    pullbackCompEq f g (f ≫ g) rfl = pullbackComp f g := by
  simp [pullbackCompEq, Scheme.Modules.pullbackCongr]

/-- **The associativity coherence of the pullback comparison**, in the form where every
composite is named by a morphism and an equation. -/
theorem pullbackCompEq_assoc {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (gh : X ⟶ Z) (fg : W ⟶ Y) (fgh : W ⟶ Z) (hgh : g ≫ h = gh) (hfg : f ≫ g = fg)
    (h₁ : f ≫ gh = fgh) (h₂ : fg ≫ h = fgh) (M : Z.Modules) :
    (Scheme.Modules.pullback f).map ((pullbackCompEq g h gh hgh).hom.app M) ≫
        (pullbackCompEq f gh fgh h₁).hom.app M =
      (pullbackCompEq f g fg hfg).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (pullbackCompEq fg h fgh h₂).hom.app M := by
  subst hgh hfg h₁
  simp only [pullbackCompEq, Iso.trans_hom, NatTrans.comp_app, Scheme.Modules.pullbackCongr,
    eqToIso_refl, Iso.refl_hom, Category.comp_id]
  exact pullbackComp_hom_app_comp f g h M

/-! ### The comparison attached to a commuting square -/

variable {V W : Scheme.{u}}

/-- **The comparison attached to a commuting square of schemes.** For `p ≫ a = d = b ≫ p` the
two composites `a^* ⋙ p^*` and `p^* ⋙ b^*` are identified, both being the pullback along the
diagonal `d` of the square. -/
def pullbackCommIso (p : V ⟶ W) (a : W ⟶ W) (b : V ⟶ V) (d : V ⟶ W) (h₁ : p ≫ a = d)
    (h₂ : b ≫ p = d) :
    Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback p ≅
      Scheme.Modules.pullback p ⋙ Scheme.Modules.pullback b :=
  pullbackCompEq p a d h₁ ≪≫ (pullbackCompEq b p d h₂).symm

/-- At a module `M`, the comparison of a commuting square is the comparison `p^* a^* M ≅ d^* M`
followed by the inverse of the comparison `b^* p^* M ≅ d^* M`. -/
theorem pullbackCommIso_hom_app (p : V ⟶ W) (a : W ⟶ W) (b : V ⟶ V) (d : V ⟶ W)
    (h₁ : p ≫ a = d) (h₂ : b ≫ p = d) (M : W.Modules) :
    (pullbackCommIso p a b d h₁ h₂).hom.app M =
      (pullbackCompEq p a d h₁).hom.app M ≫ (pullbackCompEq b p d h₂).inv.app M :=
  rfl

/-- **Two commuting squares with the same vertical edge compose.** -/
theorem pullbackCommIso_mul (p : V ⟶ W) (a a' aa' : W ⟶ W) (b b' bb' : V ⟶ V)
    (d d' dd' : V ⟶ W) (ha : a ≫ a' = aa') (hb : b ≫ b' = bb')
    (h₁ : p ≫ a = d) (h₂ : b ≫ p = d) (h₁' : p ≫ a' = d') (h₂' : b' ≫ p = d')
    (h₁'' : p ≫ aa' = dd') (h₂'' : bb' ≫ p = dd') (M : W.Modules) :
    (Scheme.Modules.pullback p).map ((pullbackCompEq a a' aa' ha).hom.app M) ≫
        (pullbackCommIso p aa' bb' dd' h₁'' h₂'').hom.app M =
      (pullbackCommIso p a b d h₁ h₂).hom.app ((Scheme.Modules.pullback a').obj M) ≫
        (Scheme.Modules.pullback b).map
            ((pullbackCommIso p a' b' d' h₁' h₂').hom.app M) ≫
          (pullbackCompEq b b' bb' hb).hom.app ((Scheme.Modules.pullback p).obj M) := by
  have hbd : b ≫ d' = dd' := by rw [← h₂', ← Category.assoc, hb, h₂'']
  have hda : d ≫ a' = dd' := by rw [← h₁, Category.assoc, ha, h₁'']
  rw [pullbackCommIso_hom_app, pullbackCommIso_hom_app, pullbackCommIso_hom_app]
  apply (cancel_mono ((pullbackCompEq bb' p dd' h₂'').hom.app M)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
    pullbackCompEq_assoc p a a' aa' d dd' ha h₁ h₁'' hda M]
  rw [← pullbackCompEq_assoc b b' p d' bb' dd' h₂' hb hbd h₂'' M,
    ← CategoryTheory.Functor.map_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [pullbackCompEq_assoc b p a' d' d dd' h₁' h₂ hbd hda M, Iso.inv_hom_id_app_assoc]

/-! ### Normalising an isomorphism against a trivialisation -/

section Normalization

variable {C : Type*} [Category C] {D : Type*} [Category D]
  {F F' F'' : C ⥤ C} {G G' G'' : D ⥤ D} {P : C ⥤ D}

/-- **The normalisation of an isomorphism `L ≅ F.obj L` against a trivialisation of `P.obj L`.**
Given an intertwiner `A : F ⋙ P ≅ P ⋙ G`, an isomorphism `t : P.obj L ≅ O` and a
trivialisation `e : G.obj O ≅ O`, the isomorphism `P.obj L ≅ P.obj (F.obj L)` obtained by
transporting `t` through `G` and reading the result through `A`. -/
def normalizedIso (A : F ⋙ P ≅ P ⋙ G) {L : C} {O : D} (t : P.obj L ≅ O) (e : G.obj O ≅ O) :
    P.obj L ≅ P.obj (F.obj L) :=
  t ≪≫ e.symm ≪≫ G.mapIso t.symm ≪≫ (A.app L).symm

/-- The normalisation is characterised by carrying `t` round the square back to `t`. -/
theorem normalizedIso_hom_comp (A : F ⋙ P ≅ P ⋙ G) {L : C} {O : D} (t : P.obj L ≅ O)
    (e : G.obj O ≅ O) :
    (normalizedIso A t e).hom ≫ A.hom.app L ≫ G.map t.hom ≫ e.hom = t.hom := by
  simp [normalizedIso]

/-- If `P.mapIso φ` is the normalisation, then `φ` carries `t` round the square back to `t`. -/
private theorem map_hom_comp_of_mapIso_eq (A : F ⋙ P ≅ P ⋙ G) {L : C} {O : D}
    (t : P.obj L ≅ O) (e : G.obj O ≅ O) {φ : L ≅ F.obj L} (hφ : P.mapIso φ = normalizedIso A t e) :
    P.map φ.hom ≫ A.hom.app L ≫ G.map t.hom ≫ e.hom = t.hom := by
  rw [← Functor.mapIso_hom, hφ]
  exact normalizedIso_hom_comp A t e

/-- **Normalised isomorphisms compose.** If `φ` and `φ'` restrict along `P` to the
normalisations for `F` and `F'`, then their composite, read through the comparison
`c : F' ⋙ F ≅ F''`, restricts to the normalisation for `F''`. The two compatibilities assumed
are that `c` and `d` intertwine the three squares (`hA`) and that `d` is compatible with the
trivialisations (`he`). -/
theorem normalizedIso_eq_of_comp (A : F ⋙ P ≅ P ⋙ G) (A' : F' ⋙ P ≅ P ⋙ G')
    (A'' : F'' ⋙ P ≅ P ⋙ G'') (c : F' ⋙ F ≅ F'') (d : G' ⋙ G ≅ G'')
    {L : C} {O : D} (t : P.obj L ≅ O) (e : G.obj O ≅ O) (e' : G'.obj O ≅ O)
    (e'' : G''.obj O ≅ O) (φ : L ≅ F.obj L) (φ' : L ≅ F'.obj L)
    (hφ : P.mapIso φ = normalizedIso A t e) (hφ' : P.mapIso φ' = normalizedIso A' t e')
    (hA : P.map (c.hom.app L) ≫ A''.hom.app L =
      A.hom.app (F'.obj L) ≫ G.map (A'.hom.app L) ≫ d.hom.app (P.obj L))
    (he : d.hom.app O ≫ e''.hom = G.map e'.hom ≫ e.hom) :
    P.mapIso (φ ≪≫ F.mapIso φ' ≪≫ c.app L) = normalizedIso A'' t e'' := by
  have hn := map_hom_comp_of_mapIso_eq A t e hφ
  have hn' := map_hom_comp_of_mapIso_eq A' t e' hφ'
  apply Iso.ext
  apply (cancel_mono (A''.hom.app L ≫ G''.map t.hom ≫ e''.hom)).mp
  rw [normalizedIso_hom_comp]
  simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.app_hom, CategoryTheory.Functor.map_comp,
    Category.assoc]
  rw [reassoc_of% hA, reassoc_of% (A.hom.naturality φ'.hom),
    ← reassoc_of% (d.hom.naturality t.hom), he]
  change P.map φ.hom ≫ A.hom.app L ≫ G.map (P.map φ'.hom) ≫ G.map (A'.hom.app L) ≫
    G.map (G'.map t.hom) ≫ G.map e'.hom ≫ e.hom = t.hom
  rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    ← CategoryTheory.Functor.map_comp_assoc]
  simpa only [Category.assoc, hn'] using hn

end Normalization

/-! ### The normalised isomorphism at a commuting square of pullbacks -/

/-- The composition compatibility of the comparison `f^* 𝒪 ≅ 𝒪`, in the form where the
composite is named by a morphism and an equation. -/
theorem pullbackUnitIso_compEq {V₁ V₂ V₃ : Scheme.{u}} (b : V₁ ⟶ V₂) (b' : V₂ ⟶ V₃)
    (bb' : V₁ ⟶ V₃) (hb : b ≫ b' = bb') :
    (pullbackCompEq b b' bb' hb).hom.app (Scheme.unitModule V₃) ≫
        (pullbackUnitIso bb').hom =
      (Scheme.Modules.pullback b).map (pullbackUnitIso b').hom ≫ (pullbackUnitIso b).hom := by
  rw [← Scheme.Modules.pullbackUnitIso_comp_eq b b' bb' hb]
  simp [pullbackCompEq]

/-- **The normalised isomorphism `p^* L ≅ p^* (a^* L)`** attached to a commuting square
`p ≫ a = d = b ≫ p` and a trivialisation `t : p^* L ≅ 𝒪` of the restriction of `L`. -/
def twistNormalizedIso (p : V ⟶ W) (a : W ⟶ W) (b : V ⟶ V) (dg : V ⟶ W) (h₁ : p ≫ a = dg)
    (h₂ : b ≫ p = dg) (L : W.Modules)
    (t : (Scheme.Modules.pullback p).obj L ≅ Scheme.unitModule V) :
    (Scheme.Modules.pullback p).obj L ≅
      (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback a).obj L) :=
  normalizedIso (pullbackCommIso p a b dg h₁ h₂) t (pullbackUnitIso b)

/-- **The cocycle identity for the normalised isomorphisms.** If `φ` and `φ'` restrict along
`p` to the normalised isomorphisms for the squares of `a` and of `a'`, then the composite
`L ≅ a^* L ≅ a^* a'^* L ≅ (a ≫ a')^* L` restricts to the normalised isomorphism for the square
of `a ≫ a'`. -/
theorem twistNormalizedIso_mul (p : V ⟶ W) (a a' aa' : W ⟶ W) (b b' bb' : V ⟶ V)
    (d d' dd' : V ⟶ W) (ha : a ≫ a' = aa') (hb : b ≫ b' = bb')
    (h₁ : p ≫ a = d) (h₂ : b ≫ p = d) (h₁' : p ≫ a' = d') (h₂' : b' ≫ p = d')
    (h₁'' : p ≫ aa' = dd') (h₂'' : bb' ≫ p = dd') (L : W.Modules)
    (t : (Scheme.Modules.pullback p).obj L ≅ Scheme.unitModule V)
    (φ : L ≅ (Scheme.Modules.pullback a).obj L)
    (φ' : L ≅ (Scheme.Modules.pullback a').obj L)
    (hφ : (Scheme.Modules.pullback p).mapIso φ = twistNormalizedIso p a b d h₁ h₂ L t)
    (hφ' : (Scheme.Modules.pullback p).mapIso φ' = twistNormalizedIso p a' b' d' h₁' h₂' L t) :
    (Scheme.Modules.pullback p).mapIso (φ ≪≫ (Scheme.Modules.pullback a).mapIso φ' ≪≫
        (pullbackCompEq a a' aa' ha).app L) =
      twistNormalizedIso p aa' bb' dd' h₁'' h₂'' L t :=
  normalizedIso_eq_of_comp (pullbackCommIso p a b d h₁ h₂)
    (pullbackCommIso p a' b' d' h₁' h₂') (pullbackCommIso p aa' bb' dd' h₁'' h₂'')
    (pullbackCompEq a a' aa' ha) (pullbackCompEq b b' bb' hb) t (pullbackUnitIso b)
    (pullbackUnitIso b') (pullbackUnitIso bb') φ φ' hφ hφ'
    (pullbackCommIso_mul p a a' aa' b b' bb' d d' dd' ha hb h₁ h₂ h₁' h₂' h₁'' h₂'' L)
    (pullbackUnitIso_compEq b b' bb' hb)

end Stacks.Picard

end
