module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiGluing

/-!
# Gluing sheaves of modules along a Zariski covering family

This file proves the remaining half of Sheaves, Section 00AK for sheaves of modules on a
scheme: the gluing of the **sheaves** themselves, as opposed to the gluing of morphisms
between them, which is
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/ZariskiGluing.lean`.  In the language of
descent data the statement is
`(AlgebraicGeometry.modulePullbackPseudofunctor.toDescentData f).EssSurj` for a family of open
immersions `f i : Y i ⟶ S` with `⨆ i, (f i).opensRange = ⊤`, and
`Stacks.Descent.isEffective_of_essSurj_zariski` turns it into the effectivity half of Stacks
023E, with no quasi-coherence side condition.

## Main definitions

* `Stacks.Descent.pushUnit`: for `g : Z ⟶ S`, `h : Z' ⟶ Z` and `h ≫ g = g'`, the pushforward
  along `g` of the unit of `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` at
  `h`, as a natural transformation `g_* ⟶ h^* ⋙ g'_*` of functors `Z.Modules ⥤ S.Modules`.
* `Stacks.Descent.pullbackCompHom`: the comparison `c^* h^* A ⟶ k^* A` attached to a
  factorisation `c ≫ h = k`, with its invertibility.
* `Stacks.Descent.descentRestrict`: for a descent datum `D` for a family of opens `U` of `S`
  and an open `W ≤ U a`, the pushforward to `S` of the restriction of `D.obj a` to `W`.
* `Stacks.Descent.descentRestrictUnit`: the comparison from the pushforward of `D.obj a` to
  that restriction, and `Stacks.Descent.descentShrink` the comparison between the restrictions
  to `W' ≤ W`.
* `Stacks.Descent.descentTransition`: the transition isomorphism of `D` over `W`, pushed
  forward to `S`.
* `Stacks.Descent.glueMatched`: for families `β i j : P i ⟶ B i j` and `γ i j : P j ⟶ B i j`
  of morphisms of `𝒪_S`-modules, **the sheaf of modules of families of sections matched by
  `β` and `γ`**, realized as the multiequalizer of the multicospan `P i ⟶ B i j ⟵ P j`.
  This is the object that the gluing of sheaves of modules along a Zariski covering family
  produces; its sections are described by `Stacks.Descent.glueMatchedπ_app_injective` and
  `Stacks.Descent.exists_glueMatchedπ_app`.

## Main results

* `Stacks.Descent.unit_pullbackPushforwardAdjunction_comp`: the **unit cocycle**.  The unit of
  the pullback-pushforward adjunction at a composite `c ≫ h` is the composite of the units at
  `h` and at `c`, transported by
  `AlgebraicGeometry.Scheme.Modules.pushforwardComp` and
  `AlgebraicGeometry.Scheme.Modules.pullbackComp`.  This is a mate computation, resting on
  Mathlib's `AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`, and it is the
  one non-formal ingredient of this file.
* `Stacks.Descent.pushUnit_comp`: consequently `Stacks.Descent.pushUnit` is itself compatible
  with composition.  This is what lets a piece of a descent datum be restricted to a smaller
  open in two steps, and it is `Stacks.Descent.descentShrink`'s characterisation.
* `Stacks.Descent.isIso_pushUnit_app_app`: for an open immersion `h` the comparison is
  invertible on sections over an open whose preimage lies in the range of `h`; at the
  inclusions of opens this is `Stacks.Descent.isIso_descentRestrictUnit_app`.
* `Stacks.Descent.pullHom_eq'`: `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom`
  for `AlgebraicGeometry.modulePullbackPseudofunctor`, written out with
  `AlgebraicGeometry.Scheme.Modules.pullbackComp`.  It holds by `rfl`; this generalises
  `Stacks.Descent.pullHom_eq`, which is the case of a single morphism, to a morphism between
  pullbacks along two different morphisms.
* `Stacks.Descent.descentTransition_self` and `Stacks.Descent.descentTransition_comp`: the
  transitions over a fixed open compose as a groupoid, indexed by the members of the covering
  whose range contains that open.
* `Stacks.Descent.glueMatchedπ_app_injective` and `Stacks.Descent.exists_glueMatchedπ_app`:
  over every open `V`, a section of `Stacks.Descent.glueMatched` *is* a family
  `s i : Γ(P i, V)` with `(β i j).app V (s i) = (γ i j).app V (s j)`.  Note that the factors
  of that product are modules over *different* rings `Γ(S, V ⊓ U i)`, which is why
  `StacksFrontier/Topology/Sheaves/Glueing/AlgebraicStructure.lean` (Stacks 00AM), which glues
  sheaves of modules over a *fixed* ring, does not apply.
* `Stacks.Descent.essSurj_toDescentData_of_opens`: **the reduction of the general statement to
  the case of a family of inclusions of opens.**  Given essential surjectivity of the descent
  functor for every family `(W j).ι` of inclusions of opens covering a scheme, it holds for an
  arbitrary family of open immersions with covering images, at an arbitrary index universe.
  This uses the Zariski prestack instance
  `Stacks.Descent.isPrestack_modulePullbackPseudofunctor` through Mathlib's
  `CategoryTheory.Pseudofunctor.DescentData.isEquivalence_toDescentData_of_sieve_le`, and it
  is what removes the universe difficulty: the images of a family indexed by any type are
  indexed by a subtype of `S.Opens`, hence by a type in the universe of the schemes.
* `Stacks.Descent.essSurj_toDescentData_opens`: **the gluing of sheaves of modules along a
  family of inclusions of opens.**  For any family `U : I → S.Opens` — no covering hypothesis
  is needed — the descent functor is essentially surjective, the preimage of a descent datum
  `D` being `Stacks.Descent.glueModule D`.
* `Stacks.Descent.essSurj_toDescentData_zariski`: consequently, by
  `Stacks.Descent.essSurj_toDescentData_of_opens`, the descent functor is essentially
  surjective for an arbitrary Zariski covering family, at an arbitrary index universe.
* `Stacks.Descent.isEffective_zariski`, tagged `@[stacks 023E "zariski_effectivity"]`, and
  `Stacks.Descent.isEffective_openCover`: **the effectivity half of Stacks 023E**, obtained
  from the previous item through `Stacks.Descent.isEffective_of_essSurj_zariski`.  Together
  with `Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_zariski` of
  `StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/ZariskiGluing.lean` this is all of
  Stacks 023E for the Zariski topology.

Stacks 023T is *not* a consequence: it is a statement about the **fpqc** topology, and the
reductions it would be deduced from need
`Stacks.Descent.qcohPseudofunctor.IsStack AlgebraicGeometry.Scheme.fpqcTopology`, which a
Zariski instance cannot supply.

## The shape of the gluing argument

Let `D` be a descent datum for a family `U : I → S.Opens`, and write `Γ(a, V)` for the
sections of `D.obj a` over `(U a).ι ⁻¹ᵁ V`.  The glued module is the multiequalizer
`Stacks.Descent.glueModule` of the multicospan `Stacks.Descent.glueFst`,
`Stacks.Descent.glueSnd` over the pairwise overlaps, so a section of it over `V` is a family
of sections of the `D.obj a` over `V` matched by the transitions of `D`.

1. Over an open `V ≤ U i` the `i`-th projection is bijective
   (`Stacks.Descent.bijective_glueMatchedπ_app_glue`).  Injectivity holds because
   `Stacks.Descent.glueSnd D i j` is invertible on sections over `V`
   (`Stacks.Descent.isIso_glueSnd_app`), so the `j`-th component of a section is determined by
   its `i`-th one.  For surjectivity the `j`-th component of the preimage of `t` is the image
   of `t` under `glueFst D i j` followed by the inverse of `glueSnd D i j`, and the matching
   condition for a pair `(j, k)` is `Stacks.Descent.glueFst_app_eq_glueSnd_app`: all three
   overlaps are compared down to `U i ⊓ U j ⊓ U k` by `Stacks.Descent.exists_glueShrink`,
   where `Stacks.Descent.glueTransition_comp` closes the argument, and the comparison for the
   pair `(j, k)` is invertible over `V` precisely because `V ≤ U i`.
2. Hence `(Scheme.Modules.restrictFunctor (U i).ι).map` of that projection is an isomorphism
   (`Stacks.Descent.isIso_restrictFunctor_map_glueMatchedπ`), and
   `Stacks.Descent.exists_pullbackIso` converts it into an isomorphism
   `e i : (Scheme.Modules.pullback (U i).ι).obj (glueModule D) ≅ D.obj i` whose adjunct is the
   projection.
3. The descent-datum compatibility of the `e i` is checked over the *chosen* pullbacks
   `Stacks.Descent.chosenPullbackOpens`, `Stacks.Descent.chosenPullback₃Opens` through
   `CategoryTheory.Pseudofunctor.DescentData'.isoMk` and
   `CategoryTheory.Pseudofunctor.DescentData'.descentDataEquivalence`.  There it is
   `Stacks.Descent.descentData_comm_of_unit`: the two adjuncts agree after
   `Stacks.Descent.pushUnit`, which is the multiequalizer condition
   `Stacks.Descent.glueMatchedπ_comp`, and the adjunction bijection along `(U i ⊓ U j).ι` is
   injective.

## Implementation notes

As in `ZariskiGluing.lean`, every comparison is stated so that the opens appearing in a
composite are *syntactically* the same: the unit is pushed all the way down to `S`, so that
each arrow is `AlgebraicGeometry.Scheme.Modules.Hom.app _ V` for one fixed open `V` of the
base, and all the category-theoretic work happens one level up, between morphisms of
`AlgebraicGeometry.Scheme.Modules`.

Several statements below are proved at the level of natural transformations and then read on
sections, rather than the other way round: a `rw` against a lemma stated for
`AlgebraicGeometry.Scheme.Modules` does not fire on a term typed at
`↑(AlgebraicGeometry.modulePullbackPseudofunctor.obj _)`, because the two carry different
`CategoryTheory.Category` instances which are only definitionally equal.  Term-level
`Eq.trans`, `congrArg` and `exact` check at default transparency and are used instead.

Three devices keep this file inside the kernel's budget; removing any
one of them turns a declaration below into a `(kernel) deterministic timeout`.

* The comparison between the restrictions to `W` and to a smaller `W'` — morally
  `Stacks.Descent.descentShrink` — is never written out at the inclusions of opens.  It is
  produced as an **existential**, `Stacks.Descent.exists_restrictShrink`, from three lemmas
  whose statements are the three clauses verbatim, so that nothing has to be compared.
* `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` appears only in statements
  whose morphisms are *variables* (`Stacks.Descent.pullbackCompHom_comp_pullHom`); at
  `AlgebraicGeometry.Scheme.homOfLE` it is expensive.  Likewise `D.obj` and `D.hom` are
  retyped once and for all by `Stacks.Descent.descentObj` and `Stacks.Descent.descentHom`,
  and the gluing works with `Stacks.Descent.glueRestrict`,
  `Stacks.Descent.glueRestrictUnit` and `Stacks.Descent.glueTransition` rather than with
  `Stacks.Descent.descentRestrict` and its companions, which are spelled with `D.obj`.
* Two proofs of one inequality of opens are interchangeable by proof irrelevance, but
  `AlgebraicGeometry.Scheme.Modules.pullbackCongr` wraps the morphism they produce in an
  `CategoryTheory.eqToIso`, and crossing the difference there costs about thirty seconds of
  kernel time.  So `Stacks.Descent.exists_glueShrink` takes the inequalities as arguments and
  its proof spells them exactly as the lemmas it feeds expect.

A consequence of the second device is that `Stacks.Descent.descentRestrict`,
`Stacks.Descent.descentRestrictUnit`, `Stacks.Descent.descentTransition`,
`Stacks.Descent.descentShrink` and the lemmas about them are no longer used by the gluing:
their `Stacks.Descent.descentObj`-spelled counterparts `Stacks.Descent.glueRestrict`,
`Stacks.Descent.glueRestrictUnit` and `Stacks.Descent.glueTransition` are.  The two families
are definitionally the same objects and morphisms.

`Stacks.Descent.pullbackCompHom` and `Stacks.Descent.pullbackCongr_rfl_hom` duplicate, at the
level of morphisms, `Stacks.Sites.pullbackCompIso` and
`Stacks.Sites.pullbackCongr_rfl_hom_app` of
`StacksFrontier/AlgebraicGeometry/Topologies/ZariskiQuasicoherentSheaf.lean`.  They are
restated here rather than imported because that file belongs to the Stacks 03DT tree and
pulling it into a descent foundation module would invert the import order.

## References

* [Stacks Project, Tag 00AK](https://stacks.math.columbia.edu/tag/00AK)
* [Stacks Project, Tag 023D](https://stacks.math.columbia.edu/tag/023D)
* [Stacks Project, Tag 023E](https://stacks.math.columbia.edu/tag/023E)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory Opposite TopologicalSpace

universe w v₂ u₂ v u

namespace Stacks.Descent

open Scheme.Modules Pseudofunctor.LocallyDiscreteOpToCat

variable {S Z Z' Z'' : Scheme.{u}}

/-! ### The pushforward of a unit -/

/-- The pushforward along `g : Z ⟶ S` of the unit of the pullback-pushforward adjunction at
`h : Z' ⟶ Z`, for a factorisation `h ≫ g = g'`. -/
def pushUnit (g : Z ⟶ S) (h : Z' ⟶ Z) (g' : Z' ⟶ S) (hg : h ≫ g = g') :
    pushforward g ⟶ pullback h ⋙ pushforward g' where
  app A := (pushforward g).map ((pullbackPushforwardAdjunction h).unit.app A) ≫
    (pushforwardComp h g).hom.app _ ≫ (pushforwardCongr hg).hom.app _
  naturality A B φ := by
    dsimp
    simp only [Category.assoc]
    rw [← NatTrans.naturality ((pushforwardCongr hg).hom) ((pullback h).map φ),
      ← NatTrans.naturality_assoc ((pushforwardComp h g).hom) ((pullback h).map φ)]
    simp only [Functor.comp_map, ← Functor.map_comp_assoc]
    congr 2
    simp

/-- The component of `Stacks.Descent.pushUnit` at `A`: the pushforward along `g` of the unit
at `A`, followed by `AlgebraicGeometry.Scheme.Modules.pushforwardComp` and
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr`. -/
theorem pushUnit_app (g : Z ⟶ S) (h : Z' ⟶ Z) (g' : Z' ⟶ S) (hg : h ≫ g = g') (A : Z.Modules) :
    (pushUnit g h g' hg).app A = (pushforward g).map
      ((pullbackPushforwardAdjunction h).unit.app A) ≫
      (pushforwardComp h g).hom.app _ ≫ (pushforwardCongr hg).hom.app _ := rfl

/-- The comparison of pushforwards along equal morphisms is the identity when the equality is
`rfl`. -/
@[simp]
theorem pushforwardCongr_rfl_hom (f : Z ⟶ S) (hf : f = f) :
    (pushforwardCongr hf).hom = 𝟙 _ := by
  ext : 3
  simp

/-- The comparison of pullbacks along equal morphisms is the identity when the equality is
reflexive. -/
@[simp]
theorem pullbackCongr_rfl_hom (f : Z ⟶ S) (hf : f = f) :
    (pullbackCongr hf).hom = 𝟙 _ := rfl

/-- **The unit cocycle.**  The unit of the pullback-pushforward adjunction at a composite
`c ≫ h` is the composite of the units at `h` and at `c`, transported along
`AlgebraicGeometry.Scheme.Modules.pushforwardComp` and
`AlgebraicGeometry.Scheme.Modules.pullbackComp`.

This is a mate computation: `pullbackComp` conjugates to `pushforwardComp`, which is Mathlib's
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`. -/
theorem unit_pullbackPushforwardAdjunction_comp (h : Z' ⟶ Z) (c : Z'' ⟶ Z') (A : Z.Modules) :
    (pullbackPushforwardAdjunction (c ≫ h)).unit.app A =
      (pullbackPushforwardAdjunction h).unit.app A ≫
        (pushforward h).map ((pullbackPushforwardAdjunction c).unit.app
          ((pullback h).obj A)) ≫
        (pushforwardComp c h).hom.app _ ≫
        (pushforward (c ≫ h)).map ((pullbackComp c h).hom.app A) := by
  have key := unit_conjugateEquiv (Adjunction.comp
      (pullbackPushforwardAdjunction h) (pullbackPushforwardAdjunction c))
      (pullbackPushforwardAdjunction (c ≫ h)) (pullbackComp c h).inv A
  rw [conjugateEquiv_pullbackComp_inv, CategoryTheory.Adjunction.comp_unit_app] at key
  simp only [Functor.comp_obj] at key
  conv_rhs => rw [← Category.assoc, ← Category.assoc, key]
  simp [← Functor.map_comp]

/-- The comparison `c^* h^* A ⟶ k^* A` attached to a factorisation `c ≫ h = k`.  It is
stated at variable morphisms, and instantiated at the inclusions of opens below: the
instantiated form is free, whereas the composite written out at those inclusions is not. -/
def pullbackCompHom (c : Z'' ⟶ Z') (h : Z' ⟶ Z) (k : Z'' ⟶ Z) (hk : c ≫ h = k)
    (A : Z.Modules) :
    (pullback c).obj ((pullback h).obj A) ⟶ (pullback k).obj A :=
  (pullbackComp c h).hom.app A ≫ (pullbackCongr hk).hom.app A

/-- The comparison `Stacks.Descent.pullbackCompHom` is an isomorphism. -/
instance (c : Z'' ⟶ Z') (h : Z' ⟶ Z) (k : Z'' ⟶ Z) (hk : c ≫ h = k) (A : Z.Modules) :
    IsIso (pullbackCompHom c h k hk A) :=
  have h₁ : IsIso ((pullbackComp c h).hom.app A) := ((pullbackComp c h).app A).isIso_hom
  have h₂ : IsIso ((pullbackCongr hk).hom.app A) := ((pullbackCongr hk).app A).isIso_hom
  @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂

/-- **`Stacks.Descent.pushUnit` is compatible with composition.** -/
theorem pushUnit_comp (g : Z ⟶ S) (h : Z' ⟶ Z) (c : Z'' ⟶ Z') (g' : Z' ⟶ S) (g'' : Z'' ⟶ S)
    (k : Z'' ⟶ Z) (hg : h ≫ g = g') (hg' : c ≫ g' = g'') (hk : c ≫ h = k) (A : Z.Modules) :
    (pushUnit g k g'' (by rw [← hk, Category.assoc, hg, hg'])).app A =
      (pushUnit g h g' hg).app A ≫ (pushUnit g' c g'' hg').app ((pullback h).obj A) ≫
        (pushforward g'').map (pullbackCompHom c h k hk A) := by
  subst hk hg hg'
  rw [pushUnit_app, pushUnit_app, pushUnit_app, pullbackCompHom,
    unit_pullbackPushforwardAdjunction_comp]
  simp only [Functor.map_comp, Category.assoc]
  refine Scheme.Modules.hom_ext _ _ fun V ↦ ?_
  simp only [Functor.id_obj, pushforward_obj_obj, Scheme.Hom.comp_base, Opens.map_comp_obj,
    Functor.comp_obj, Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
    pushforwardCongr_hom_app_app, Category.id_comp, pushforwardCongr_rfl_hom, NatTrans.id_app,
    pullbackCongr_rfl_hom]
  congr 1
  congr 1
  generalize_proofs e
  rw [Subsingleton.elim (eqToHom e) (𝟙 _)]
  simp

/-- On sections over `V`, the component of `Stacks.Descent.pushUnit` for the factorisation
`h ≫ g` at `A` is `Stacks.Descent.unitApp h A (g ⁻¹ᵁ V)`. -/
theorem pushUnit_app_app (g : Z ⟶ S) (h : Z' ⟶ Z) (A : Z.Modules) (V : S.Opens) :
    ((pushUnit g h (h ≫ g) rfl).app A).app V = unitApp h A (g ⁻¹ᵁ V) := by
  simp only [pushUnit_app, unitApp, Scheme.Modules.Hom.comp_app,
    pushforward_map_app, pushforwardComp_hom_app_app, pushforwardCongr_rfl_hom, NatTrans.id_app]
  exact Category.comp_id _

/-- **The comparison is invertible on sections over an open whose preimage lies in the range.**
This is `Stacks.Descent.isIso_unitApp`, pushed forward to the base. -/
theorem isIso_pushUnit_app_app (g : Z ⟶ S) (h : Z' ⟶ Z) [IsOpenImmersion h] (g' : Z' ⟶ S)
    (hg : h ≫ g = g') (A : Z.Modules) (V : S.Opens) (hV : g ⁻¹ᵁ V ≤ h.opensRange) :
    IsIso (((pushUnit g h g' hg).app A).app V) := by
  subst hg
  rw [pushUnit_app_app]
  exact isIso_unitApp h A _ hV

/-- `Stacks.Descent.isIso_pushUnit_app_app` at the inclusion of an open `W ≤ Ua`, over an open
`V` with `V ⊓ Ua ≤ W`. -/
private theorem isIso_pushUnit_homOfLE_app_of_inf_le {S : Scheme.{u}} (Ua W V : S.Opens)
    (haW : W ≤ Ua) (A : Ua.toScheme.Modules) (hV : V ⊓ Ua ≤ W) :
    IsIso (((pushUnit Ua.ι (S.homOfLE haW) W.ι (S.homOfLE_ι haW)).app A).app V) := by
  refine isIso_pushUnit_app_app Ua.ι (S.homOfLE haW) W.ι (S.homOfLE_ι haW) A V ?_
  rw [Scheme.opensRange_homOfLE]
  intro x hx
  exact hV ⟨hx, x.2⟩

/-- `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` for
`AlgebraicGeometry.modulePullbackPseudofunctor`, written out.  This generalises
`Stacks.Descent.pullHom_eq` to a morphism between pullbacks along two different morphisms. -/
theorem pullHom_eq' {Z₁ Z₂ Y Y' : Scheme.{u}} {M₁ : Z₁.Modules} {M₂ : Z₂.Modules}
    (f₁ : Y ⟶ Z₁) (f₂ : Y ⟶ Z₂) (φ : (pullback f₁).obj M₁ ⟶ (pullback f₂).obj M₂)
    (c : Y' ⟶ Y) (gf₁ : Y' ⟶ Z₁) (gf₂ : Y' ⟶ Z₂) (h₁ : c ≫ f₁ = gf₁) (h₂ : c ≫ f₂ = gf₂) :
    pullHom (F := modulePullbackPseudofunctor) (M₁ := M₁) (M₂ := M₂) φ c gf₁ gf₂ h₁ h₂ =
      ((pullbackComp c f₁).app M₁ ≪≫ (pullbackCongr h₁).app M₁).inv ≫ (pullback c).map φ ≫
        ((pullbackComp c f₂).app M₂ ≪≫ (pullbackCongr h₂).app M₂).hom := by
  subst h₁ h₂
  rfl

/-- `Stacks.Descent.pullbackCompHom c h k hk A` is the forward morphism of the composite of
the isomorphisms `(pullbackComp c h).app A` and `(pullbackCongr hk).app A`. -/
theorem pullbackCompHom_eq_hom (c : Z'' ⟶ Z') (h : Z' ⟶ Z) (k : Z'' ⟶ Z) (hk : c ≫ h = k)
    (A : Z.Modules) :
    pullbackCompHom c h k hk A =
      ((pullbackComp c h).app A ≪≫ (pullbackCongr hk).app A).hom := rfl

/-- **`Stacks.Descent.pullbackCompHom` intertwines a morphism of pullbacks with its pullback
along a further morphism.**  The pullback is given as a separate argument `ψ` together with the
equation identifying it with
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom`, so that neither the statement nor
the conclusion mentions `pullHom`: at the inclusions of opens the latter is what makes a
statement kernel-time out. -/
theorem pullbackCompHom_comp_pullHom {Z₁ Z₂ Y Y' : Scheme.{u}} {M₁ : Z₁.Modules} {M₂ : Z₂.Modules}
    (f₁ : Y ⟶ Z₁) (f₂ : Y ⟶ Z₂) (φ : (pullback f₁).obj M₁ ⟶ (pullback f₂).obj M₂)
    (c : Y' ⟶ Y) (gf₁ : Y' ⟶ Z₁) (gf₂ : Y' ⟶ Z₂) (h₁ : c ≫ f₁ = gf₁) (h₂ : c ≫ f₂ = gf₂)
    (ψ : (pullback gf₁).obj M₁ ⟶ (pullback gf₂).obj M₂)
    (hψ : pullHom (F := modulePullbackPseudofunctor) (M₁ := M₁) (M₂ := M₂) φ c gf₁ gf₂ h₁ h₂ =
      ψ) :
    pullbackCompHom c f₁ gf₁ h₁ M₁ ≫ ψ =
      (pullback c).map φ ≫ pullbackCompHom c f₂ gf₂ h₂ M₂ := by
  subst hψ
  rw [pullHom_eq' f₁ f₂ φ c gf₁ gf₂ h₁ h₂, pullbackCompHom_eq_hom c f₁ gf₁ h₁ M₁,
    pullbackCompHom_eq_hom c f₂ gf₂ h₂ M₂]
  exact Iso.hom_inv_id_assoc _ _

/-! ### The pieces of a descent datum for a family of opens, pushed to the base -/

section Transitions

variable {I : Type v} {U : I → S.Opens}
  (D : modulePullbackPseudofunctor.DescentData (fun i ↦ (U i).ι))

/-- The pushforward to `S` of the restriction of `D.obj a` to an open `W ≤ U a`. -/
def descentRestrict (W : S.Opens) (a : I) (haW : W ≤ U a) : S.Modules :=
  (pushforward W.ι).obj ((pullback (S.homOfLE haW)).obj (D.obj a))

/-- The comparison from the pushforward of `D.obj a` to its restriction over `W ≤ U a`. -/
def descentRestrictUnit (W : S.Opens) (a : I) (haW : W ≤ U a) :
    (pushforward (U a).ι).obj (D.obj a) ⟶ descentRestrict D W a haW :=
  (pushUnit (U a).ι (S.homOfLE haW) W.ι (S.homOfLE_ι haW)).app (D.obj a)

/-- The transition of the descent datum over an open `W` contained in both `U a` and `U b`,
pushed forward to `S`. -/
def descentTransition (W : S.Opens) (a b : I) (haW : W ≤ U a) (hbW : W ≤ U b) :
    descentRestrict D W a haW ⟶ descentRestrict D W b hbW :=
  (pushforward W.ι).map
    (D.hom W.ι (S.homOfLE haW) (S.homOfLE hbW) (S.homOfLE_ι haW) (S.homOfLE_ι hbW))

/-- The transition of `D` from `a` to itself over `W` is the identity. -/
@[simp]
theorem descentTransition_self (W : S.Opens) (a : I) (haW : W ≤ U a) :
    descentTransition D W a a haW haW = 𝟙 _ :=
  (congrArg (pushforward W.ι).map
      (D.hom_self W.ι (S.homOfLE haW) (S.homOfLE_ι haW))).trans
    ((pushforward W.ι).map_id _)

/-- The transitions of `D` over `W` compose: the transition from `a` to `b` followed by the one
from `b` to `c` is the transition from `a` to `c`. -/
@[reassoc]
theorem descentTransition_comp (W : S.Opens) (a b c : I) (haW : W ≤ U a) (hbW : W ≤ U b)
    (hcW : W ≤ U c) :
    descentTransition D W a b haW hbW ≫ descentTransition D W b c hbW hcW =
      descentTransition D W a c haW hcW :=
  ((pushforward W.ι).map_comp _ _).symm.trans
    (congrArg (pushforward W.ι).map (D.hom_comp W.ι _ _ _ _ _ _))

/-- **The comparison to the restriction over `W` is invertible on sections over `V`** as soon
as `V ⊓ U a ≤ W`. -/
theorem isIso_descentRestrictUnit_app (W V : S.Opens) (a : I) (haW : W ≤ U a)
    (hV : V ⊓ U a ≤ W) : IsIso ((descentRestrictUnit D W a haW).app V) := by
  exact isIso_pushUnit_homOfLE_app_of_inf_le (U a) W V haW (D.obj a) hV

/-- The comparison between restricting `D.obj a` to `W` and then to `W' ≤ W`, and restricting
it to `W'` directly. -/
abbrev descentShrinkHom (W W' : S.Opens) (a : I) (hW' : W' ≤ W) (haW : W ≤ U a) :
    (pullback (S.homOfLE hW')).obj ((pullback (S.homOfLE haW)).obj (D.obj a)) ⟶
      (pullback (S.homOfLE (hW'.trans haW))).obj (D.obj a) :=
  pullbackCompHom (S.homOfLE hW') (S.homOfLE haW) (S.homOfLE (hW'.trans haW))
    (S.homOfLE_homOfLE hW' haW) (D.obj a)

/-- Shrinking the open over which a piece of a descent datum is restricted. -/
abbrev descentShrink (W W' : S.Opens) (a : I) (hW' : W' ≤ W) (haW : W ≤ U a) :
    descentRestrict D W a haW ⟶ descentRestrict D W' a (hW'.trans haW) :=
  (pushUnit W.ι (S.homOfLE hW') W'.ι (S.homOfLE_ι hW')).app _ ≫
    (pushforward W'.ι).map (descentShrinkHom D W W' a hW' haW)

end Transitions

/-! ### The sheaf of matched families -/

section Matched

variable {I : Type u} {P : I → S.Modules} {B : I → I → S.Modules}
  (β : ∀ i j, P i ⟶ B i j) (γ : ∀ i j, P j ⟶ B i j)

/-- The multicospan `P i ⟶ B i j ⟵ P j` whose multiequalizer is
`Stacks.Descent.glueMatched`. -/
def matchedIndex : Limits.MulticospanIndex (.prod I) S.Modules where
  left := P
  right := fun p ↦ B p.1 p.2
  fst := fun p ↦ β p.1 p.2
  snd := fun p ↦ γ p.1 p.2

/-- **The sheaf of modules of families of sections matched by `β` and `γ`.**  This is the
object that the gluing of sheaves of modules along a Zariski covering family produces: over
an open `V` its sections are the families `s i : Γ(P i, V)` with
`(β i j).app V (s i) = (γ i j).app V (s j)`, by
`Stacks.Descent.glueMatchedπ_app_injective` and `Stacks.Descent.exists_glueMatchedπ_app`. -/
def glueMatched : S.Modules := Limits.multiequalizer (matchedIndex β γ)

/-- The `i`-th component of a section of `Stacks.Descent.glueMatched`. -/
def glueMatchedπ (i : I) : glueMatched β γ ⟶ P i := Limits.Multiequalizer.ι (matchedIndex β γ) i

/-- The components of a section of `Stacks.Descent.glueMatched` are matched by `β` and `γ`. -/
theorem glueMatchedπ_comp (i j : I) :
    glueMatchedπ β γ i ≫ β i j = glueMatchedπ β γ j ≫ γ i j :=
  Limits.Multiequalizer.condition (matchedIndex β γ) (i, j)

/-- Sections over a fixed open `V`, as a functor `S.Modules ⥤ Ab`.  On objects it is
`fun M ↦ Γ(M, V)` and on morphisms `fun φ ↦ φ.app V`, both by definition. -/
def matchedSectionsFunctor (V : S.Opens) : S.Modules ⥤ Ab.{u} :=
  Scheme.Modules.toPresheaf S ⋙ (CategoryTheory.evaluation _ _).obj (op V)

/-- Taking sections over an open preserves limits, being a composite of two functors that
do. -/
instance preservesLimitsMatchedSectionsFunctor (V : S.Opens) :
    Limits.PreservesLimitsOfSize.{u, u} (matchedSectionsFunctor (S := S) V) := by
  have h : Limits.PreservesLimitsOfSize.{u, u}
      ((CategoryTheory.evaluation ((Opens ↥S)ᵒᵖ) Ab.{u}).obj (op V)) := inferInstance
  unfold matchedSectionsFunctor
  exact Limits.comp_preservesLimits _ _

/-- The multicospan of abelian groups obtained from `Stacks.Descent.matchedIndex` by taking
sections over `V`. -/
def matchedSectionsIndex (V : S.Opens) : Limits.MulticospanIndex (.prod I) Ab.{u} where
  left i := Γ(P i, V)
  right p := Γ(B p.1 p.2, V)
  fst p := (β p.1 p.2).app V
  snd p := (γ p.1 p.2).app V

/-- Taking sections over `V` of `Stacks.Descent.matchedIndex` is
`Stacks.Descent.matchedSectionsIndex`. -/
def matchedComparison (V : S.Opens) :
    (matchedIndex β γ).multicospan ⋙ matchedSectionsFunctor V ≅
      (matchedSectionsIndex β γ V).multicospan :=
  Limits.WalkingMulticospan.functorExt (fun _ ↦ Iso.refl _) (fun _ ↦ Iso.refl _)

/-- The sections of `Stacks.Descent.glueMatched` over `V`, as a multifork. -/
def matchedSectionsMultifork (V : S.Opens) :
    Limits.Multifork (matchedSectionsIndex β γ V) :=
  (Limits.Cone.postcompose (matchedComparison β γ V).hom).obj
    ((matchedSectionsFunctor V).mapCone (Limits.Multiequalizer.multifork (matchedIndex β γ)))

/-- `Stacks.Descent.matchedSectionsMultifork` is a limit multifork. -/
def matchedSectionsMultiforkIsLimit (V : S.Opens) :
    Limits.IsLimit (matchedSectionsMultifork β γ V) :=
  (Limits.IsLimit.postcomposeHomEquiv (matchedComparison β γ V) _).symm
    (Limits.isLimitOfPreserves (matchedSectionsFunctor V)
      (Limits.limit.isLimit (matchedIndex β γ).multicospan))

/-- The sections of `Stacks.Descent.glueMatched` over `V` are the multiequalizer, in abelian
groups, of the sections of the `P i` and of the `B i j` over `V`. -/
def matchedSectionsIso (V : S.Opens) :
    Γ(glueMatched β γ, V) ≅ Limits.multiequalizer (matchedSectionsIndex β γ V) :=
  Limits.IsLimit.conePointUniqueUpToIso (matchedSectionsMultiforkIsLimit β γ V)
    (Limits.limit.isLimit _)

/-- `Stacks.Descent.matchedSectionsIso` is compatible with the projections. -/
theorem matchedSectionsIso_hom_comp (V : S.Opens) (i : I) :
    (matchedSectionsIso β γ V).hom ≫ Limits.Multiequalizer.ι (matchedSectionsIndex β γ V) i =
      (glueMatchedπ β γ i).app V :=
  (Limits.IsLimit.conePointUniqueUpToIso_hom_comp (matchedSectionsMultiforkIsLimit β γ V)
    (Limits.limit.isLimit (matchedSectionsIndex β γ V).multicospan)
    (Limits.WalkingMulticospan.left i)).trans (Category.comp_id _)

/-- **A section of `Stacks.Descent.glueMatched` over an open is determined by its
components.** -/
theorem glueMatchedπ_app_injective (V : S.Opens) {x y : Γ(glueMatched β γ, V)}
    (h : ∀ i, (glueMatchedπ β γ i).app V x = (glueMatchedπ β γ i).app V y) : x = y := by
  refine (ConcreteCategory.bijective_of_isIso (matchedSectionsIso β γ V).hom).1 ?_
  refine Limits.Concrete.multiequalizer_ext _ _ fun i ↦ ?_
  have hi := matchedSectionsIso_hom_comp β γ V i
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, hi]
  exact h i

/-- **Every matched family of sections over an open comes from a section of
`Stacks.Descent.glueMatched`.** -/
theorem exists_glueMatchedπ_app (V : S.Opens) (s : ∀ i, Γ(P i, V))
    (hs : ∀ i j, (β i j).app V (s i) = (γ i j).app V (s j)) :
    ∃ x : Γ(glueMatched β γ, V), ∀ i, (glueMatchedπ β γ i).app V x = s i := by
  obtain ⟨z, hz⟩ : ∃ z : ↥(Limits.multiequalizer (matchedSectionsIndex β γ V)),
      ∀ i, Limits.Multiequalizer.ι (matchedSectionsIndex β γ V) i z = s i := by
    refine ⟨(Limits.Concrete.multiequalizerEquiv (matchedSectionsIndex β γ V)).symm
      ⟨s, fun p ↦ hs p.1 p.2⟩, fun i ↦ ?_⟩
    rw [← Limits.Concrete.multiequalizerEquiv_apply, Equiv.apply_symm_apply]
  refine ⟨(matchedSectionsIso β γ V).inv z, fun i ↦ ?_⟩
  have h1 : (matchedSectionsIso β γ V).inv ≫ (glueMatchedπ β γ i).app V =
      Limits.Multiequalizer.ι (matchedSectionsIndex β γ V) i := by
    rw [← matchedSectionsIso_hom_comp β γ V i]
    exact Iso.inv_hom_id_assoc _ _
  rw [← ConcreteCategory.comp_apply, h1]
  exact hz i

end Matched

/-! ### Reduction to a family of opens -/

/-- **Essential surjectivity of the descent functor for an arbitrary Zariski covering family
reduces to the case of a family of inclusions of opens.**  The reduction is Mathlib's
`CategoryTheory.Pseudofunctor.DescentData.isEquivalence_toDescentData_of_sieve_le`, whose
standing prestack hypothesis is
`Stacks.Descent.isPrestack_modulePullbackPseudofunctor`, applied to the family of the images
of the given morphisms; those images form a family of opens generating the same sieve, and
they are indexed by a subtype of `S.Opens`, hence by a type in the universe of the schemes,
whatever the universe of the original index type. -/
theorem essSurj_toDescentData_of_opens
    (hopens : ∀ (T : Scheme.{u}) (J : Type u) (W : J → T.Opens), ⨆ j, W j = ⊤ →
      (modulePullbackPseudofunctor.toDescentData (fun j ↦ (W j).ι)).EssSurj)
    {S : Scheme.{u}} {I : Type v} {Y : I → Scheme.{u}} (f : ∀ i, Y i ⟶ S)
    [∀ i, IsOpenImmersion (f i)] (hf : ⨆ i, (f i).opensRange = ⊤) :
    (modulePullbackPseudofunctor.toDescentData f).EssSurj := by
  obtain ⟨K, W, hW, hfac⟩ : ∃ (K : Type u) (W : K → S.Opens), (⨆ j, W j = ⊤) ∧
      ∀ j, ∃ (i : I) (b : (W j).toScheme ⟶ Y i), (W j).ι = b ≫ f i := by
    refine ⟨↥(Set.range fun i ↦ (f i).opensRange), Subtype.val, le_antisymm le_top ?_, ?_⟩
    · rw [← hf]
      exact iSup_le fun i ↦ le_iSup Subtype.val
        (⟨_, i, rfl⟩ : ↥(Set.range fun i ↦ (f i).opensRange))
    · rintro ⟨_, i, rfl⟩
      exact ⟨i, (f i).isoOpensRange.inv, ((f i).isoOpensRange_inv_comp).symm⟩
  have hWι : ⨆ j, ((W j).ι).opensRange = ⊤ := by
    simpa only [Scheme.Opens.opensRange_ι] using hW
  have := hopens S K W hW
  have := (fullyFaithfulToDescentData hWι).full
  have := (fullyFaithfulToDescentData hWι).faithful
  have : (modulePullbackPseudofunctor.toDescentData fun j ↦ (W j).ι).IsEquivalence := { }
  have h₁ : Sieve.ofArrows _ (fun j ↦ (W j).ι) ∈ Scheme.zariskiTopology.{u} S := by
    refine Precoverage.generate_mem_toGrothendieck ?_
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun j ↦ inferInstance⟩
    have hx : x ∈ ⨆ j, ((W j).ι).opensRange := by rw [hWι]; exact Opens.mem_top x
    exact Opens.mem_iSup.1 hx
  have h₂ : Sieve.ofArrows _ (fun j ↦ (W j).ι) ≤ Sieve.ofArrows Y f := by
    intro T g hg
    rw [Sieve.mem_ofArrows_iff] at hg ⊢
    obtain ⟨j, a, rfl⟩ := hg
    obtain ⟨i, b, hb⟩ := hfac j
    exact ⟨i, a ≫ b, by rw [hb, Category.assoc]⟩
  have := Pseudofunctor.DescentData.isEquivalence_toDescentData_of_sieve_le
    modulePullbackPseudofunctor h₁ h₂ (f := f)
  infer_instance


/-! ### Comparisons between the restrictions to two opens -/

section Opens

variable (Ua Ub W W' V : S.Opens)

/-- **`Stacks.Descent.pushUnit` at the inclusions of opens**, with the module kept behind a
variable.  Restricting a module on `Ua` to `W ≤ Ua` and then to `W' ≤ W` is restricting it to
`W'`; the second arrow is `Stacks.Descent.descentShrink`.  Keeping the module variable is what
makes this statement cheap to elaborate; see the warning in the module docstring. -/
theorem pushUnit_comp_opens (hW' : W' ≤ W) (haW : W ≤ Ua) (A : Ua.toScheme.Modules) :
    (pushUnit Ua.ι (S.homOfLE haW) W.ι (S.homOfLE_ι haW)).app A ≫
        ((pushUnit W.ι (S.homOfLE hW') W'.ι (S.homOfLE_ι hW')).app
            ((pullback (S.homOfLE haW)).obj A) ≫
          (pushforward W'.ι).map (pullbackCompHom (S.homOfLE hW') (S.homOfLE haW)
            (S.homOfLE (hW'.trans haW)) (S.homOfLE_homOfLE hW' haW) A)) =
      (pushUnit Ua.ι (S.homOfLE (hW'.trans haW)) W'.ι (S.homOfLE_ι (hW'.trans haW))).app A :=
  (pushUnit_comp Ua.ι (S.homOfLE haW) (S.homOfLE hW') W.ι W'.ι
    (S.homOfLE (hW'.trans haW)) (S.homOfLE_ι haW) (S.homOfLE_ι hW')
    (S.homOfLE_homOfLE hW' haW) A).symm

/-- `Stacks.Descent.isIso_pushUnit_app_app` at the inclusion of an open `W' ≤ W`. -/
theorem isIso_pushUnit_homOfLE_app (hW' : W' ≤ W) (A : W.toScheme.Modules) (hV : V ⊓ W ≤ W') :
    IsIso (((pushUnit W.ι (S.homOfLE hW') W'.ι (S.homOfLE_ι hW')).app A).app V) := by
  exact isIso_pushUnit_homOfLE_app_of_inf_le W W' V hW' A hV

/-- **A morphism between restrictions to `W` is compatible with shrinking to `W' ≤ W`.**  The
hypothesis `hθ` says that `θ'` is the pullback of `θ` along the inclusion of `W'`, in the form
`Stacks.Descent.pullbackCompHom_comp_pullHom` produces it. -/
theorem pushforward_map_comp_shrink (hW' : W' ≤ W) (haW : W ≤ Ua) (hbW : W ≤ Ub)
    (A : Ua.toScheme.Modules) (B : Ub.toScheme.Modules)
    (θ : (pullback (S.homOfLE haW)).obj A ⟶ (pullback (S.homOfLE hbW)).obj B)
    (θ' : (pullback (S.homOfLE (hW'.trans haW))).obj A ⟶
      (pullback (S.homOfLE (hW'.trans hbW))).obj B)
    (hθ : pullbackCompHom (S.homOfLE hW') (S.homOfLE haW) (S.homOfLE (hW'.trans haW))
          (S.homOfLE_homOfLE hW' haW) A ≫ θ' =
        (pullback (S.homOfLE hW')).map θ ≫ pullbackCompHom (S.homOfLE hW') (S.homOfLE hbW)
          (S.homOfLE (hW'.trans hbW)) (S.homOfLE_homOfLE hW' hbW) B) :
    (pushforward W.ι).map θ ≫
        ((pushUnit W.ι (S.homOfLE hW') W'.ι (S.homOfLE_ι hW')).app
            ((pullback (S.homOfLE hbW)).obj B) ≫
          (pushforward W'.ι).map (pullbackCompHom (S.homOfLE hW') (S.homOfLE hbW)
            (S.homOfLE (hW'.trans hbW)) (S.homOfLE_homOfLE hW' hbW) B)) =
      ((pushUnit W.ι (S.homOfLE hW') W'.ι (S.homOfLE_ι hW')).app
            ((pullback (S.homOfLE haW)).obj A) ≫
          (pushforward W'.ι).map (pullbackCompHom (S.homOfLE hW') (S.homOfLE haW)
            (S.homOfLE (hW'.trans haW)) (S.homOfLE_homOfLE hW' haW) A)) ≫
        (pushforward W'.ι).map θ' := by
  rw [← Category.assoc, NatTrans.naturality]
  simp only [Category.assoc, Functor.comp_map, ← Functor.map_comp, hθ]

/-- **`Stacks.Descent.descentShrink` is invertible on sections over an open `V` with
`V ⊓ W ≤ W'`.** -/
theorem isIso_shrink_app (hW' : W' ≤ W) (hbW : W ≤ Ub) (B : Ub.toScheme.Modules)
    (hV : V ⊓ W ≤ W') :
    IsIso (((pushUnit W.ι (S.homOfLE hW') W'.ι (S.homOfLE_ι hW')).app
          ((pullback (S.homOfLE hbW)).obj B) ≫
        (pushforward W'.ι).map (pullbackCompHom (S.homOfLE hW') (S.homOfLE hbW)
          (S.homOfLE (hW'.trans hbW)) (S.homOfLE_homOfLE hW' hbW) B)).app V) := by
  rw [Scheme.Modules.Hom.comp_app]
  have h₁ := isIso_pushUnit_homOfLE_app W W' V hW' ((pullback (S.homOfLE hbW)).obj B) hV
  have h₂ : IsIso (((pushforward W'.ι).map (pullbackCompHom (S.homOfLE hW') (S.homOfLE hbW)
      (S.homOfLE (hW'.trans hbW)) (S.homOfLE_homOfLE hW' hbW) B)).app V) := inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂

/-- **Restricting to `W` and then shrinking to `W' ≤ W` transports a morphism `θ` between
restrictions to its pullback `θ'`.** -/
theorem pushUnit_comp_shrink (hW' : W' ≤ W) (haW : W ≤ Ua) (hbW : W ≤ Ub)
    (A : Ua.toScheme.Modules) (B : Ub.toScheme.Modules)
    (θ : (pullback (S.homOfLE haW)).obj A ⟶ (pullback (S.homOfLE hbW)).obj B)
    (θ' : (pullback (S.homOfLE (hW'.trans haW))).obj A ⟶
      (pullback (S.homOfLE (hW'.trans hbW))).obj B)
    (hθ : pullbackCompHom (S.homOfLE hW') (S.homOfLE haW) (S.homOfLE (hW'.trans haW))
          (S.homOfLE_homOfLE hW' haW) A ≫ θ' =
        (pullback (S.homOfLE hW')).map θ ≫ pullbackCompHom (S.homOfLE hW') (S.homOfLE hbW)
          (S.homOfLE (hW'.trans hbW)) (S.homOfLE_homOfLE hW' hbW) B) :
    (pushUnit Ua.ι (S.homOfLE (hW'.trans haW)) W'.ι (S.homOfLE_ι (hW'.trans haW))).app A ≫
        (pushforward W'.ι).map θ' =
      (pushUnit Ua.ι (S.homOfLE haW) W.ι (S.homOfLE_ι haW)).app A ≫
        (pushforward W.ι).map θ ≫
          ((pushUnit W.ι (S.homOfLE hW') W'.ι (S.homOfLE_ι hW')).app
              ((pullback (S.homOfLE hbW)).obj B) ≫
            (pushforward W'.ι).map (pullbackCompHom (S.homOfLE hW') (S.homOfLE hbW)
              (S.homOfLE (hW'.trans hbW)) (S.homOfLE_homOfLE hW' hbW) B)) := by
  rw [← pushUnit_comp_opens Ua W W' hW' haW A, Category.assoc,
    ← pushforward_map_comp_shrink Ua Ub W W' hW' haW hbW A B θ θ' hθ]

/-- **The comparison between the restrictions to `W` and to `W' ≤ W`, as an existential.**  The
comparison itself is `Stacks.Descent.descentShrink`; it is returned as an existential because
writing it out at the inclusions of opens is what kernel-times-out in this area.  Its three
properties are `Stacks.Descent.isIso_shrink_app`, `Stacks.Descent.pushUnit_comp_opens` and
`Stacks.Descent.pushUnit_comp_shrink`. -/
theorem exists_restrictShrink (hW' : W' ≤ W) (haW : W ≤ Ua) (hbW : W ≤ Ub)
    (A : Ua.toScheme.Modules) (B : Ub.toScheme.Modules)
    (θ : (pullback (S.homOfLE haW)).obj A ⟶ (pullback (S.homOfLE hbW)).obj B)
    (θ' : (pullback (S.homOfLE (hW'.trans haW))).obj A ⟶
      (pullback (S.homOfLE (hW'.trans hbW))).obj B)
    (hθ : pullbackCompHom (S.homOfLE hW') (S.homOfLE haW) (S.homOfLE (hW'.trans haW))
          (S.homOfLE_homOfLE hW' haW) A ≫ θ' =
        (pullback (S.homOfLE hW')).map θ ≫ pullbackCompHom (S.homOfLE hW') (S.homOfLE hbW)
          (S.homOfLE (hW'.trans hbW)) (S.homOfLE_homOfLE hW' hbW) B) :
    ∃ σ : (pushforward W.ι).obj ((pullback (S.homOfLE hbW)).obj B) ⟶
        (pushforward W'.ι).obj ((pullback (S.homOfLE (hW'.trans hbW))).obj B),
      (∀ V₀ : S.Opens, V₀ ⊓ W ≤ W' → IsIso (σ.app V₀)) ∧
      (pushUnit Ub.ι (S.homOfLE (hW'.trans hbW)) W'.ι (S.homOfLE_ι (hW'.trans hbW))).app B =
        (pushUnit Ub.ι (S.homOfLE hbW) W.ι (S.homOfLE_ι hbW)).app B ≫ σ ∧
      (pushUnit Ua.ι (S.homOfLE (hW'.trans haW)) W'.ι (S.homOfLE_ι (hW'.trans haW))).app A ≫
          (pushforward W'.ι).map θ' =
        (pushUnit Ua.ι (S.homOfLE haW) W.ι (S.homOfLE_ι haW)).app A ≫
          (pushforward W.ι).map θ ≫ σ :=
  ⟨_, fun V₀ hV₀ ↦ isIso_shrink_app Ub W W' V₀ hW' hbW B hV₀,
    (pushUnit_comp_opens Ub W W' hW' hbW B).symm,
    pushUnit_comp_shrink Ua Ub W W' hW' haW hbW A B θ θ' hθ⟩

end Opens

/-! ### The unit of the adjunction as a comparison of pushforwards -/

/-- **The unit along `g'` factors through the unit along `g`**, for `h ≫ g = g'`. -/
theorem unit_eq_pushUnit_comp (g : Z ⟶ S) (h : Z' ⟶ Z) (g' : Z' ⟶ S) (hg : h ≫ g = g')
    (M : S.Modules) :
    (pullbackPushforwardAdjunction g').unit.app M =
      (pullbackPushforwardAdjunction g).unit.app M ≫
        (pushUnit g h g' hg).app ((pullback g).obj M) ≫
          (pushforward g').map (pullbackCompHom h g g' hg M) := by
  subst hg
  rw [pushUnit_app, pullbackCompHom, pullbackCongr_rfl_hom, pushforwardCongr_rfl_hom,
    unit_pullbackPushforwardAdjunction_comp]
  simp

/-- **The adjunct of a morphism out of a pullback along `g'` is the adjunct along `g` followed
by `Stacks.Descent.pushUnit`**, when the two morphisms correspond under
`Stacks.Descent.pullbackCompHom`. -/
theorem unit_comp_pushforward_map (g : Z ⟶ S) (h : Z' ⟶ Z) (g' : Z' ⟶ S) (hg : h ≫ g = g')
    {M : S.Modules} {K : Z.Modules} (ε : (pullback g).obj M ⟶ K)
    (ε' : (pullback g').obj M ⟶ (pullback h).obj K)
    (hε : pullbackCompHom h g g' hg M ≫ ε' = (pullback h).map ε) :
    (pullbackPushforwardAdjunction g').unit.app M ≫ (pushforward g').map ε' =
      ((pullbackPushforwardAdjunction g).unit.app M ≫ (pushforward g).map ε) ≫
        (pushUnit g h g' hg).app K := by
  rw [unit_eq_pushUnit_comp g h g' hg M, Category.assoc, Category.assoc, Category.assoc,
    ← Functor.map_comp, hε]
  exact congrArg (fun x ↦ (pullbackPushforwardAdjunction g).unit.app M ≫ x)
    (NatTrans.naturality (pushUnit g h g' hg) ε).symm

/-- The inverse of the composition isomorphism of `AlgebraicGeometry.modulePullbackPseudofunctor`
for `c ≫ h = k`, at `A`, is `Stacks.Descent.pullbackCompHom c h k hk A`. -/
theorem mapComp'_inv_app_eq (c : Z'' ⟶ Z') (h : Z' ⟶ Z) (k : Z'' ⟶ Z) (hk : c ≫ h = k)
    (A : Z.Modules) :
    (modulePullbackPseudofunctor.mapComp' h.op.toLoc c.op.toLoc k.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hk])).inv.toNatTrans.app A =
      pullbackCompHom c h k hk A := by
  subst hk; rfl

/-- The transition of the canonical descent datum of `M` is the comparison between the two
descriptions of the pullback of `M`.  Stated for an arbitrary pseudofunctor, where no
`CategoryTheory.Category` instance has to be compared. -/
theorem ofObj_hom_comp_mapComp'_inv_app {C : Type u₂} [Category.{v₂} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat} {ι : Type w} {S₀ : C} {X : ι → C}
    {f : ∀ i, X i ⟶ S₀} (M : F.obj (.mk (op S₀))) {T : C} (q : T ⟶ S₀) {i₁ i₂ : ι}
    (f₁ : T ⟶ X i₁) (f₂ : T ⟶ X i₂) (h₁ : f₁ ≫ f i₁ = q) (h₂ : f₂ ≫ f i₂ = q) :
    (Pseudofunctor.DescentData.ofObj (f := f) M).hom q f₁ f₂ h₁ h₂ ≫
        (F.mapComp' (f i₂).op.toLoc f₂.op.toLoc q.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₂])).inv.toNatTrans.app M =
      (F.mapComp' (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₁])).inv.toNatTrans.app M :=
  (Iso.comp_inv_eq ((Cat.Hom.toNatIso (F.mapComp' (f i₂).op.toLoc f₂.op.toLoc q.op.toLoc
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, h₂]))).app M)).2 rfl

/-- **The transition of the canonical descent datum of `N`, through
`Stacks.Descent.pullbackCompHom`.** -/
theorem ofObj_hom_comp_pullbackCompHom {I : Type v} {Y : I → Scheme.{u}} {f : ∀ i, Y i ⟶ S}
    (N : S.Modules) {T : Scheme.{u}} (q : T ⟶ S) {i₁ i₂ : I}
    (f₁ : T ⟶ Y i₁) (f₂ : T ⟶ Y i₂) (h₁ : f₁ ≫ f i₁ = q) (h₂ : f₂ ≫ f i₂ = q) :
    (Pseudofunctor.DescentData.ofObj (F := modulePullbackPseudofunctor) (f := f) N).hom
          q f₁ f₂ h₁ h₂ ≫ pullbackCompHom f₂ (f i₂) q h₂ N =
      pullbackCompHom f₁ (f i₁) q h₁ N := by
  rw [← mapComp'_inv_app_eq f₂ (f i₂) q h₂ N, ← mapComp'_inv_app_eq f₁ (f i₁) q h₁ N]
  exact ofObj_hom_comp_mapComp'_inv_app (F := modulePullbackPseudofunctor) N q f₁ f₂ h₁ h₂

section Retype

variable {I : Type v} {U : I → S.Opens}
  (D : modulePullbackPseudofunctor.DescentData (fun i ↦ (U i).ι))

/-- **`D.obj a`, retyped as an object of `(U a).toScheme.Modules`.**  A term of type
`↑(AlgebraicGeometry.modulePullbackPseudofunctor.obj _)` is definitionally one of type
`AlgebraicGeometry.Scheme.Modules`, but the two are not syntactically equal, and crossing
between them repeatedly inside one declaration is what exhausts the kernel's budget here.
Crossing once, in this definition and in `Stacks.Descent.descentHom`, keeps the statements
below free. -/
def descentObj (a : I) : (U a).toScheme.Modules := D.obj a

/-- **A transition of `D`, retyped at `Stacks.Descent.descentObj`.**  See the comment there. -/
def descentHom {T : Scheme.{u}} (q : T ⟶ S) {a b : I} (f₁ : T ⟶ (U a).toScheme)
    (f₂ : T ⟶ (U b).toScheme) (h₁ : f₁ ≫ (U a).ι = q) (h₂ : f₂ ≫ (U b).ι = q) :
    (pullback f₁).obj (descentObj D a) ⟶ (pullback f₂).obj (descentObj D b) :=
  D.hom q f₁ f₂ h₁ h₂

/-- **`Stacks.Descent.pullbackCompHom` intertwines a transition of a descent datum with its
pullback.**  This is `Stacks.Descent.pullbackCompHom_comp_pullHom` fed by
`CategoryTheory.Pseudofunctor.DescentData.pullHom_hom`; it is stated at variable morphisms, and
the conclusion mentions neither
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom` nor `D.hom`, which is what makes
it usable at the inclusions of opens. -/
theorem pullbackCompHom_comp_descentHom {T T' : Scheme.{u}} (q : T ⟶ S) (q' : T' ⟶ S)
    (c : T' ⟶ T) (hq : c ≫ q = q') {a b : I} (f₁ : T ⟶ (U a).toScheme)
    (f₂ : T ⟶ (U b).toScheme) (g₁ : T' ⟶ (U a).toScheme) (g₂ : T' ⟶ (U b).toScheme)
    (hf₁ : f₁ ≫ (U a).ι = q) (hf₂ : f₂ ≫ (U b).ι = q)
    (hg₁ : c ≫ f₁ = g₁) (hg₂ : c ≫ f₂ = g₂)
    (hgq₁ : g₁ ≫ (U a).ι = q') (hgq₂ : g₂ ≫ (U b).ι = q') :
    pullbackCompHom c f₁ g₁ hg₁ (descentObj D a) ≫ descentHom D q' g₁ g₂ hgq₁ hgq₂ =
      (pullback c).map (descentHom D q f₁ f₂ hf₁ hf₂) ≫
        pullbackCompHom c f₂ g₂ hg₂ (descentObj D b) :=
  pullbackCompHom_comp_pullHom f₁ f₂ (D.hom q f₁ f₂ hf₁ hf₂) c g₁ g₂ hg₁ hg₂ _
    (D.pullHom_hom c q q' hq f₁ f₂ hf₁ hf₂ g₁ g₂ hg₁ hg₂)

/-- `CategoryTheory.Pseudofunctor.DescentData.hom_comp` at
`Stacks.Descent.descentHom`. -/
theorem descentHom_comp {T : Scheme.{u}} (q : T ⟶ S) {a b c : I} (f₁ : T ⟶ (U a).toScheme)
    (f₂ : T ⟶ (U b).toScheme) (f₃ : T ⟶ (U c).toScheme) (h₁ : f₁ ≫ (U a).ι = q)
    (h₂ : f₂ ≫ (U b).ι = q) (h₃ : f₃ ≫ (U c).ι = q) :
    descentHom D q f₁ f₂ h₁ h₂ ≫ descentHom D q f₂ f₃ h₂ h₃ = descentHom D q f₁ f₃ h₁ h₃ :=
  D.hom_comp q f₁ f₂ f₃ h₁ h₂ h₃

/-- `CategoryTheory.Pseudofunctor.DescentData.hom_self` at
`Stacks.Descent.descentHom`. -/
theorem descentHom_self {T : Scheme.{u}} (q : T ⟶ S) {a : I} (f₁ : T ⟶ (U a).toScheme)
    (h₁ : f₁ ≫ (U a).ι = q) : descentHom D q f₁ f₁ h₁ h₁ = 𝟙 _ :=
  D.hom_self q f₁ h₁

end Retype

/-- **A morphism into a pushforward along an open immersion whose restriction is invertible is
the adjunct of an isomorphism.**  This is the step from the projections of the glued module to
the isomorphisms of a descent datum: it uses
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorAdjCounitIso` (in the form of the counit of
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction`), and the isomorphism is returned as an
existential together with the only property used, namely that `φ` is its adjunct. -/
theorem exists_pullbackIso {X : Scheme.{u}} (g : X ⟶ S) [IsOpenImmersion g] {M : S.Modules}
    {K : X.Modules} (φ : M ⟶ (pushforward g).obj K)
    (hφ : IsIso ((restrictFunctor g).map φ)) :
    ∃ ε : (pullback g).obj M ≅ K,
      (pullbackPushforwardAdjunction g).unit.app M ≫ (pushforward g).map ε.hom = φ := by
  have hδ : IsIso ((restrictAdjunction g).counit.app K) := inferInstance
  refine ⟨((restrictFunctorIsoPullback g).app M).symm ≪≫ asIso ((restrictFunctor g).map φ) ≪≫
    asIso ((restrictAdjunction g).counit.app K), ?_⟩
  have hu : (pullbackPushforwardAdjunction g).unit.app M =
      (restrictAdjunction g).unit.app M ≫
        (pushforward g).map ((restrictFunctorIsoPullback g).hom.app M) :=
    (Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction g)
      (pullbackPushforwardAdjunction g) M).symm
  rw [hu]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Iso.app_inv, Functor.map_comp,
    Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, ← Functor.comp_map,
    ← NatTrans.naturality_assoc (restrictAdjunction g).unit φ]
  simp

/-- **The descent-datum compatibility over a chosen pullback.**  Let `g₁`, `g₂` be morphisms to
`S`, let `q` factor through both via `p₁` and `p₂`, and let `ε₁`, `ε₂` be morphisms from the
pullbacks of `N` whose adjuncts `φ₁`, `φ₂` satisfy the matching condition `h` over `q`.  Then
the `ε` commute with any morphism `θ` of the pullbacks over `q` and with the comparison `ω` of
the canonical descent datum of `N`.  This is the `comm` hypothesis of
`CategoryTheory.Pseudofunctor.DescentData'.isoMk`; it is proved by the injectivity of the
adjunction bijection along `q`. -/
theorem descentData_comm_of_unit {Z₁ Z₂ T : Scheme.{u}} {g₁ : Z₁ ⟶ S} {g₂ : Z₂ ⟶ S}
    {q : T ⟶ S} (p₁ : T ⟶ Z₁) (p₂ : T ⟶ Z₂) (hq₁ : p₁ ≫ g₁ = q) (hq₂ : p₂ ≫ g₂ = q)
    {N : S.Modules} {K₁ : Z₁.Modules} {K₂ : Z₂.Modules}
    (ε₁ : (pullback g₁).obj N ⟶ K₁) (ε₂ : (pullback g₂).obj N ⟶ K₂)
    (θ : (pullback p₁).obj K₁ ⟶ (pullback p₂).obj K₂)
    (ω : (pullback p₁).obj ((pullback g₁).obj N) ⟶ (pullback p₂).obj ((pullback g₂).obj N))
    (hω : ω ≫ pullbackCompHom p₂ g₂ q hq₂ N = pullbackCompHom p₁ g₁ q hq₁ N)
    (h : ((pullbackPushforwardAdjunction g₁).unit.app N ≫ (pushforward g₁).map ε₁) ≫
          (pushUnit g₁ p₁ q hq₁).app K₁ ≫ (pushforward q).map θ =
        ((pullbackPushforwardAdjunction g₂).unit.app N ≫ (pushforward g₂).map ε₂) ≫
          (pushUnit g₂ p₂ q hq₂).app K₂) :
    (pullback p₁).map ε₁ ≫ θ = ω ≫ (pullback p₂).map ε₂ := by
  have h₁ := unit_comp_pushforward_map g₁ p₁ q hq₁ ε₁
    (inv (pullbackCompHom p₁ g₁ q hq₁ N) ≫ (pullback p₁).map ε₁) (IsIso.hom_inv_id_assoc _ _)
  have h₂ := unit_comp_pushforward_map g₂ p₂ q hq₂ ε₂
    (inv (pullbackCompHom p₂ g₂ q hq₂ N) ≫ (pullback p₂).map ε₂) (IsIso.hom_inv_id_assoc _ _)
  have key : (inv (pullbackCompHom p₁ g₁ q hq₁ N) ≫ (pullback p₁).map ε₁) ≫ θ =
      inv (pullbackCompHom p₂ g₂ q hq₂ N) ≫ (pullback p₂).map ε₂ := by
    refine ((pullbackPushforwardAdjunction q).homEquiv N ((pullback p₂).obj K₂)).injective ?_
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      h₁, h₂]
    simp only [Category.assoc] at h ⊢
    exact h
  have hω' : ω = pullbackCompHom p₁ g₁ q hq₁ N ≫ inv (pullbackCompHom p₂ g₂ q hq₂ N) := by
    rw [← hω, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hω', Category.assoc, ← key]
  simp only [Category.assoc]
  rw [IsIso.hom_inv_id_assoc]

/-! ### Sections of the sheaf of matched families -/

section Matched

variable {I : Type u} {P : I → S.Modules} {B : I → I → S.Modules}
  (β : ∀ i j, P i ⟶ B i j) (γ : ∀ i j, P j ⟶ B i j)

/-- **The `i`-th projection of `Stacks.Descent.glueMatched` is bijective on sections over an
open where `γ i j` is invertible for every `j`.**  Injectivity: the `j`-th component of a
section is determined by its `i`-th one.  Surjectivity: the `j`-th component of the preimage of
`t` is the image of `t` under `β i j` followed by the inverse of `γ i j`, and the matching
condition for a pair `(j, k)` is the hypothesis `hmatch`. -/
theorem bijective_glueMatchedπ_app (V : S.Opens) (i : I)
    (hγ : ∀ j, IsIso ((γ i j).app V)) (hii : β i i = γ i i)
    (hmatch : ∀ (j k : I) (z : Γ(P i, V)) (x : Γ(P j, V)) (y : Γ(P k, V)),
      (γ i j).app V x = (β i j).app V z → (γ i k).app V y = (β i k).app V z →
        (β j k).app V x = (γ j k).app V y) :
    Function.Bijective ((glueMatchedπ β γ i).app V) := by
  constructor
  · intro a b hab
    refine glueMatchedπ_app_injective β γ V fun j ↦ ?_
    have hj := hγ j
    refine (ConcreteCategory.bijective_of_isIso ((γ i j).app V)).1 ?_
    have h := ConcreteCategory.congr_hom (congrArg (fun α ↦ Scheme.Modules.Hom.app α V)
      (glueMatchedπ_comp β γ i j))
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h
    rw [← h a, ← h b, hab]
  · intro t
    choose s hs using fun j ↦
      have := hγ j
      (ConcreteCategory.bijective_of_isIso ((γ i j).app V)).2 ((β i j).app V t)
    have hsi : s i = t := by
      have hi := hγ i
      refine (ConcreteCategory.bijective_of_isIso ((γ i i).app V)).1 ?_
      rw [hs i, hii]
    obtain ⟨a, ha⟩ := exists_glueMatchedπ_app β γ V s
      (fun j k ↦ hmatch j k t (s j) (s k) (hs j) (hs k))
    exact ⟨a, (ha i).trans hsi⟩

end Matched

/-! ### Chosen pullbacks of inclusions of opens -/

/-- The intersection of two opens, as a chosen pullback of their inclusions. -/
def chosenPullbackOpens (U₁ U₂ : S.Opens) : Limits.ChosenPullback U₁.ι U₂.ι where
  pullback := (U₁ ⊓ U₂).toScheme
  p₁ := S.homOfLE inf_le_left
  p₂ := S.homOfLE inf_le_right
  condition := (isPullback_opens_inf U₁ U₂).w
  isLimit := (isPullback_opens_inf U₁ U₂).isLimit
  p := (U₁ ⊓ U₂).ι
  hp₁ := S.homOfLE_ι _

/-- The first projection of `Stacks.Descent.chosenPullbackOpens U₁ U₂` is the inclusion of
`U₁ ⊓ U₂` into `U₁`. -/
@[simp]
theorem chosenPullbackOpens_p₁ (U₁ U₂ : S.Opens) :
    (chosenPullbackOpens U₁ U₂).p₁ = S.homOfLE inf_le_left := rfl

/-- The second projection of `Stacks.Descent.chosenPullbackOpens U₁ U₂` is the inclusion of
`U₁ ⊓ U₂` into `U₂`. -/
@[simp]
theorem chosenPullbackOpens_p₂ (U₁ U₂ : S.Opens) :
    (chosenPullbackOpens U₁ U₂).p₂ = S.homOfLE inf_le_right := rfl

/-- The morphism to `S` of `Stacks.Descent.chosenPullbackOpens U₁ U₂` is the inclusion of
`U₁ ⊓ U₂`. -/
@[simp]
theorem chosenPullbackOpens_p (U₁ U₂ : S.Opens) :
    (chosenPullbackOpens U₁ U₂).p = (U₁ ⊓ U₂).ι := rfl

/-- The threefold wide pullback of the inclusions of three opens, compatible with
`Stacks.Descent.chosenPullbackOpens`. -/
def chosenPullback₃Opens (U₁ U₂ U₃ : S.Opens) :
    Limits.ChosenPullback₃ (chosenPullbackOpens U₁ U₂) (chosenPullbackOpens U₂ U₃)
      (chosenPullbackOpens U₁ U₃) where
  chosenPullback :=
    { pullback := ((U₁ ⊓ U₂) ⊓ (U₂ ⊓ U₃)).toScheme
      p₁ := S.homOfLE inf_le_left
      p₂ := S.homOfLE inf_le_right
      condition := (isPullback_opens_inf_le (inf_le_right : U₁ ⊓ U₂ ≤ U₂)
        (inf_le_left : U₂ ⊓ U₃ ≤ U₂)).w
      isLimit := (isPullback_opens_inf_le (inf_le_right : U₁ ⊓ U₂ ≤ U₂)
        (inf_le_left : U₂ ⊓ U₃ ≤ U₂)).isLimit
      p := S.homOfLE (inf_le_left.trans inf_le_right)
      hp₁ := by dsimp only [chosenPullbackOpens]; rw [Scheme.homOfLE_homOfLE] }
  p := ((U₁ ⊓ U₂) ⊓ (U₂ ⊓ U₃)).ι
  p₁ := S.homOfLE (inf_le_left.trans inf_le_left)
  p₃ := S.homOfLE (inf_le_right.trans inf_le_right)
  l :=
    { f := S.homOfLE (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right))
      f_p₁ := by dsimp only [chosenPullbackOpens]; rw [Scheme.homOfLE_homOfLE]
      f_p₂ := by dsimp only [chosenPullbackOpens]; rw [Scheme.homOfLE_homOfLE]
      f_p := by dsimp only [chosenPullbackOpens]; rw [Scheme.homOfLE_ι] }
  hp₁ := by dsimp only [chosenPullbackOpens]; rw [Scheme.homOfLE_homOfLE]
  hp₃ := by dsimp only [chosenPullbackOpens]; rw [Scheme.homOfLE_homOfLE]

/-! ### The gluing -/

section Glue

variable {I : Type u} {U : I → S.Opens}
  (D : modulePullbackPseudofunctor.DescentData (fun i ↦ (U i).ι))

/-- The restriction of `D.obj a` to an open `W ≤ U a`, pushed forward to `S`.  This is
`Stacks.Descent.descentRestrict` written with `Stacks.Descent.descentObj`, so that the
comparisons of the section "Comparisons between the restrictions to two opens" apply to it
without any defeq between the two spellings of `D.obj a`. -/
def glueRestrict (W : S.Opens) (a : I) (ha : W ≤ U a) : S.Modules :=
  (pushforward W.ι).obj ((pullback (S.homOfLE ha)).obj (descentObj D a))

/-- The comparison from the pushforward of `D.obj a` to its restriction to `W ≤ U a`. -/
def glueRestrictUnit (W : S.Opens) (a : I) (ha : W ≤ U a) :
    (pushforward (U a).ι).obj (descentObj D a) ⟶ glueRestrict D W a ha :=
  (pushUnit (U a).ι (S.homOfLE ha) W.ι (S.homOfLE_ι ha)).app (descentObj D a)

/-- The transition of `D` over an open `W` contained in both `U a` and `U b`, pushed forward
to `S`. -/
def glueTransition (W : S.Opens) (a b : I) (ha : W ≤ U a) (hb : W ≤ U b) :
    glueRestrict D W a ha ⟶ glueRestrict D W b hb :=
  (pushforward W.ι).map
    (descentHom D W.ι (S.homOfLE ha) (S.homOfLE hb) (S.homOfLE_ι ha) (S.homOfLE_ι hb))

/-- The transitions `Stacks.Descent.glueTransition` over `W` compose: the transition from `a` to
`b` followed by the one from `b` to `c` is the transition from `a` to `c`. -/
@[reassoc]
theorem glueTransition_comp (W : S.Opens) (a b c : I) (ha : W ≤ U a) (hb : W ≤ U b)
    (hc : W ≤ U c) :
    glueTransition D W a b ha hb ≫ glueTransition D W b c hb hc =
      glueTransition D W a c ha hc :=
  ((pushforward W.ι).map_comp _ _).symm.trans
    (congrArg (pushforward W.ι).map (descentHom_comp D W.ι _ _ _ _ _ _))

/-- The transition `Stacks.Descent.glueTransition` from `a` to itself over `W` is the identity,
for any two proofs of `W ≤ U a`. -/
theorem glueTransition_self (W : S.Opens) (a : I) (ha : W ≤ U a) (ha' : W ≤ U a) :
    glueTransition D W a a ha ha' = 𝟙 _ :=
  (congrArg (pushforward W.ι).map (descentHom_self D W.ι (S.homOfLE ha) (S.homOfLE_ι ha))).trans
    ((pushforward W.ι).map_id _)

/-- The `(i, j)` entry of the multicospan whose multiequalizer glues `D`. -/
def glueOverlap (i j : I) : S.Modules := glueRestrict D (U i ⊓ U j) j inf_le_right

/-- Restrict `D.obj i` to the overlap `U i ⊓ U j` and apply the transition of `D`. -/
def glueFst (i j : I) : (pushforward (U i).ι).obj (descentObj D i) ⟶ glueOverlap D i j :=
  glueRestrictUnit D (U i ⊓ U j) i inf_le_left ≫
    glueTransition D (U i ⊓ U j) i j inf_le_left inf_le_right

/-- Restrict `D.obj j` to the overlap `U i ⊓ U j`. -/
def glueSnd (i j : I) : (pushforward (U j).ι).obj (descentObj D j) ⟶ glueOverlap D i j :=
  glueRestrictUnit D (U i ⊓ U j) j inf_le_right

/-- **The module on `S` glued from a descent datum for a family of opens.**  Its sections over
an open `V` are the families of sections of the `D.obj j` over `(U j).ι ⁻¹ᵁ V` that agree on the
overlaps after the transitions of `D`. -/
def glueModule : S.Modules :=
  glueMatched (P := fun j ↦ (pushforward (U j).ι).obj (descentObj D j)) (B := glueOverlap D)
    (glueFst D) (glueSnd D)

/-- Over the overlap `U i ⊓ U i`, `Stacks.Descent.glueFst D i i` and
`Stacks.Descent.glueSnd D i i` agree. -/
theorem glueFst_self (i : I) : glueFst D i i = glueSnd D i i :=
  (congrArg (fun φ ↦ glueRestrictUnit D (U i ⊓ U i) i inf_le_left ≫ φ)
      (glueTransition_self D (U i ⊓ U i) i inf_le_left inf_le_right)).trans
    (Category.comp_id _)

/-- **`Stacks.Descent.glueSnd` is invertible on sections over an open `V` with
`V ⊓ U j ≤ U i ⊓ U j`.** -/
theorem isIso_glueSnd_app (i j : I) (V : S.Opens) (hV : V ⊓ U j ≤ U i ⊓ U j) :
    IsIso ((glueSnd D i j).app V) := by
  exact isIso_pushUnit_homOfLE_app_of_inf_le (U j) (U i ⊓ U j) V inf_le_right
    (descentObj D j) hV

/-- **The comparison between the restrictions to `W` and to a smaller open `W'`, in the
vocabulary of `Stacks.Descent.glueRestrict`.**  The comparison is kept existential and the
proofs of `W' ≤ U a`, `W' ≤ U b` are taken as arguments, so that a consumer using the lemma
several times over one triple overlap gets syntactically identical restriction comparisons.

Spelling the two `≤` proofs the same way matters for more than `rw`: feeding
`AlgebraicGeometry.Scheme.homOfLE` two proofs of the same inequality is proof-irrelevant but
*not* free, because `AlgebraicGeometry.Scheme.Modules.pullbackCongr` wraps the morphism in an
`CategoryTheory.eqToIso`, and crossing that difference inside this proof costs about thirty
seconds of kernel time. -/
theorem exists_glueShrink (a b : I) (W W' : S.Opens) (hWa : W ≤ U a) (hWb : W ≤ U b)
    (ha : W' ≤ U a) (hb : W' ≤ U b) (hW' : W' ≤ W) :
    ∃ σ : glueRestrict D W b hWb ⟶ glueRestrict D W' b hb,
      (∀ V : S.Opens, V ⊓ W ≤ W' → IsIso (σ.app V)) ∧
      glueRestrictUnit D W' b hb = glueRestrictUnit D W b hWb ≫ σ ∧
      glueRestrictUnit D W' a ha ≫ glueTransition D W' a b ha hb =
        glueRestrictUnit D W a hWa ≫ glueTransition D W a b hWa hWb ≫ σ :=
  ⟨_, fun V hV ↦ isIso_shrink_app (U b) W W' V hW' hWb (descentObj D b) hV,
    (pushUnit_comp_opens (U b) W W' hW' hWb (descentObj D b)).symm,
    pushUnit_comp_shrink (U a) (U b) W W' hW' hWa hWb (descentObj D a) (descentObj D b)
      (descentHom D W.ι (S.homOfLE hWa) (S.homOfLE hWb) (S.homOfLE_ι hWa) (S.homOfLE_ι hWb))
      (descentHom D W'.ι (S.homOfLE (hW'.trans hWa)) (S.homOfLE (hW'.trans hWb))
        (S.homOfLE_ι _) (S.homOfLE_ι _))
      (pullbackCompHom_comp_descentHom D W.ι W'.ι (S.homOfLE hW') (S.homOfLE_ι hW')
        (S.homOfLE hWa) (S.homOfLE hWb) (S.homOfLE (hW'.trans hWa))
        (S.homOfLE (hW'.trans hWb)) (S.homOfLE_ι hWa) (S.homOfLE_ι hWb)
        (S.homOfLE_homOfLE hW' hWa) (S.homOfLE_homOfLE hW' hWb) (S.homOfLE_ι _)
        (S.homOfLE_ι _))⟩

/-- **The matching condition for a pair `(j, k)` follows from the matching conditions against a
fixed `i` over an open contained in `U i`.**  This is the cocycle step of the gluing: the three
comparisons down to `U i ⊓ U j ⊓ U k` turn the two hypotheses into statements about the
transitions of `D` over that triple overlap, where `Stacks.Descent.glueTransition_comp` closes
the argument; the comparison for the pair `(j, k)` is invertible on sections over `V` because
`V ≤ U i`. -/
theorem glueFst_app_eq_glueSnd_app (i j k : I) (V : S.Opens) (hVi : V ≤ U i)
    (z : Γ((pushforward (U i).ι).obj (descentObj D i), V))
    (x : Γ((pushforward (U j).ι).obj (descentObj D j), V))
    (y : Γ((pushforward (U k).ι).obj (descentObj D k), V))
    (hx : (glueSnd D i j).app V x = (glueFst D i j).app V z)
    (hy : (glueSnd D i k).app V y = (glueFst D i k).app V z) :
    (glueFst D j k).app V x = (glueSnd D j k).app V y := by
  have hi3 : U i ⊓ U j ⊓ U k ≤ U i := inf_le_left.trans inf_le_left
  have hj3 : U i ⊓ U j ⊓ U k ≤ U j := inf_le_left.trans inf_le_right
  have hk3 : U i ⊓ U j ⊓ U k ≤ U k := inf_le_right
  obtain ⟨σ₁, hiso₁, hsnd₁, hfst₁⟩ := exists_glueShrink D j k (U j ⊓ U k) (U i ⊓ U j ⊓ U k)
    inf_le_left inf_le_right hj3 hk3 (le_inf hj3 hk3)
  obtain ⟨σ₂, -, hsnd₂, hfst₂⟩ := exists_glueShrink D i j (U i ⊓ U j) (U i ⊓ U j ⊓ U k)
    inf_le_left inf_le_right hi3 hj3 inf_le_left
  obtain ⟨σ₃, -, hsnd₃, hfst₃⟩ := exists_glueShrink D i k (U i ⊓ U k) (U i ⊓ U j ⊓ U k)
    inf_le_left inf_le_right hi3 hk3 (le_inf hi3 hk3)
  have hiso := hiso₁ V (le_inf (le_inf (inf_le_left.trans hVi)
    (inf_le_right.trans inf_le_left)) (inf_le_right.trans inf_le_right))
  have app : ∀ {M N : S.Modules} {φ ψ : M ⟶ N}, φ = ψ → ∀ t : Γ(M, V),
      Scheme.Modules.Hom.app φ V t = Scheme.Modules.Hom.app ψ V t :=
    fun h t ↦ ConcreteCategory.congr_hom (congrArg (fun α ↦ Scheme.Modules.Hom.app α V) h) t
  have g₁ : glueFst D j k ≫ σ₁ =
      glueRestrictUnit D (U i ⊓ U j ⊓ U k) j hj3 ≫
        glueTransition D (U i ⊓ U j ⊓ U k) j k hj3 hk3 :=
    (Category.assoc _ _ _).trans hfst₁.symm
  have g₂ : glueSnd D j k ≫ σ₁ = glueRestrictUnit D (U i ⊓ U j ⊓ U k) k hk3 := hsnd₁.symm
  have g₃ : glueSnd D i j ≫ σ₂ = glueRestrictUnit D (U i ⊓ U j ⊓ U k) j hj3 := hsnd₂.symm
  have g₄ : glueFst D i j ≫ σ₂ =
      glueRestrictUnit D (U i ⊓ U j ⊓ U k) i hi3 ≫
        glueTransition D (U i ⊓ U j ⊓ U k) i j hi3 hj3 :=
    (Category.assoc _ _ _).trans hfst₂.symm
  have g₅ : glueSnd D i k ≫ σ₃ = glueRestrictUnit D (U i ⊓ U j ⊓ U k) k hk3 := hsnd₃.symm
  have g₆ : glueFst D i k ≫ σ₃ =
      glueRestrictUnit D (U i ⊓ U j ⊓ U k) i hi3 ≫
        glueTransition D (U i ⊓ U j ⊓ U k) i k hi3 hk3 :=
    (Category.assoc _ _ _).trans hfst₃.symm
  have e₁ : σ₁.app V ((glueFst D j k).app V x) =
      (glueTransition D (U i ⊓ U j ⊓ U k) j k hj3 hk3).app V
        ((glueRestrictUnit D (U i ⊓ U j ⊓ U k) j hj3).app V x) := app g₁ x
  have e₂ : σ₁.app V ((glueSnd D j k).app V y) =
      (glueRestrictUnit D (U i ⊓ U j ⊓ U k) k hk3).app V y := app g₂ y
  have e₃ : σ₂.app V ((glueSnd D i j).app V x) =
      (glueRestrictUnit D (U i ⊓ U j ⊓ U k) j hj3).app V x := app g₃ x
  have e₄ : σ₂.app V ((glueFst D i j).app V z) =
      (glueTransition D (U i ⊓ U j ⊓ U k) i j hi3 hj3).app V
        ((glueRestrictUnit D (U i ⊓ U j ⊓ U k) i hi3).app V z) := app g₄ z
  have e₅ : σ₃.app V ((glueSnd D i k).app V y) =
      (glueRestrictUnit D (U i ⊓ U j ⊓ U k) k hk3).app V y := app g₅ y
  have e₆ : σ₃.app V ((glueFst D i k).app V z) =
      (glueTransition D (U i ⊓ U j ⊓ U k) i k hi3 hk3).app V
        ((glueRestrictUnit D (U i ⊓ U j ⊓ U k) i hi3).app V z) := app g₆ z
  have e₇ : (glueTransition D (U i ⊓ U j ⊓ U k) j k hj3 hk3).app V
        ((glueTransition D (U i ⊓ U j ⊓ U k) i j hi3 hj3).app V
          ((glueRestrictUnit D (U i ⊓ U j ⊓ U k) i hi3).app V z)) =
      (glueTransition D (U i ⊓ U j ⊓ U k) i k hi3 hk3).app V
        ((glueRestrictUnit D (U i ⊓ U j ⊓ U k) i hi3).app V z) :=
    app (glueTransition_comp D (U i ⊓ U j ⊓ U k) i j k hi3 hj3 hk3) _
  have hx' := congrArg (fun w ↦ Scheme.Modules.Hom.app σ₂ V w) hx
  have hy' := congrArg (fun w ↦ Scheme.Modules.Hom.app σ₃ V w) hy
  refine (ConcreteCategory.bijective_of_isIso (σ₁.app V)).1 ?_
  rw [e₁, e₂, ← e₃, hx', e₄, e₇, ← e₆, ← hy', e₅]

/-- **The `i`-th projection of the glued module is bijective on sections over an open contained
in `U i`.** -/
theorem bijective_glueMatchedπ_app_glue (i : I) (V : S.Opens) (hVi : V ≤ U i) :
    Function.Bijective ((glueMatchedπ (glueFst D) (glueSnd D) i).app V) :=
  bijective_glueMatchedπ_app (glueFst D) (glueSnd D) V i
    (fun j ↦ isIso_glueSnd_app D i j V (le_inf (inf_le_left.trans hVi) inf_le_right))
    (glueFst_self D i)
    (fun j k z a b ha hb ↦ glueFst_app_eq_glueSnd_app D i j k V hVi z a b ha hb)

/-- **The `i`-th projection of the glued module becomes an isomorphism after restriction to
`U i`.**  Every open of `(U i).toScheme` is of the form `(U i).ι ''ᵁ W₀`, which is contained in
`U i`, and `AlgebraicGeometry.Scheme.Modules.restrictFunctor` is a pushforward along
`AlgebraicGeometry.Scheme.Hom.opensFunctor`, so its action on sections is evaluation at that
open. -/
theorem isIso_restrictFunctor_map_glueMatchedπ (i : I) :
    IsIso ((restrictFunctor (U i).ι).map (glueMatchedπ (glueFst D) (glueSnd D) i)) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W₀
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_glueMatchedπ_app_glue D i ((U i).ι ''ᵁ W₀) ((U i).ι_image_le W₀))

end Glue

/-! ### Essential surjectivity -/

/-- **Essential surjectivity of the descent functor for a family of inclusions of opens.**  No
hypothesis on the family is needed: the glued module `Stacks.Descent.glueModule` restricts to
the given descent datum over every member, whether or not they cover `S`. -/
theorem essSurj_toDescentData_opens {S : Scheme.{u}} {I : Type u} (U : I → S.Opens) :
    (modulePullbackPseudofunctor.toDescentData (fun i ↦ (U i).ι)).EssSurj where
  mem_essImage D := by
    choose e he using fun i ↦ exists_pullbackIso (U i).ι
      (glueMatchedπ (glueFst D) (glueSnd D) i) (isIso_restrictFunctor_map_glueMatchedπ D i)
    refine ⟨glueModule D, ⟨(Pseudofunctor.DescentData'.descentDataEquivalence
      modulePullbackPseudofunctor (fun a b ↦ chosenPullbackOpens (U a) (U b))
      (fun a b c ↦ chosenPullback₃Opens (U a) (U b) (U c))).fullyFaithfulInverse.preimageIso
        (Pseudofunctor.DescentData'.isoMk (fun i ↦ e i) ?_)⟩⟩
    intro i₁ i₂
    have hmatch := glueMatchedπ_comp (glueFst D) (glueSnd D) i₁ i₂
    rw [← he i₁, ← he i₂] at hmatch
    exact descentData_comm_of_unit (chosenPullbackOpens (U i₁) (U i₂)).p₁
      (chosenPullbackOpens (U i₁) (U i₂)).p₂ (chosenPullbackOpens (U i₁) (U i₂)).hp₁
      (chosenPullbackOpens (U i₁) (U i₂)).hp₂ (e i₁).hom (e i₂).hom _ _
      (ofObj_hom_comp_pullbackCompHom (glueModule D) _ _ _ _ _) hmatch

/-- **Essential surjectivity of the descent functor for a Zariski covering family.**  With
`Stacks.Descent.full_toDescentData` and
`Stacks.Descent.faithful_toDescentData_of_iSup_opensRange_eq_top` this makes
`CategoryTheory.Pseudofunctor.toDescentData` of
`AlgebraicGeometry.modulePullbackPseudofunctor` an equivalence for such a family. -/
theorem essSurj_toDescentData_zariski {S : Scheme.{u}} {I : Type v} {Y : I → Scheme.{u}}
    (f : ∀ i, Y i ⟶ S) [∀ i, IsOpenImmersion (f i)] (hf : ⨆ i, (f i).opensRange = ⊤) :
    (modulePullbackPseudofunctor.toDescentData f).EssSurj :=
  essSurj_toDescentData_of_opens (fun _ _ V _ ↦ essSurj_toDescentData_opens V) f hf

/-- **The effectivity half of Stacks 023E.**  Every quasi-coherent descent datum for a family
of open immersions whose images cover the target is effective.  This is
`Stacks.Descent.isEffective_of_essSurj_zariski` with its standing essential-surjectivity
hypothesis discharged by `Stacks.Descent.essSurj_toDescentData_zariski`; the full faithfulness
half is `Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_zariski`. -/
@[stacks 023E "zariski_effectivity"]
theorem isEffective_zariski {S : Scheme.{u}} {I : Type v} {Y : I → Scheme.{u}}
    (f : ∀ i, Y i ⟶ S) [∀ i, IsOpenImmersion (f i)] (hf : ⨆ i, (f i).opensRange = ⊤)
    (D : QuasicoherentDescentData f) : D.IsEffective :=
  have := essSurj_toDescentData_zariski f hf
  isEffective_of_essSurj_zariski f hf D

/-- **The effectivity half of Stacks 023E**, for an open covering of a scheme in the form of an
`AlgebraicGeometry.Scheme.OpenCover`. -/
theorem isEffective_openCover {S : Scheme.{u}} (𝒰 : Scheme.OpenCover.{v} S)
    (D : QuasicoherentDescentData 𝒰.f) : D.IsEffective :=
  isEffective_zariski 𝒰.f 𝒰.iSup_opensRange D

end Stacks.Descent

end

end
