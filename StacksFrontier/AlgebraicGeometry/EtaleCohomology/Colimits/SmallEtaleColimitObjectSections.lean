module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLevelLegPinning
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleObjectBaseChangeAssociativity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleOpensLegQuasiCompact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.QcSeparatedObjectColimit
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.AbelianSectionsOverAnObjectOfColimitOfFiniteSites
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.AbelianObjectSectionsOfColimitOfFiniteSites
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitAffineOpensVanishing

/-!
# Stacks 09YQ in degree zero over an étale object of a stage, at abelian coefficients

`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab` is the
degree-zero step of [Stacks, Tag 09YQ] for sheaves of **abelian** groups over an object which
neither the levels of [Stacks, Tag 0EYL] nor their colimit site need contain. This file
instantiates it at the geometry of Tag 09YQ, which is what the remaining two hypotheses of
`SmallEtaleLimitCohomology.isCohomologyColimit_of_degreeZero_of_affineOpensAcyclic` need:
`hsub`, through the surjectivity `hqc` of
`Stacks.EtaleCohomology.sectionsDifference_of_isCompact_surjective_opensLeg` over a quasi-compact
open of a stage, and `H0`, over the terminal object of the small étale site of a stage.

## Main results

* `Stacks.EtaleCohomology.AffineLimitCohomology.datumIsColimit_of_realization` — the
  one-hypercover step at the levels of [Stacks, Tag 0EYL], for transition data satisfying only
  the cocycle law, with the three level-side inputs as a hypothesis.
* `Stacks.EtaleCohomology.AffineLimitCohomology.objectSectionsLeg` and
  `objectSectionsLeg_pinned` — the restriction map `F_n(V_n) → 𝓕(V_X)` of the datum, and the
  pinning condition `hρ` the one-hypercover step asks of it.
* `Stacks.EtaleCohomology.AffineLimitCohomology.exists_objectSectionsLeg_eq` — **the
  surjectivity**: for a system of abelian sheaves on Mathlib's small étale sites presented on the
  limit and an étale object `V₀` of a stage with monomorphic structure morphism, every section of
  `𝓕` over the base change of `V₀` to the limit is `objectSectionsLeg` of a section of some `F_n`
  over the base change of `V₀` to `X_n`.

## Implementation notes

**Every long hypothesis and the conclusion are named.** The one-hypercover step has
twenty-six arguments, and writing its object-level inputs, its pinning condition and its
conclusion out inside one signature exhausts the elaborator's 200000 heartbeats *in the
signature*, before any proof runs — the rule
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.RestrictionIsColimit` records and
`Stacks.EtaleCohomology.QcSeparatedColimit.SectionsMapPinned` follows for the set-valued
instantiation. A definition of its own gets its own budget. Raising an option is not available in
this
development.

**The sheaf data is abstract in `datumIsColimit_of_pinned` and concrete only in
`datumIsColimit_objectSectionsLeg`.** The colimit presentation of the level data is *not* a
hypothesis of the first: its two consequences
`Stacks.EtaleCohomology.AffineLimitCohomology.exists_levelSection_eq_of_pullbackPresentation` and
`exists_levelCocycleMap_eq_of_pullbackPresentation` are, named by `LevelObjectSurjective` and
`LevelObjectSeparated`. This is for the same budget reason: the predicate
`...AbelianCocycleSystem.IsColimitPresentation` quantifies over every abelian sheaf on the colimit
site, and one occurrence of it in a signature that also mentions the pinning condition does not
elaborate.

**The ambient sites are the size-bounded small étale sites of [Stacks, Tag 021B]**, and the
restriction isomorphisms `e₀` and `en` the one-hypercover step asks for are `Iso.refl`:
`Stacks.EtaleCohomology.AffineEtaleModel.toModel` composed with `CategoryTheory.AsSmall.down` is
`Stacks.EtaleCohomology.AffineLimitCohomology.limitToSmallEtale` composed with
`AlgebraicGeometry.SmallEtale.toEtaleSite` on the nose, and the level crossing
`Stacks.EtaleCohomology.AffineLimitCohomology.levelEtaleSite` is by definition
`Stacks.EtaleCohomology.QcSeparatedColimit.levelToSmallEtale` followed by that same embedding. So
no sheaf has to be transported anywhere.

**The pinning condition is proved from two facts and nothing else**: the pinning lemma
`Stacks.EtaleCohomology.AffineLimitCohomology.levelPullbackLeg_app_apply`, which says what the leg
of a level does to a section restricted along a morphism of Mathlib's site of the stage, and the
square `Stacks.EtaleCohomology.AffineLimitCohomology`
`.toEtaleSite_map_fV_comp_toLimitBaseChangeEtaleObjIso_hom`, which compares the leg `fV k` of the
datum at the limit with the base change of its leg `fVn a k` at the stage. The three steps between
them are stated in an arbitrary category and applied by `exact`, for the reason the implementation
notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleLevelCocyclePresentation.lean`
record: a goal mentioning an object of `AlgebraicGeometry.Scheme.Etale` is not type-correct at the
transparency `rewrite` builds its motive at.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Sites.InverseSystem

universe v u w

namespace Stacks.EtaleCohomology

/-! ### Three identities in an arbitrary category -/

/-- **Moving a transport along an equality of objects to the other side of a square.** If the
image under two functors of the transport along `e` precomposed with `f` is `g`, then `f` is the
transport along `e.symm` followed by `g`.

Stated in arbitrary categories and applied by `exact`, for the reason recorded on
`Stacks.EtaleCohomology.comp_eq_of_eq_of_naturality`: a goal mentioning an object of
`AlgebraicGeometry.Scheme.Etale` is not type-correct at the transparency `rewrite` builds its
motive at, so the associativity cannot be done in place. -/
theorem eq_eqToHom_comp_of_map_map_comp_eq {A A' A'' : Type*} [Category* A] [Category* A']
    [Category* A''] (Φ : A ⥤ A') (Ψ : A' ⥤ A'') {X Y : A} (e : X = Y)
    {Z : A''} (f : Ψ.obj (Φ.obj Y) ⟶ Z) (g : Ψ.obj (Φ.obj X) ⟶ Z)
    (h : Ψ.map (Φ.map (eqToHom e)) ≫ f = g) :
    f = eqToHom (congrArg (fun W => Ψ.obj (Φ.obj W)) e).symm ≫ g := by
  subst e
  simpa using h

/-- **Two restrictions against three, on a section, from one commuting square.** For a presheaf of
abelian groups, restricting a section along `q` and then along `p` is restricting it along `m`,
then `s`, then `r`, as soon as `p ≫ q = r ≫ s ≫ m`. -/
theorem presheafMap_op_apply_eq_of_comp_eq {A : Type*} [Category* A]
    (P : Aᵒᵖ ⥤ AddCommGrpCat.{w}) {X Y Z T₁ T₂ : A} (p : X ⟶ Y) (q : Y ⟶ Z) (r : X ⟶ T₁)
    (s : T₁ ⟶ T₂) (m : T₂ ⟶ Z) (h : p ≫ q = r ≫ s ≫ m) (x : ToType (P.obj (op Z))) :
    P.map p.op (P.map q.op x) = P.map r.op (P.map s.op (P.map m.op x)) := by
  simp only [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, h, Category.assoc]

/-- **A transport along an equality of objects of a site, read after restriction along a
functor.** For a presheaf `P` on `A'` and a functor `Ψ : A ⥤ A'`, the transport that the
restriction `Ψ.op ⋙ P` performs along `e` is the transport `P` performs along `Ψ.obj`
of `e`. -/
theorem map_eqToHom_congrArg_op {A A' : Type*} [Category* A] [Category* A'] (Ψ : A ⥤ A')
    (P : A'ᵒᵖ ⥤ AddCommGrpCat.{w}) {X Y : A} (e : X = Y) :
    (Ψ.op ⋙ P).map (eqToHom (congrArg op e)) =
      P.map (eqToHom (congrArg Ψ.obj e).symm).op := by
  subst e
  simp

/-! ### The size-bounded small étale site as an ambient site -/

section Bounded

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An abelian sheaf on Mathlib's small étale site of a scheme of `B`, read on the size-bounded
small étale site of [Stacks, Tag 021B].** Restriction along
`AlgebraicGeometry.SmallEtale.toEtaleSite`, which is a dense subsite inclusion, so nothing is
lost; this is the ambient sheaf `G'` respectively `H_n` of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab` at the
geometry of [Stacks, Tag 09YQ]. -/
def boundedEtaleRestrictAb (G : Sheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}) :
    Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1} :=
  ((SmallEtale.toEtaleSite B S hS).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B S hS) (Scheme.smallEtaleTopology S)).obj G

/-- Reading an abelian sheaf on the size-bounded site does not change its sections: the underlying
presheaf is restriction along the embedding, on the nose. -/
theorem boundedEtaleRestrictAb_obj
    (G : Sheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}) :
    (boundedEtaleRestrictAb B S hS G).obj = (SmallEtale.toEtaleSite B S hS).op ⋙ G.obj :=
  rfl

/-- **An open subscheme of `S` as an object of the size-bounded small étale site.** An open
immersion is étale and the source of an open immersion into a scheme of the big étale site again
belongs to it ([Stacks, Tag 000R] (3)), so no affineness and no quasi-compactness is needed; this
is `Stacks.EtaleCohomology.QcqsLimitCohomology.objOfAffineOpen` with the affineness dropped and
the small *affine* étale site replaced by the small étale site, which is where the object of a
merely quasi-compact open has to live. -/
def opensEtaleObj (V : S.Opens) : SmallEtale B S hS :=
  mkObj B hS (V : Scheme.{u}) V.ι (Scheme.size_lt_of_isOpenImmersion V.ι hS) inferInstance

/-- The image of the object of an open subscheme in Mathlib's small étale site is the object that
open is there. -/
theorem toEtaleSite_opensEtaleObj (V : S.Opens) :
    (SmallEtale.toEtaleSite B S hS).obj (opensEtaleObj B S hS V) = (opensToEtale S).obj V :=
  rfl

/-- The structure morphism of the object of an open subscheme is a monomorphism, being an open
immersion. -/
theorem mono_hom_opensEtaleObj (V : S.Opens) :
    Mono (B.inclusion.map (opensEtaleObj B S hS V).obj.hom) :=
  inferInstanceAs (Mono V.ι)

/-- A quasi-compact open subscheme has quasi-compact object: the instance
`CompactSpace` that `Stacks.EtaleCohomology.QcSeparatedColimit.exists_oneHypercoverOf_datum`
requires of `V₀`. -/
theorem compactSpace_opensEtaleObj (V : S.Opens) (hV : IsCompact (V : Set S)) :
    CompactSpace ((SmallEtale.toScheme B S hS).obj (opensEtaleObj B S hS V)) :=
  isCompact_iff_compactSpace.mp hV

/-- An open subscheme of a quasi-separated scheme is quasi-separated: the instance
`QuasiSeparatedSpace` that `exists_oneHypercoverOf_datum` requires of `V₀`. It is inherited from
the ambient scheme and is not an extra hypothesis on the open. -/
theorem quasiSeparatedSpace_opensEtaleObj [QuasiSeparatedSpace S] (V : S.Opens) :
    QuasiSeparatedSpace ((SmallEtale.toScheme B S hS).obj (opensEtaleObj B S hS V)) :=
  QuasiSeparatedSpace.of_isOpenEmbedding V.ι.isOpenEmbedding

end Bounded

namespace AffineLimitCohomology

open Stacks.EtaleCohomology.QcSeparatedColimit (levelIndex levelToSmallEtale
  toLimitBaseChangeEtaleObj transitionBaseChangeEtaleObj OneHypercoverDatum)
open Stacks.EtaleCohomology.SmallEtaleLimitCohomology (conePi transportLeg)

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt) (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-! ### The inputs and the conclusion of the one-hypercover step, named -/

/-- **The compatibility of the legs with the transitions, on sections, named at the levels of
[Stacks, Tag 0EYL].** This is the hypothesis `hι` of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab`, and it is the
compatibility clause `...AbelianCocycleSystem.IsCompatible` of a colimit presentation read on
sections by `Stacks.WeakSites.ColimitSiteCohomology.cocycleLeg_app_eq_of_isCompatible`. -/
def LevelLegCompatible
    (M : InverseSystemOfFiniteSites.AbelianCocycleSystem.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc))
    (G : Sheaf (AffineEtaleModel.precoverage B c.pt hX).toGrothendieck Ab.{max u v + 1})
    (ι : ∀ n, (M.obj n).obj ⟶ (toLimitSmall D c B hD hX hc n).op ⋙ G.obj) : Prop :=
  ∀ {n m : (sys D c B hD hX hc).I} (a : m ⟶ n) (Y : (sys D c B hD hX hc).C n)
    (x : ToType ((M.obj n).obj.obj (op Y))),
    (ι n).app (op Y) x =
      G.obj.map (eqToHom (congrArg op (Functor.congr_obj
          (toLimitSmall_transition D c B hD hX hc a) Y)))
        ((ι m).app (op (((sys D c B hD hX hc).u a).obj Y)) ((M.map a).app (op Y) x))

/-- **The object-level surjectivity input of the degree-zero step, named at the levels of
[Stacks, Tag 0EYL].** Every section of `𝒢` over the image of an object of a level comes from a
section of the data at some level below. This is the hypothesis `hsurjObj` of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab`, and it is
`Stacks.EtaleCohomology.AffineLimitCohomology.exists_levelSection_eq_of_pullbackPresentation` at
the étale system. -/
def LevelObjectSurjective
    (M : InverseSystemOfFiniteSites.AbelianCocycleSystem.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc))
    (G : Sheaf (AffineEtaleModel.precoverage B c.pt hX).toGrothendieck Ab.{max u v + 1})
    (ι : ∀ n, (M.obj n).obj ⟶ (toLimitSmall D c B hD hX hc n).op ⋙ G.obj) : Prop :=
  ∀ (n : (sys D c B hD hX hc).I) (Y : (sys D c B hD hX hc).C n)
    (z : ToType (G.obj.obj (op ((toLimitSmall D c B hD hX hc n).obj Y)))),
    ∃ (m : (sys D c B hD hX hc).I) (a : m ⟶ n)
      (s : ToType ((M.obj m).obj.obj (op (((sys D c B hD hX hc).u a).obj Y)))),
      G.obj.map (eqToHom (congrArg op (Functor.congr_obj
          (toLimitSmall_transition D c B hD hX hc a) Y)))
        ((ι m).app (op (((sys D c B hD hX hc).u a).obj Y)) s) = z

/-- **The object-level separatedness input of the degree-zero step, named at the levels of
[Stacks, Tag 0EYL].** Two sections of the data at a level with the same image in `𝒢` agree at a
further level. This is the hypothesis `hsep` of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab`, and it is
`Stacks.EtaleCohomology.AffineLimitCohomology.exists_levelCocycleMap_eq_of_pullbackPresentation`
at the étale system. -/
def LevelObjectSeparated
    (M : InverseSystemOfFiniteSites.AbelianCocycleSystem.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc))
    (G : Sheaf (AffineEtaleModel.precoverage B c.pt hX).toGrothendieck Ab.{max u v + 1})
    (ι : ∀ n, (M.obj n).obj ⟶ (toLimitSmall D c B hD hX hc n).op ⋙ G.obj) : Prop :=
  ∀ (n : (sys D c B hD hX hc).I) (Y : (sys D c B hD hX hc).C n)
    (m : (sys D c B hD hX hc).I) (a : m ⟶ n)
    (s s' : ToType ((M.obj m).obj.obj (op (((sys D c B hD hX hc).u a).obj Y)))),
    (ι m).app (op (((sys D c B hD hX hc).u a).obj Y)) s =
      (ι m).app (op (((sys D c B hD hX hc).u a).obj Y)) s' →
    ∃ (p : (sys D c B hD hX hc).I) (b : p ⟶ m),
      ((M.map b).app (op (((sys D c B hD hX hc).u a).obj Y)) s) =
        ((M.map b).app (op (((sys D c B hD hX hc).u a).obj Y)) s')

/-- **The pinning condition of the degree-zero step, named at the levels of
[Stacks, Tag 0EYL].** The restriction map `ρ` of the datum, restricted to the objects `W₀ k` of
the covering family, is the leg of the level. This is the hypothesis `hρ` of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab`. -/
def DatumPinned
    (M : InverseSystemOfFiniteSites.AbelianCocycleSystem.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc))
    (G : Sheaf (AffineEtaleModel.precoverage B c.pt hX).toGrothendieck Ab.{max u v + 1})
    (ι : ∀ n, (M.obj n).obj ⟶ (toLimitSmall D c B hD hX hc n).op ⋙ G.obj)
    {i₀ : (sys D c B hD hX hc).I}
    {V₀ : SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _)}
    (G' : Sheaf (SmallEtale.topology B c.pt hX) Ab.{max u v + 1})
    (e₀ : (limitToSmallEtale D c B hX).op ⋙ G'.obj ≅ G.obj)
    (Hs : ∀ n : (sys D c B hD hX hc).I,
      Sheaf (SmallEtale.topology B (D.obj (levelIndex D c B hD hX hc n)) (hD _))
        Ab.{max u v + 1})
    (en : ∀ n, (levelToSmallEtale D c B hD hX hc n).op ⋙ (Hs n).obj ≅ (M.obj n).obj)
    (E : OneHypercoverDatum D c B hD hX hc i₀ V₀)
    (ρ : ∀ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀),
      ToType ((Hs n).obj.obj (op (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a))) →
        ToType (G'.obj.obj (op (toLimitBaseChangeEtaleObj D c B hD hX hc V₀)))) : Prop :=
  ∀ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀)
    (t : ToType ((Hs n).obj.obj
      (op (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a)))) (k : E.κ'),
    e₀.hom.app (op ((toLimitSmall D c B hD hX hc i₀).obj (E.W₀ k)))
        (G'.obj.map (E.fV k).op (ρ n a t)) =
      G.obj.map (eqToHom (congrArg op (Functor.congr_obj
          (toLimitSmall_transition D c B hD hX hc a) (E.W₀ k))))
        ((ι n).app (op (((sys D c B hD hX hc).u a).obj (E.W₀ k)))
          ((en n).hom.app (op (((sys D c B hD hX hc).u a).obj (E.W₀ k)))
            ((Hs n).obj.map (E.fVn n a k).op t)))

/-- **The conclusion of the degree-zero step, named at the levels of [Stacks, Tag 0EYL].** The
sections of `𝒢` over the base change of `V₀` to the limit are the filtered colimit, over the
arrows into `i₀`, of the sections of the data over the base changes of `V₀` to the stages: every
section of `𝒢` there is the image of a section of some level, and two sections of a level with
the same image agree, on the objects of the datum, at a further level. This is the conclusion of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab`. -/
def DatumIsColimit
    (M : InverseSystemOfFiniteSites.AbelianCocycleSystem.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc))
    {i₀ : (sys D c B hD hX hc).I}
    {V₀ : SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _)}
    (G' : Sheaf (SmallEtale.topology B c.pt hX) Ab.{max u v + 1})
    (Hs : ∀ n : (sys D c B hD hX hc).I,
      Sheaf (SmallEtale.topology B (D.obj (levelIndex D c B hD hX hc n)) (hD _))
        Ab.{max u v + 1})
    (en : ∀ n, (levelToSmallEtale D c B hD hX hc n).op ⋙ (Hs n).obj ≅ (M.obj n).obj)
    (E : OneHypercoverDatum D c B hD hX hc i₀ V₀)
    (ρ : ∀ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀),
      ToType ((Hs n).obj.obj (op (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a))) →
        ToType (G'.obj.obj (op (toLimitBaseChangeEtaleObj D c B hD hX hc V₀)))) : Prop :=
  (∀ s : ToType (G'.obj.obj (op (toLimitBaseChangeEtaleObj D c B hD hX hc V₀))),
      ∃ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀)
        (t : ToType ((Hs n).obj.obj
          (op (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a)))), ρ n a t = s) ∧
    ∀ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀)
      (t t' : ToType ((Hs n).obj.obj
        (op (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a)))),
      ρ n a t = ρ n a t' →
      ∃ (m : (sys D c B hD hX hc).I) (b : m ⟶ n), ∀ k : E.κ',
        (M.map b).app (op (((sys D c B hD hX hc).u a).obj (E.W₀ k)))
            ((en n).hom.app (op (((sys D c B hD hX hc).u a).obj (E.W₀ k)))
              ((Hs n).obj.map (E.fVn n a k).op t)) =
          (M.map b).app (op (((sys D c B hD hX hc).u a).obj (E.W₀ k)))
            ((en n).hom.app (op (((sys D c B hD hX hc).u a).obj (E.W₀ k)))
              ((Hs n).obj.map (E.fVn n a k).op t'))

/-- **The three level-side inputs of the degree-zero step, bundled.** The compatibility of the
legs with the transitions on sections, the object-level surjectivity and the object-level
separatedness: the hypotheses `hι`, `hsurjObj` and `hsep` of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab`.

Bundled for the reason the module's implementation notes record: as three binders they do not fit
in one signature with the covering datum and the conclusion. -/
def LevelSectionsColimit
    (M : InverseSystemOfFiniteSites.AbelianCocycleSystem.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc))
    (G : Sheaf (AffineEtaleModel.precoverage B c.pt hX).toGrothendieck Ab.{max u v + 1})
    (ι : ∀ n, (M.obj n).obj ⟶ (toLimitSmall D c B hD hX hc n).op ⋙ G.obj) : Prop :=
  LevelLegCompatible D c B hD hX hc M G ι ∧
    LevelObjectSurjective D c B hD hX hc M G ι ∧
      LevelObjectSeparated D c B hD hX hc M G ι

/-! ### The realization of a covering datum -/

/-- **The ambient sheaves and the restriction map of a covering datum, bundled.** The ambient
sheaf `G'` on the size-bounded small étale site of `X` restricting to `𝒢`, the ambient sheaves
`H_n` on those of the stages restricting to the data, the map `ρ` on sections over the base
changes of `V₀`, and the pinning condition on it: the last six arguments of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab`.

Bundled for the reason the module's implementation notes record: as six binders of one signature,
together with the three level-side inputs and the conclusion, they exhaust the elaborator's
heartbeat budget before any proof runs. A structure declaration gets its own budget, and so does
the construction of a term of it. -/
structure DatumRealization
    (M : InverseSystemOfFiniteSites.AbelianCocycleSystem.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc))
    (G : Sheaf (AffineEtaleModel.precoverage B c.pt hX).toGrothendieck Ab.{max u v + 1})
    (ι : ∀ n, (M.obj n).obj ⟶ (toLimitSmall D c B hD hX hc n).op ⋙ G.obj)
    {i₀ : (sys D c B hD hX hc).I}
    {V₀ : SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _)}
    (E : OneHypercoverDatum D c B hD hX hc i₀ V₀) where
  /-- The ambient abelian sheaf on the size-bounded small étale site of the limit. -/
  G' : Sheaf (SmallEtale.topology B c.pt hX) Ab.{max u v + 1}
  /-- Its restriction to the raised small affine étale site is `𝒢`. -/
  e₀ : (limitToSmallEtale D c B hX).op ⋙ G'.obj ≅ G.obj
  /-- The ambient abelian sheaves on the size-bounded small étale sites of the stages. -/
  Hs : ∀ n : (sys D c B hD hX hc).I,
    Sheaf (SmallEtale.topology B (D.obj (levelIndex D c B hD hX hc n)) (hD _))
      Ab.{max u v + 1}
  /-- Their restrictions to the levels are the data. -/
  en : ∀ n, (levelToSmallEtale D c B hD hX hc n).op ⋙ (Hs n).obj ≅ (M.obj n).obj
  /-- The map on sections from a stage to the limit. -/
  ρ : ∀ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀),
    ToType ((Hs n).obj.obj (op (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a))) →
      ToType (G'.obj.obj (op (toLimitBaseChangeEtaleObj D c B hD hX hc V₀)))
  /-- Restricted to the objects of the datum, `ρ` is the leg of the level. -/
  pinned : DatumPinned D c B hD hX hc M G ι G' e₀ Hs en E ρ

/-- **The conclusion of the degree-zero step at a realized covering datum**, named: the sections
over the base change to the limit are the filtered colimit of the sections over the base changes
to the stages, for the realization's own map on sections. Named for the same budget reason as
`DatumRealization`. -/
def DatumRealizationIsColimit
    (M : InverseSystemOfFiniteSites.AbelianCocycleSystem.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc))
    (G : Sheaf (AffineEtaleModel.precoverage B c.pt hX).toGrothendieck Ab.{max u v + 1})
    (ι : ∀ n, (M.obj n).obj ⟶ (toLimitSmall D c B hD hX hc n).op ⋙ G.obj)
    {i₀ : (sys D c B hD hX hc).I}
    {V₀ : SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _)}
    (E : OneHypercoverDatum D c B hD hX hc i₀ V₀)
    (R : DatumRealization D c B hD hX hc M G ι E) : Prop :=
  DatumIsColimit D c B hD hX hc M R.G' R.Hs R.en E R.ρ

/-! ### The one-hypercover step at the geometry -/

/-- **[Stacks, Tag 09YQ] in degree zero over a quasi-compact quasi-separated étale object of a
stage, at abelian coefficients.** Let `(X_i)` be an inverse system of schemes over a nonempty
directed index with affine transition morphisms, all objects of a big étale site `B`, let `X` be
the vertex of a limit cone, let `M` be transition data of abelian sheaves on the levels of
[Stacks, Tag 0EYL] in the sense [Stacks, Tag 0EZL] imposes — the cocycle law and no identity law
— and let `𝒢` on the raised small affine étale site of `X` with legs `ι` compatible with the
transitions (`LevelLegCompatible`) be such that every section of `𝒢` over the image of a level
object comes from a level (`LevelObjectSurjective`) and two sections of a level with the same
image there agree further down (`LevelObjectSeparated`). Let `V₀` be an object of the small étale
site of a stage `X_{i₀}` with a finite one-hypercover datum `E` realized by `R`. Then the sections
of `𝒢` over the base change of `V₀` to `X` are the filtered colimit of the sections of the `M_n`
over the base changes of `V₀` to the `X_n`.

This is `Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab` at the
geometry of [Stacks, Tag 09YQ]: the cocycle law on sections is
`Stacks.WeakSites.ColimitSiteCohomology.cocycleMap_app_comp`, and the two halves of the covering
hypothesis are the fields `isLimitDatum` and `isLevelDatum` of the datum. No identity law on `M`
is used or available; nothing is assumed about the sheaves beyond the three named level-side
inputs. -/
theorem datumIsColimit_of_realization
    (M : InverseSystemOfFiniteSites.AbelianCocycleSystem.{v, v, max u v + 1, max u v + 1}
      (sys D c B hD hX hc))
    (G : Sheaf (AffineEtaleModel.precoverage B c.pt hX).toGrothendieck Ab.{max u v + 1})
    (ι : ∀ n, (M.obj n).obj ⟶ (toLimitSmall D c B hD hX hc n).op ⋙ G.obj)
    (h : LevelSectionsColimit D c B hD hX hc M G ι)
    {i₀ : (sys D c B hD hX hc).I}
    {V₀ : SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _)}
    (E : OneHypercoverDatum D c B hD hX hc i₀ V₀)
    (R : DatumRealization D c B hD hX hc M G ι E) :
    DatumRealizationIsColimit D c B hD hX hc M G ι E R := by
  have := E.finite_κ
  have := E.finite_ν
  exact Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab
    (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
    (toLimitSmall_transition D c B hD hX hc) M.obj M.map G ι
    (Stacks.WeakSites.ColimitSiteCohomology.cocycleMap_app_comp M) h.1 h.2.1 h.2.2
    i₀ E.W₀ E.P₀ E.q₁ E.q₂ (limitToSmallEtale D c B hX) R.G' R.e₀ E.isLimitDatum
    (levelToSmallEtale D c B hD hX hc) R.Hs R.en (fun {n} a => E.isLevelDatum n a) R.ρ R.pinned


/-! ### The realization at a system of abelian sheaves on Mathlib's small étale sites -/

section Etale

variable (F : Stacks.EtaleCohomology.EtaleSheafSystem D AddCommGrpCat.{max u v + 1})
  (𝓕 : Sheaf (Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1})

/-- **The ambient abelian sheaf at a stage**: the sheaf of the system there, read on the
size-bounded small étale site of [Stacks, Tag 021B]. This is the `H_n` of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab`. -/
def levelAmbientSheaf (n : (sys D c B hD hX hc).I) :
    Sheaf (SmallEtale.topology B (D.obj (levelIndex D c B hD hX hc n)) (hD _))
      AddCommGrpCat.{max u v + 1} :=
  boundedEtaleRestrictAb B (D.obj (levelIndex D c B hD hX hc n)) (hD _)
    (F.obj (levelIndex D c B hD hX hc n))

/-- **The restriction isomorphism `e₀` at the limit is the identity.**
`Stacks.EtaleCohomology.AffineEtaleModel.toModel` composed with `CategoryTheory.AsSmall.down` is
`limitToSmallEtale` composed with `AlgebraicGeometry.SmallEtale.toEtaleSite` on the nose, so the
restriction to the raised small affine étale site of the ambient sheaf at the limit *is* the sheaf
the level presentation is stated against. -/
def limitAmbientIso :
    (limitToSmallEtale D c B hX).op ⋙ (boundedEtaleRestrictAb B c.pt hX 𝓕).obj ≅
      ((AffineEtaleModel.modelRestrict B c.pt hX).obj
        ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕)).obj :=
  Iso.refl _

/-- **The restriction isomorphism `en` at a stage is the identity.** The level crossing
`levelEtaleSite` is by definition `Stacks.EtaleCohomology.QcSeparatedColimit.levelToSmallEtale`
followed by `AlgebraicGeometry.SmallEtale.toEtaleSite`, so the restriction to the level of the
ambient sheaf at the stage *is* the sheaf of
`Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleSystem` there. -/
def levelAmbientIso (n : (sys D c B hD hX hc).I) :
    (levelToSmallEtale D c B hD hX hc n).op ⋙ (levelAmbientSheaf D c B hD hX hc F n).obj ≅
      ((levelCocycleSystem D c B hD hX hc F).obj n).obj :=
  Iso.refl _

variable (ι : ∀ i : Iᵒᵖ,
  (Stacks.EtaleCohomology.smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕)

/-- **The compatibility of the level legs with the transitions, on sections.** This is
`LevelLegCompatible` at the étale system: the compatibility clause of
`Stacks.EtaleCohomology.AffineLimitCohomology.isColimitPresentation_levelCocycleSystem`, read on
sections by `Stacks.WeakSites.ColimitSiteCohomology.cocycleLeg_app_eq_of_isCompatible`. -/
theorem levelPullbackLeg_app_eq_of_pullbackPresentation
    (hpres : Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓕 F ι)
    (hιc : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (Stacks.EtaleCohomology.conePullbackComp c a).inv.app (F.obj j) ≫
        (Stacks.EtaleCohomology.smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫ ι i = ι j)
    {n m : (sys D c B hD hX hc).I} (a : m ⟶ n) (Y : (sys D c B hD hX hc).C n)
    (x : ToType (((levelCocycleSystem D c B hD hX hc F).obj n).obj.obj (op Y))) :
    (levelPullbackLeg D c B hD hX hc F 𝓕 ι n).app (op Y) x =
      ((AffineEtaleModel.modelRestrict B c.pt hX).obj
          ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕)).obj.map
        (eqToHom (congrArg op (Functor.congr_obj
          (toLimitSmall_transition D c B hD hX hc a) Y)))
        ((levelPullbackLeg D c B hD hX hc F 𝓕 ι m).app
            (op (((sys D c B hD hX hc).u a).obj Y))
          (((levelCocycleSystem D c B hD hX hc F).map a).app (op Y) x)) :=
  Stacks.WeakSites.ColimitSiteCohomology.cocycleLeg_app_eq_of_isCompatible
    (levelCocycleSystem D c B hD hX hc F) (toLimitSmall D c B hD hX hc)
    (toLimitSmall_transition D c B hD hX hc) _
    (levelPullbackLeg D c B hD hX hc F 𝓕 ι)
    (isColimitPresentation_levelCocycleSystem D c B hD hX hc F 𝓕 ι hpres hιc).1 a Y x

/-- **The three level-side inputs of the degree-zero step, named at the étale system.**
`LevelSectionsColimit` for the level cocycle data of a system of abelian sheaves on Mathlib's
small étale sites, with a family of legs out of the abstract inverse images. Named for the budget
reason the module's implementation notes record: the level data, the restricted sheaf of the limit
and the level legs are three sizeable terms, and spelling them out both in a hypothesis and in a
conclusion of one signature does not elaborate. -/
def EtaleLevelSectionsColimit
    (ι : ∀ i : Iᵒᵖ,
      (Stacks.EtaleCohomology.smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕) : Prop :=
  LevelSectionsColimit D c B hD hX hc (levelCocycleSystem D c B hD hX hc F)
    ((AffineEtaleModel.modelRestrict B c.pt hX).obj
      ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕))
    (levelPullbackLeg D c B hD hX hc F 𝓕 ι)

/-- **The three level-side inputs of the degree-zero step, at a system presented on the limit.**
`LevelSectionsColimit` for the level cocycle data of a system of abelian sheaves on Mathlib's
small étale sites presented as `colim_i f_i^{-1}F_i`: the compatibility is
`levelPullbackLeg_app_eq_of_pullbackPresentation` and the two object-level inputs are
`exists_levelSection_eq_of_pullbackPresentation` and
`exists_levelCocycleMap_eq_of_pullbackPresentation`. -/
theorem levelSectionsColimit_of_pullbackPresentation
    (hpres : Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓕 F ι)
    (hιc : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (Stacks.EtaleCohomology.conePullbackComp c a).inv.app (F.obj j) ≫
        (Stacks.EtaleCohomology.smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫ ι i = ι j) :
    EtaleLevelSectionsColimit D c B hD hX hc F 𝓕 ι :=
  ⟨fun a Y x => levelPullbackLeg_app_eq_of_pullbackPresentation D c B hD hX hc F 𝓕 ι
      hpres hιc a Y x,
    exists_levelSection_eq_of_pullbackPresentation D c B hD hX hc F 𝓕 ι hpres hιc,
    exists_levelCocycleMap_eq_of_pullbackPresentation D c B hD hX hc F 𝓕 ι hpres hιc⟩


/-! ### The map on sections of a covering datum, and its pinning -/

variable (ιe : ∀ i : Iᵒᵖ,
  (Stacks.EtaleCohomology.etaleAbelianInverseImage.{max u v, max u v + 1}
    (conePi c i)).obj (F.obj i) ⟶ 𝓕)

/-- **The map on sections of a covering datum**, from the sections of `F_n` over the base change
`V_n` of `V₀` to a stage to the sections of `𝓕` over the base change `V_X` to the limit: the
transpose `Stacks.EtaleCohomology.etaleTransposeSection` of the leg `ι_n` over `V_n`, followed by
the identification `toLimitBaseChangeEtaleObjIso` of `V_X` with the base change of `V_n` along the
projection of the cone. This is the `ρ` of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab`. -/
def objectSectionsLeg {i₀ : (sys D c B hD hX hc).I}
    (V₀ : SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _))
    (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀)
    (t : ToType ((levelAmbientSheaf D c B hD hX hc F n).obj.obj
      (op (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a)))) :
    ToType ((boundedEtaleRestrictAb B c.pt hX 𝓕).obj.obj
      (op (toLimitBaseChangeEtaleObj D c B hD hX hc V₀))) :=
  𝓕.obj.map (toLimitBaseChangeEtaleObjIso D c B hD hX hc V₀ a).hom.op
    (Stacks.EtaleCohomology.etaleTransposeSection.{max u v + 1, max u v}
      (conePi c (levelIndex D c B hD hX hc n)) (ιe (levelIndex D c B hD hX hc n))
      ((SmallEtale.toEtaleSite B (D.obj (levelIndex D c B hD hX hc n)) (hD _)).obj
        (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a)) t)

/-- **The pinning condition on `objectSectionsLeg`, with the two restriction isomorphisms
dropped.** They are `Iso.refl`, so this is `DatumPinned` with nothing to transport; the two are
separated because the statement here is what the geometry proves and the other is what the
one-hypercover step consumes.

The proof is the pinning lemma
`Stacks.EtaleCohomology.AffineLimitCohomology.levelPullbackLeg_app_apply` at the leg `fVn n a k`
of the datum read in Mathlib's site, and the square
`toEtaleSite_map_fV_comp_toLimitBaseChangeEtaleObjIso_hom`, which needs the structure morphism of
`V₀` to be a monomorphism. The three steps in between are
`Stacks.EtaleCohomology.eq_eqToHom_comp_of_map_map_comp_eq`,
`Stacks.EtaleCohomology.map_eqToHom_congrArg_op` and
`Stacks.EtaleCohomology.presheafMap_op_apply_eq_of_comp_eq`, each stated in arbitrary categories
and applied by `exact`. -/
theorem objectSectionsLeg_app_eq
    {i₀ : (sys D c B hD hX hc).I}
    {V₀ : SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _)}
    (hV₀ : Mono (B.inclusion.map V₀.obj.hom))
    (E : OneHypercoverDatum D c B hD hX hc i₀ V₀)
    (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀)
    (t : ToType ((levelAmbientSheaf D c B hD hX hc F n).obj.obj
      (op (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a))))
    (k : E.κ') :
    (boundedEtaleRestrictAb B c.pt hX 𝓕).obj.map (E.fV k).op
        (objectSectionsLeg D c B hD hX hc F 𝓕 ιe V₀ n a t) =
      ((AffineEtaleModel.modelRestrict B c.pt hX).obj
          ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕)).obj.map
        (eqToHom (congrArg op (Functor.congr_obj
          (toLimitSmall_transition D c B hD hX hc a) (E.W₀ k))))
        ((levelPullbackLeg D c B hD hX hc F 𝓕 (transportLeg F 𝓕 ιe) n).app
          (op (((sys D c B hD hX hc).u a).obj (E.W₀ k)))
          ((levelAmbientSheaf D c B hD hX hc F n).obj.map (E.fVn n a k).op t)) := by
  have hpin := levelPullbackLeg_app_apply D c B hD hX hc F 𝓕 ιe n
    (((sys D c B hD hX hc).u a).obj (E.W₀ k))
    ((SmallEtale.toEtaleSite B (D.obj (levelIndex D c B hD hX hc n)) (hD _)).map
      (E.fVn n a k)) t
  have hkey := Stacks.EtaleCohomology.eq_eqToHom_comp_of_map_map_comp_eq
    (limitToSmallEtale D c B hX) (SmallEtale.toEtaleSite B c.pt hX)
    (Functor.congr_obj (toLimitSmall_transition D c B hD hX hc a) (E.W₀ k)) _ _
    (toEtaleSite_map_fV_comp_toLimitBaseChangeEtaleObjIso_hom D c B hD hX hc hV₀ E a k)
  have hEq := Stacks.EtaleCohomology.map_eqToHom_congrArg_op
    (limitToSmallEtale D c B hX ⋙ SmallEtale.toEtaleSite B c.pt hX) 𝓕.obj
    (Functor.congr_obj (toLimitSmall_transition D c B hD hX hc a) (E.W₀ k))
  refine Eq.trans ?_ (congrArg
    (((AffineEtaleModel.modelRestrict B c.pt hX).obj
        ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕)).obj.map
      (eqToHom (congrArg op (Functor.congr_obj
        (toLimitSmall_transition D c B hD hX hc a) (E.W₀ k))))) hpin).symm
  refine Eq.trans ?_ (ConcreteCategory.congr_hom hEq _).symm
  exact Stacks.EtaleCohomology.presheafMap_op_apply_eq_of_comp_eq 𝓕.obj _ _ _ _ _ hkey _

/-- **The pinning condition `hρ` of the degree-zero step at the étale system.**
`objectSectionsLeg_app_eq` with the two restriction isomorphisms `limitAmbientIso` and
`levelAmbientIso` written in; both are `Iso.refl`, so nothing is transported. -/
theorem objectSectionsLeg_pinned
    {i₀ : (sys D c B hD hX hc).I}
    {V₀ : SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _)}
    (hV₀ : Mono (B.inclusion.map V₀.obj.hom))
    (E : OneHypercoverDatum D c B hD hX hc i₀ V₀) :
    DatumPinned D c B hD hX hc (levelCocycleSystem D c B hD hX hc F)
      ((AffineEtaleModel.modelRestrict B c.pt hX).obj
        ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕))
      (levelPullbackLeg D c B hD hX hc F 𝓕 (transportLeg F 𝓕 ιe))
      (boundedEtaleRestrictAb B c.pt hX 𝓕) (limitAmbientIso D c B hX 𝓕)
      (levelAmbientSheaf D c B hD hX hc F) (levelAmbientIso D c B hD hX hc F) E
      (objectSectionsLeg D c B hD hX hc F 𝓕 ιe V₀) :=
  fun n a t k => objectSectionsLeg_app_eq D c B hD hX hc F 𝓕 ιe hV₀ E n a t k

/-- **The realization of a covering datum at the étale system.** The ambient sheaves are the
sheaves of the system read on the size-bounded small étale sites, the two restriction
isomorphisms are `Iso.refl`, the map on sections is `objectSectionsLeg` and the pinning is
`objectSectionsLeg_pinned`. -/
def datumRealization
    {i₀ : (sys D c B hD hX hc).I}
    {V₀ : SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _)}
    (hV₀ : Mono (B.inclusion.map V₀.obj.hom))
    (E : OneHypercoverDatum D c B hD hX hc i₀ V₀) :
    DatumRealization D c B hD hX hc (levelCocycleSystem D c B hD hX hc F)
      ((AffineEtaleModel.modelRestrict B c.pt hX).obj
        ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕))
      (levelPullbackLeg D c B hD hX hc F 𝓕 (transportLeg F 𝓕 ιe)) E where
  G' := boundedEtaleRestrictAb B c.pt hX 𝓕
  e₀ := limitAmbientIso D c B hX 𝓕
  Hs := levelAmbientSheaf D c B hD hX hc F
  en := levelAmbientIso D c B hD hX hc F
  ρ := objectSectionsLeg D c B hD hX hc F 𝓕 ιe V₀
  pinned := objectSectionsLeg_pinned D c B hD hX hc F 𝓕 ιe hV₀ E


/-- **[Stacks, Tag 09YQ] in degree zero over an étale object of a stage, at a system of abelian
sheaves on Mathlib's small étale sites: every section over the base change to the limit comes from
a stage.** Let `(X_i)` be an inverse system of schemes over a nonempty directed index with affine
transition morphisms, all objects of a big étale site `B`, let `X` be the vertex of a limit cone,
let `F` be a system of abelian sheaves on Mathlib's small étale sites of the `X_i` in the sense of
[Stacks, Tag 0EZL] and let `ι_i : f_i^{-1}F_i ⟶ 𝓕` be legs whose level cocycle data is presented
on the limit (`EtaleLevelSectionsColimit`, which
`levelSectionsColimit_of_pullbackPresentation` supplies from a colimit presentation). Let `V₀` be
an object of the small étale site of a stage whose structure morphism is a monomorphism, carrying
a finite one-hypercover datum `E`. Then every section of `𝓕` over the base change of `V₀` to `X`
is `objectSectionsLeg` of a section of some `F_n` over the base change of `V₀` to `X_n`.

This is the surjectivity half of `datumIsColimit_of_realization` at the realization
`datumRealization`, whose pinning condition is `objectSectionsLeg_pinned`. -/
theorem exists_objectSectionsLeg_eq
    (h : EtaleLevelSectionsColimit D c B hD hX hc F 𝓕 (transportLeg F 𝓕 ιe))
    {i₀ : (sys D c B hD hX hc).I}
    {V₀ : SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _)}
    (hV₀ : Mono (B.inclusion.map V₀.obj.hom))
    (E : OneHypercoverDatum D c B hD hX hc i₀ V₀)
    (s : ToType ((boundedEtaleRestrictAb B c.pt hX 𝓕).obj.obj
      (op (toLimitBaseChangeEtaleObj D c B hD hX hc V₀)))) :
    ∃ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀)
      (t : ToType ((levelAmbientSheaf D c B hD hX hc F n).obj.obj
        (op (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a)))),
      objectSectionsLeg D c B hD hX hc F 𝓕 ιe V₀ n a t = s :=
  (datumIsColimit_of_realization D c B hD hX hc (levelCocycleSystem D c B hD hX hc F)
    ((AffineEtaleModel.modelRestrict B c.pt hX).obj
      ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕))
    (levelPullbackLeg D c B hD hX hc F 𝓕 (transportLeg F 𝓕 ιe)) h E
    (datumRealization D c B hD hX hc F 𝓕 ιe hV₀ E)).1 s

end Etale


end AffineLimitCohomology


end Stacks.EtaleCohomology

end
