module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.BaseChangeAlgebraSystemCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLimitColimitSheaf
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSitesSystems

/-!
# The descent of Stacks 09YN along a restriction functor, at arbitrary coefficients

`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.descent_along_restriction` is
stated for sheaves of **sets**: in the situation of [Stacks, Tag 0A34], with the functors
`u i : D.C i ⥤ C` exhibiting the small category `C` as the colimit of the levels and `Λ : C ⥤ E`
a continuous functor along which restriction of sheaves is fully faithful, a compatible family of
maps on the levels is the restriction of a unique map of sheaves of sets on `(E, J)`. That is the
half of [Stacks, Tag 0EYN] which says `𝓕 = colim_i f_i^{-1}f_{i, *}𝓕`, in the elementwise form the
machinery proves it.

This file states and proves the same descent for sheaves with values in an **arbitrary** category
`A`, which is what a consumer at abelian coefficients needs.

## Main definitions

* `CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.RestrictionIsColimit'` — that
  descent read as a predicate on the sheaf, which is the form a geometric instantiation applies.
  Its legs are an arbitrary family of functors from the levels to the ambient site and its
  transition datum is an **isomorphism**, so that a geometric instantiation whose legs are chosen
  fibre products can state it; see its docstring on why that is a generalisation of the equality
  form and not a weakening.
* `CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.transportFamily` — the
  conjugation of a family of maps on one family of legs onto an isomorphic family of legs.

## Main results

* `CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.descent_along_restriction'` —
  **the descent at arbitrary coefficients.**
* `CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.restrictionIsColimit'_of_inputs` —
  the same, as the predicate, at the strict legs `u i ⋙ Λ` of [Stacks, Tag 0A34] with
  `CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.compTransitionIso` as the
  transition datum.
* `CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.RestrictionIsColimit'.ofIso` —
  **the predicate transports along an isomorphism of the legs**, the transition datum being
  conjugated. No coherence hypothesis arises, the conjugated datum being defined from the old one
  and the isomorphism.
* `Stacks.EtaleCohomology.AffineLimitCohomology.full_limitRestrictionAb`,
  `faithful_limitRestrictionAb` — restriction of **abelian** sheaves along the two crossings from
  the raised small affine étale site of a limit of schemes to its size-bounded small étale site is
  fully faithful.
* `Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitAb_limitToSmallEtale` —
  **[Stacks, Tag 0EYN], second half, at the geometry, for sheaves of abelian groups**: the
  instantiation of the above for the system of sites of [Stacks, Tag 0EYL], which is
  `Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimit_limitToSmallEtale` with
  sheaves of sets replaced by abelian sheaves.

## Implementation notes

**Why this is not a transport of the set-valued statement.** A colimit of abelian sheaves is not
the colimit of the underlying sheaves of sets, and the universal property asserted here is not the
invertibility of any comparison 2-cell, so neither the mate transport of
`Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isIso_smallEtaleSetsBaseChange` nor any
other "sets force abelian" device applies: those carry `CategoryTheory.IsIso` of a mate across a
change of the four categories of a square, and there is no square here. What makes the statement
true at every coefficient category is that *nothing in it is a colimit*: every functor occurring
is a restriction along a functor of sites, so the content is the single assertion that a
morphism of presheaves on `C` may be assembled from morphisms on the levels. That assertion is
`CategoryTheory.Sites.InverseSystem.Stacks.WeakSites.ColimitPresheafDescent.General.natTrans`,
which the tree already carries at an arbitrary target category, the set-valued development being
its instance at `A := Type w`. This file is the corresponding instance of
`descent_along_restriction`, and it is the sets-to-abelian step for a colimit presentation.

**It is a generalisation, not a variant.** Besides the coefficients, `K`, `hhom_inj` and `hK`
drop out: the set-valued statement passes them on to
`InverseSystemOfFiniteSites.isColimit_pullback_pushforward_of_colimit`, which ignores them (they
are its `_hhom_inj` and `_hK`), their role being in the *other* half of [Stacks, Tag 09YN], the
computation of the sections of the colimit. The coverings of `C` still enter, through the
site `K.toGrothendieck` that `Λ` is continuous for and that the fully faithfulness of restriction
along `Λ` is about; they are simply not used as data.

**The compatibility hypothesis is in morphism form.** With no elements available, `hg` says that
`g i` at `V` is `g j` at `(D.u a).obj V` conjugated by the reindexing isomorphisms, which is what
`General` asks for. At `A := Type w` this is
`CategoryTheory.Sites.InverseSystem.Stacks.WeakSites.ColimitPresheafDescent.hg_hom` of the
elementwise form.

## References

* [Stacks Project, Tag 09YN](https://stacks.math.columbia.edu/tag/09YN)
* [Stacks Project, Tag 0A34](https://stacks.math.columbia.edu/tag/0A34)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 09YL](https://stacks.math.columbia.edu/tag/09YL)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ u₁ v₂ u₂ vA uA

namespace CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites

open CategoryTheory.Sites.InverseSystem

variable {C : Type w} [SmallCategory C] {E : Type u₂} [Category.{v₂} E]
  (K : Precoverage C) (J : GrothendieckTopology E) (Λ : C ⥤ E)
  [Λ.IsContinuous K.toGrothendieck J] (A : Type uA) [Category.{vA} A]

/-- **Reindexing a restricted sheaf along an identification of objects of `C` is reindexing along
the image identification in `E`.** This is
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.map_eqToHom_sheafPushforward` at an
arbitrary coefficient category, where there are no elements and so the statement is an equation of
morphisms. -/
theorem map_eqToHom_sheafPushforward' (F : Sheaf J A) {Z Z' : C} (e : Z = Z') :
    ((Λ.sheafPushforwardContinuous A K.toGrothendieck J).obj F).obj.map
        (eqToHom (congrArg op e)) =
      F.obj.map (eqToHom (congrArg op (congrArg Λ.obj e))) := by
  subst e
  rw [eqToHom_refl, eqToHom_refl, Functor.map_id, Functor.map_id]
  rfl

/-- **Stacks 09YN's descent statement, transported along a restriction functor, at arbitrary
coefficients.** In the situation of [Stacks, Tag 0A34] let the functors `u i : D.C i ⥤ C` exhibit
the small category `C` as the colimit of the levels `D.C i` (`hu`, `hobj`, `hhom`), and let
`Λ : C ⥤ E` be a functor continuous for `K.toGrothendieck` and `J` along which restriction of
sheaves with values in `A` is full and faithful — the case of interest being the inclusion of a
dense subsite composed with a universe raising.

Let `F` and `H` be sheaves on `(E, J)` with values in `A` and let `g i` be a family of maps on
their restrictions to the levels through `u i ⋙ Λ`, compatible with the canonical reindexing
isomorphisms (`hg`). Then the `g i` are the restrictions of a **unique** map of sheaves `F ⟶ H`.

This is `CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.descent_along_restriction`
with the coefficients `Type w` replaced by an arbitrary `A`, and it is the only form in which the
half of [Stacks, Tag 0EYN] saying `𝓕 = colim_i f_i^{-1}f_{i, *}𝓕` is available for sheaves of
abelian groups. See the module docstring on why no transport of the set-valued statement would
do, and on why `hhom_inj` and the description of the coverings of `C` are absent here while the
set-valued statement carries them. -/
theorem descent_along_restriction' (D : InverseSystemOfFiniteSites.{v₁, u₁, w})
    (u : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j)
    (hobj : ∀ X : C, ∃ (i : D.I) (Y : D.C i), (u i).obj Y = X)
    (hhom :
      ∀ (i : D.I) (X Y : D.C i) (f : (u i).obj X ⟶ (u i).obj Y),
        ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj X ⟶ (D.u a).obj Y),
          (u j).map g =
            eqToHom (Functor.congr_obj (hu a) X) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Y).symm)
    [(Λ.sheafPushforwardContinuous A K.toGrothendieck J).Full]
    [(Λ.sheafPushforwardContinuous A K.toGrothendieck J).Faithful]
    (F H : Sheaf J A)
    (g : ∀ i, (u i ⋙ Λ).op ⋙ F.obj ⟶ (u i ⋙ Λ).op ⋙ H.obj)
    (hg : ∀ {i j : D.I} (a : j ⟶ i) (V : D.C i),
      (g i).app (op V) =
        F.obj.map (eqToHom (congrArg op (congrArg Λ.obj
            (Functor.congr_obj (hu a) V).symm))) ≫
          (g j).app (op ((D.u a).obj V)) ≫
            H.obj.map (eqToHom (congrArg op (congrArg Λ.obj
              (Functor.congr_obj (hu a) V))))) :
    ∃! h : F ⟶ H, ∀ (i : D.I) (V : D.C i),
      (g i).app (op V) = h.hom.app (op ((u i ⋙ Λ).obj V)) := by
  have hg' : ∀ {i j : D.I} (a : j ⟶ i) (V : D.C i),
      (g i).app (op V) =
        ((Λ.sheafPushforwardContinuous A K.toGrothendieck J).obj F).obj.map
            (eqToHom (congrArg op (Functor.congr_obj (hu a) V).symm)) ≫
          (g j).app (op ((D.u a).obj V)) ≫
            ((Λ.sheafPushforwardContinuous A K.toGrothendieck J).obj H).obj.map
              (eqToHom (congrArg op (Functor.congr_obj (hu a) V))) := by
    intro i j a V
    rw [map_eqToHom_sheafPushforward' K J Λ A F (Functor.congr_obj (hu a) V).symm,
      map_eqToHom_sheafPushforward' K J Λ A H (Functor.congr_obj (hu a) V)]
    exact hg a V
  let P := ((Λ.sheafPushforwardContinuous A K.toGrothendieck J).obj F).obj
  let Q := ((Λ.sheafPushforwardContinuous A K.toGrothendieck J).obj H).obj
  exact (Λ.sheafPushforwardContinuous A K.toGrothendieck J).existsUnique_of_fullyFaithful
    _ (fun k => ∀ (i : D.I) (V : D.C i),
      (g i).app (op V) = k.hom.app (op ((u i).obj V))) (fun _ => Iff.rfl)
    ⟨⟨Stacks.WeakSites.ColimitPresheafDescent.General.natTrans
      (P := P) (Q := Q) D u hu g hg' hobj hhom⟩,
    fun i V => (Stacks.WeakSites.ColimitPresheafDescent.General.natTrans_app_obj
      (P := P) (Q := Q) D u hu g hg' hobj hhom i V).symm,
    fun y hy => Sheaf.hom_ext (Stacks.WeakSites.ColimitPresheafDescent.General.eq_natTrans
      (P := P) (Q := Q) D u hu g hg' hobj hhom y.hom hy)⟩

/-- **`F = colim_i f_i^{-1}f_{i, *}F` read through a family of functors from the levels to the
ambient site, at arbitrary coefficients, as a predicate.** The conclusion of
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.descent_along_restriction'` with
the second sheaf and the family universally quantified: every family `g` of maps out of the
restrictions of `F` to the levels along the `v i`, compatible with the identifications `hv` of
the two readings of a level, is the restriction of a **unique** map of sheaves out of `F`.

**The transition datum `hv` is an isomorphism, not an equality, and that is a generalisation.**
`descent_along_restriction'` proves the statement where the legs `v i` are `u i ⋙ Λ` for a
*strict* cocone `u` of functors into a small site `C` along whose crossing `Λ : C ⥤ E`
restriction of sheaves is fully faithful, and there the identification is the equality
`D.u a ⋙ u i = u j` of [Stacks, Tag 0A34] composed with `Λ`. That case is
`restrictionIsColimit'_of_inputs`, which supplies `CategoryTheory.eqToIso` of
`comp_transition_eq`; so asking only for an isomorphism adds no hypothesis and drops no
conclusion. What the generality buys is that the predicate transports along isomorphisms of the
legs (`RestrictionIsColimit'.ofIso`) into a vocabulary in which no equality is available: the
legs of a geometric instantiation are often *chosen* fibre products, and a chosen fibre product
agrees with a given one only up to `CategoryTheory.IsPullback.isoPullback`.

It is named rather than written out for the reason recorded on
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.RestrictionIsColimit`: written out
at a *concrete* system — one whose `D` is a projection of a large structure literal — the telescope
mentions `D.I`, `D.C i` and `D.u a` some thirty times and the elaborator goes through that
projection at each occurrence, exhausting the heartbeat budget in the signature before any proof
runs.

Unlike `RestrictionIsColimit` this carries no `ψ`: there the transition maps are quantified over
and then pinned by `hψ` to be the canonical reindexing, so they are determined, and the
coefficient-free statement simply writes the reindexing into the compatibility hypothesis. Nothing
is quantified away. -/
def RestrictionIsColimit' (D : InverseSystemOfFiniteSites.{v₁, u₁, w}) (v : ∀ i, D.C i ⥤ E)
    (hv : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ v i ≅ v j) (F : Sheaf J A) : Prop :=
  ∀ (H : Sheaf J A) (g : ∀ i, (v i).op ⋙ F.obj ⟶ (v i).op ⋙ H.obj),
    (∀ {i j : D.I} (a : j ⟶ i) (V : D.C i),
        (g i).app (op V) =
          F.obj.map ((hv a).hom.app V).op ≫
            (g j).app (op ((D.u a).obj V)) ≫
              H.obj.map ((hv a).inv.app V).op) →
      ∃! h : F ⟶ H, ∀ (i : D.I) (V : D.C i),
        (g i).app (op V) = h.hom.app (op ((v i).obj V))

/-- `descent_along_restriction'` read as the predicate `RestrictionIsColimit'`, with its site
inputs taken as the same bundle
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.ColimitSiteInputs` the set-valued
development uses. This is the form a geometric instantiation applies: the bundle is built in its
own declaration, and nothing here costs the elaborator anything, `D`, `u` and `F` being
variables.

Only `hobj` and `hhom` of the bundle are consumed; the bundle is taken whole so that a geometric
instantiation can reuse the existing one rather than re-derive two of its four fields. -/
theorem restrictionIsColimit'_of_inputs (D : InverseSystemOfFiniteSites.{v₁, u₁, w})
    (u : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ u i = u j)
    (hin : ColimitSiteInputs K D u hu)
    [(Λ.sheafPushforwardContinuous A K.toGrothendieck J).Full]
    [(Λ.sheafPushforwardContinuous A K.toGrothendieck J).Faithful]
    (F : Sheaf J A) :
    RestrictionIsColimit' J A D (fun i => u i ⋙ Λ) (compTransitionIso Λ D u hu) F := by
  intro H g hg
  refine descent_along_restriction' K J Λ A D u hu hin.hobj hin.hhom F H g ?_
  intro i j a V
  rw [hg a V, map_op_compTransitionIso_hom_app, map_op_compTransitionIso_inv_app]

/-! ### Transporting the predicate along isomorphisms of the legs

The point of stating `RestrictionIsColimit'` with an isomorphism rather than an equality: the
predicate may be carried from one family of legs to any family isomorphic to it, the transition
datum being conjugated by the isomorphism. The legs that a geometric instantiation of
[Stacks, Tag 09YQ] wants are base changes along the projections of a limit cone, i.e. *chosen*
fibre products, and the system of sites of [Stacks, Tag 0EYL] only identifies them with its own
levels up to `CategoryTheory.IsPullback.isoPullback`. -/

section Transport

variable {D : InverseSystemOfFiniteSites.{v₁, u₁, w}}

/-- **A family of maps on one family of legs, conjugated onto an isomorphic family of legs.**
Both ends of a map of restricted sheaves move, so the conjugation is by the inverse on the source
and by the isomorphism itself on the target. -/
def transportFamily {v v' : ∀ i, D.C i ⥤ E} (ε : ∀ i, v i ≅ v' i)
    {F H : Sheaf J A} (g : ∀ i, (v' i).op ⋙ F.obj ⟶ (v' i).op ⋙ H.obj) (i : D.I) :
    (v i).op ⋙ F.obj ⟶ (v i).op ⋙ H.obj :=
  Functor.whiskerRight (NatTrans.op (ε i).inv) F.obj ≫ g i ≫
    Functor.whiskerRight (NatTrans.op (ε i).hom) H.obj

/-- The conjugated family, read at an object of a level. -/
theorem transportFamily_app {v v' : ∀ i, D.C i ⥤ E} (ε : ∀ i, v i ≅ v' i)
    {F H : Sheaf J A} (g : ∀ i, (v' i).op ⋙ F.obj ⟶ (v' i).op ⋙ H.obj) (i : D.I)
    (V : D.C i) :
    (transportFamily J A ε g i).app (op V) =
      F.obj.map ((ε i).inv.app V).op ≫ (g i).app (op V) ≫
        H.obj.map ((ε i).hom.app V).op :=
  rfl

/-- **A map of sheaves restricts to the conjugated family exactly when it restricts to the
original one.** This is the naturality of the map together with the invertibility of `ε`, and it
is what makes the two universal properties the same assertion about the same map. -/
theorem transportFamily_app_iff {v v' : ∀ i, D.C i ⥤ E} (ε : ∀ i, v i ≅ v' i)
    {F H : Sheaf J A} (g : ∀ i, (v' i).op ⋙ F.obj ⟶ (v' i).op ⋙ H.obj) (k : F ⟶ H)
    (i : D.I) (V : D.C i) :
    (transportFamily J A ε g i).app (op V) = k.hom.app (op ((v i).obj V)) ↔
      (g i).app (op V) = k.hom.app (op ((v' i).obj V)) := by
  have hk : k.hom.app (op ((v i).obj V)) = F.obj.map ((ε i).inv.app V).op ≫
      k.hom.app (op ((v' i).obj V)) ≫ H.obj.map ((ε i).hom.app V).op := by
    rw [k.hom.naturality_assoc]
    simp [← Functor.map_comp, ← op_comp]
  rw [transportFamily_app, hk, cancel_epi, cancel_mono]

/-- **The conjugated family is compatible with the conjugated transition datum.** The
cancellations are the two `ε ≫ ε⁻¹` of the conjugation at the level `i`; what is left on either
side is the same composite through the level `j`. -/
theorem transportFamily_compat {v v' : ∀ i, D.C i ⥤ E} (ε : ∀ i, v i ≅ v' i)
    (hv : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ v i ≅ v j)
    {F H : Sheaf J A} (g : ∀ i, (v' i).op ⋙ F.obj ⟶ (v' i).op ⋙ H.obj)
    (hg : ∀ {i j : D.I} (a : j ⟶ i) (V : D.C i),
      (g i).app (op V) =
        F.obj.map ((Functor.isoWhiskerLeft (D.u a) (ε j).symm ≪≫ hv a ≪≫ ε i).hom.app V).op ≫
          (g j).app (op ((D.u a).obj V)) ≫
            H.obj.map ((Functor.isoWhiskerLeft (D.u a) (ε j).symm ≪≫ hv a ≪≫ ε i).inv.app V).op)
    {i j : D.I} (a : j ⟶ i) (V : D.C i) :
    (transportFamily J A ε g i).app (op V) =
      F.obj.map ((hv a).hom.app V).op ≫
        (transportFamily J A ε g j).app (op ((D.u a).obj V)) ≫
          H.obj.map ((hv a).inv.app V).op := by
  rw [transportFamily_app, transportFamily_app, hg a V]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, op_comp, Functor.map_comp, Category.assoc]
  simp only [Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc, ← op_comp,
    Iso.hom_inv_id_app, op_id, Functor.map_id, Category.comp_id]

/-- **The predicate transports along an isomorphism of the legs**, the transition datum being
conjugated: if `F` is the colimit of its restrictions along the legs `v` with the transitions
`hv`, then it is the colimit of its restrictions along any isomorphic family `v'` with the
transitions `hv` conjugated by the isomorphism.

Nothing is assumed beyond the isomorphisms: the conjugated transition datum is *defined* from
`hv` and `ε`, so there is no coherence hypothesis to discharge. The two universal properties are
the same assertion about the same map, by `transportFamily_app_iff`. -/
theorem RestrictionIsColimit'.ofIso {v v' : ∀ i, D.C i ⥤ E}
    (hv : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ v i ≅ v j)
    (ε : ∀ i, v i ≅ v' i) {F : Sheaf J A} (h : RestrictionIsColimit' J A D v hv F) :
    RestrictionIsColimit' J A D v'
      (fun {i j} a => Functor.isoWhiskerLeft (D.u a) (ε i).symm ≪≫ hv a ≪≫ ε j) F :=
  fun H g hg => (existsUnique_congr fun k => forall_congr' fun i => forall_congr' fun V =>
      transportFamily_app_iff J A ε g k i V).mp
    (h H (transportFamily J A ε g) (transportFamily_compat J A ε hv g hg))

end Transport

end CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites

/-! ### The small étale site of a limit of schemes, at abelian coefficients

The two crossings of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleLimitColimitSheaf.lean`, carried
out at the coefficients `AddCommGrpCat.{max u v + 1}` instead of at sheaves of sets. The
`CategoryTheory.AsSmall` half is coefficient-free already; the half of [Stacks, Tag 04HR] is
`Stacks.EtaleCohomology.BaseChangeAlgebraSystem.restrictToAffineEtale_isEquivalence`, the
abelian counterpart of `AlgebraicGeometry.SmallAffineEtale.sheafEquiv`, which the tree carries only
for sheaves of sets in `Type (u + 1)`. -/

namespace Stacks.EtaleCohomology.AffineLimitCohomology

open AlgebraicGeometry CategoryTheory.Sites.InverseSystem

universe v u

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-- Restriction of **abelian** sheaves along the composite crossing is full: it is the composite of
the [Stacks, Tag 04HR] equivalence on abelian sheaves
(`Stacks.EtaleCohomology.BaseChangeAlgebraSystem.restrictToAffineEtale`) with the
`CategoryTheory.AsSmall` raising, each of which is full. This is
`Stacks.EtaleCohomology.AffineLimitCohomology.full_limitRestriction` at abelian coefficients. -/
instance full_limitRestrictionAb :
    ((limitToSmallEtale D c B hX).sheafPushforwardContinuous AddCommGrpCat.{max u v + 1}
      (limitSitePrecoverage D c B hX).toGrothendieck
      (AlgebraicGeometry.SmallEtale.topology B c.pt hX)).Full :=
  haveI := Stacks.EtaleCohomology.BaseChangeAlgebraSystem.restrictToAffineEtale_isEquivalence
    B c.pt hX
  inferInstanceAs
    ((Stacks.EtaleCohomology.BaseChangeAlgebraSystem.restrictToAffineEtale B c.pt hX ⋙
      AsSmall.sheafRaise (AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX)
        AddCommGrpCat.{max u v + 1}).Full)

/-- Restriction of **abelian** sheaves along the composite crossing is faithful, for the same
reason as `Stacks.EtaleCohomology.AffineLimitCohomology.full_limitRestrictionAb`. -/
instance faithful_limitRestrictionAb :
    ((limitToSmallEtale D c B hX).sheafPushforwardContinuous AddCommGrpCat.{max u v + 1}
      (limitSitePrecoverage D c B hX).toGrothendieck
      (AlgebraicGeometry.SmallEtale.topology B c.pt hX)).Faithful :=
  haveI := Stacks.EtaleCohomology.BaseChangeAlgebraSystem.restrictToAffineEtale_isEquivalence
    B c.pt hX
  inferInstanceAs
    ((Stacks.EtaleCohomology.BaseChangeAlgebraSystem.restrictToAffineEtale B c.pt hX ⋙
      AsSmall.sheafRaise (AlgebraicGeometry.SmallAffineEtale.precoverage B c.pt hX)
        AddCommGrpCat.{max u v + 1}).Faithful)

/-- **[Stacks, Tag 0EYN], second half, on the small étale site of a limit of schemes, for sheaves
of ABELIAN GROUPS.** Let `(X_i)` be an inverse system of schemes with affine transition morphisms
over a nonempty directed index, all of them objects of a big étale site `B`, let `X = lim X_i`,
and let `F` be an abelian sheaf on the size-bounded small étale site of `X`. Then

`F = colim_i p_i^{-1} p_{i, *} F`,

in the form the inverse-system machinery proves it: every family of maps out of the restrictions
of `F` to the levels of the system of sites of [Stacks, Tag 0EYL], compatible with the canonical
reindexings, is the restriction of a **unique** map of sheaves out of `F`.

This is `Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimit_limitToSmallEtale` with
sheaves of sets replaced by sheaves of abelian groups. The replacement is not a transport of the
set-valued statement — see the module docstring — but the same proof at another coefficient
category, through
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.restrictionIsColimit'_of_inputs`;
what has to be supplied afresh is the full faithfulness of restriction along the composite
crossing at these coefficients, which is
`Stacks.EtaleCohomology.AffineLimitCohomology.full_limitRestrictionAb` and
`faithful_limitRestrictionAb`.

The four site inputs are the bundle
`Stacks.EtaleCohomology.AffineLimitCohomology.colimitSiteInputs_toLimitSmall`, reused unchanged:
they are statements about the system of sites and say nothing about coefficients. Bundling them is
what makes the instantiation fit the elaborator's budget, for the reason recorded on
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.ColimitSiteInputs`: feeding them
one by one here is a `whnf` timeout over the telescope, exactly as it is
for the set-valued statement. -/
theorem restrictionIsColimitAb_limitToSmallEtale
    (F : Sheaf (AlgebraicGeometry.SmallEtale.topology B c.pt hX) AddCommGrpCat.{max u v + 1}) :
    InverseSystemOfFiniteSites.RestrictionIsColimit'
      (AlgebraicGeometry.SmallEtale.topology B c.pt hX)
      AddCommGrpCat.{max u v + 1} (sys D c B hD hX hc)
      (fun i => toLimitSmall D c B hD hX hc i ⋙ limitToSmallEtale D c B hX)
      (InverseSystemOfFiniteSites.compTransitionIso (limitToSmallEtale D c B hX)
        (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
        (toLimitSmall_transition D c B hD hX hc)) F :=
  InverseSystemOfFiniteSites.restrictionIsColimit'_of_inputs
    (limitSitePrecoverage D c B hX) (AlgebraicGeometry.SmallEtale.topology B c.pt hX)
    (limitToSmallEtale D c B hX) AddCommGrpCat.{max u v + 1} (sys D c B hD hX hc)
    (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc)
    (colimitSiteInputs_toLimitSmall D c B hD hX hc) F

end Stacks.EtaleCohomology.AffineLimitCohomology

end
