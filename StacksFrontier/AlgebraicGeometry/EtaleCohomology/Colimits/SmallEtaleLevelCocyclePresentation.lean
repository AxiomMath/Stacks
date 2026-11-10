module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLevelCocycleSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.QcqsColimitAffineOpensAcyclic

/-!
# The colimit presentation of the level cocycle data of Stacks 09YQ

`Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleSystem` is **(i)** of the passage of
[Stacks, Tag 09YQ] from Mathlib's small étale sites to the levels of [Stacks, Tag 0EYL]: a system
of abelian étale sheaves in the sense of [Stacks, Tag 0EZL], read as
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianCocycleSystem` on those
levels. This file is **(ii)**: a colimit presentation of that data, in the sense of
`...AbelianCocycleSystem.IsColimitPresentation`, out of a colimit presentation of the system on
Mathlib's small étale sites.

With both halves in, the coefficient side of the crossing owes nothing further:
`...AbelianCocycleSystem.isColimitPresentation_split` carries a presentation of cocycle data to a
presentation for a genuine `...AbelianSheafSystem`, splitting the identity arrows' idempotents, so
the identity law — which an `Stacks.EtaleCohomology.EtaleSheafSystem` does not satisfy and cannot
be made to satisfy — is not part of the debt.

## Main definitions

* `Stacks.EtaleCohomology.systemDirShift` — **the shift of a map of direct images along an arrow of
  the index**, the right-hand side of the compatibility condition
  `Stacks.EtaleCohomology.compatible_iff_systemDirTransition` names.
* `Stacks.EtaleCohomology.systemDirLeg` — the transpose of a family of legs out of the inverse
  images.
* `Stacks.EtaleCohomology.AffineEtaleModel.crossPreimage` and `crossPreimageIso` — an abelian
  sheaf on the raised small affine étale site of a scheme, read back on Mathlib's small étale site
  of that scheme through the two restrictions, both of which are equivalences.
* `Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleLeg` — **the legs of the level
  presentation**: the transposed legs of the system, restricted along the level crossing and
  transported along `Stacks.EtaleCohomology.AffineLimitCohomology.levelCrossingIso`.

## Main results

* `Stacks.EtaleCohomology.systemDirShift_comp` — **the cocycle law of the shift**, which is what
  makes the compatibility of a family transitive and hence what the reindexing of the levels by
  `Iᵒᵖ` runs on.
* `Stacks.EtaleCohomology.AffineLimitCohomology.levelCrossingIso_comp_map_levelTransitionIso` —
  **the geometric identity the compatibility of the legs rests on**, the
  `levelBaseChangeCrossing_transition_hom_app` with its conjugation undone.
* `Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleLeg_compat_iff` — **the compatibility
  of the legs is the compatibility of the family of direct images**, in both directions.
* `Stacks.EtaleCohomology.AffineLimitCohomology.isColimitPresentation_levelCocycleSystem` —
  **(ii) of the site crossing.**

## Implementation notes

**Why the reindexing cannot be an equality.** The levels of [Stacks, Tag 0EYL] are indexed by
`(affineEtaleSiteColimit …).system.I`, which *is* `Iᵒᵖ`, and
`(affineEtaleSiteColimit …).indexEquiv` *is* `CategoryTheory.Equivalence.refl`; but
`affineEtaleSiteColimit` carries `@[no_expose]` and its body cannot be exposed — the levels are
*chosen* fibre products and
`CategoryTheory.Limits.pullback` reduces only through Mathlib's `@[no_expose]`
`CategoryTheory.Limits.getLimitCone` — so the two indexings are related by the equivalence and by
nothing cheaper. The cost is one shift along the counit at each index, and it is paid by
`systemDirShift_comp` together with the thinness of `Iᵒᵖ`: the index is a preorder, so its hom-sets
are subsingletons and every coherence of the reindexing is a `Subsingleton.elim`.

**Where the identity law would be needed, and what replaces it.** The shift along an identity arrow
is *not* the identity: it carries the system's transition at `𝟙 i`, which
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimitPresentation_zeroTransitionSystem`
exhibits as zero on a nonzero sheaf while the presentation hypothesis holds. What the reindexing
uses instead is the *compatibility* of the family at an identity arrow of a level, which is an
instance of the hypothesis and not a new assumption; this is the same observation that
`Stacks.WeakSites.ColimitSiteCohomology.idem_comp_of_isCompatible` records on the other side of the
crossing.

**Why the associativity juggling is done in an arbitrary category.** As in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleLevelCocycleSystem.lean`,
a goal mentioning an object of `AlgebraicGeometry.Scheme.Etale` is not type-correct at the
transparency `rewrite` builds its motive at. Every composite rearrangement below is therefore stated
as a lemma in an arbitrary category — `comp_eq_of_conjugate`,
`assoc_cancel_of_naturality_of_transport`, `comp_assoc_substitute`, `whiskerRight_natTransOp_cancel`
— and applied by `exact`. No compiler option is relaxed.

**Where the crossing of the target is produced, and why there.** Both restrictions it is made of —
`Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict` and
`Stacks.EtaleCohomology.AffineEtaleModel.modelRestrict` — are equivalences of sheaf categories,
found by instance search at the coefficients `AddCommGrpCat.{max u v + 1}` through
`CategoryTheory.Functor.IsDenseSubsite.instIsEquivalenceSheafSheafPushforwardContinuous`, so a
preimage exists; `crossPreimage`, `crossPreimageIso` and `exists_crossPreimage` produce it, and it
is obtained at the top of `existsUnique_desc_levelCocycleLeg` rather than in
`isColimitPresentation_levelCocycleSystem`. Three points, each of which costs the full
heartbeat budget if ignored:

* the preimage must be taken one restriction at a time, not through the composite functor: a
  preimage under a `CategoryTheory.Functor.comp` makes the elaborator reduce a chosen sheaf through
  `Classical.choice`;
* the coefficients of `crossPreimage` and `exists_crossPreimage` must be spelled `Ab`, which is how
  `...AbelianCocycleSystem.IsColimitPresentation` spells them, and not `AddCommGrpCat`, which is
  how `modelRestrict` spells them — the two are definitionally equal and the unification is not
  free here;
* and the sheaf must be obtained inside `existsUnique_desc_levelCocycleLeg`, against that
  declaration's own binder, rather than against the sheaf `intro` produces from the presentation
  predicate: the latter carries the structure's raw universe expression
  `max v v (max u v + 1) (max u v + 1)` rather than `max u v + 1`.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry CategoryTheory.Sites.InverseSystem

universe u₂ t₁ w₁ u₁ v₁ w' w v u

namespace Stacks.EtaleCohomology

/-! ### The associativity lemmas, in an arbitrary category -/

/-- **Cancelling a conjugation.** If `p` and `q` are mutually inverse on one side and `r`, `s`
on the other, an identity `q ≫ x ≫ y = f ≫ r` between the conjugated arrows is the identity
`p ≫ f = x ≫ y ≫ s` between the unconjugated ones. Stated in an arbitrary category and applied
by `exact`, as `Stacks.EtaleCohomology.assoc_cancel_of_naturality` is: a goal mentioning an object
of `AlgebraicGeometry.Scheme.Etale` is not type-correct at the transparency `rewrite` builds its
motive at, so the associativity juggling has to happen away from those objects. -/
theorem comp_eq_of_conjugate {𝒜 : Type w} [Category.{w'} 𝒜] {A₀ A₁ A₂ A₃ A₄ : 𝒜}
    {p : A₀ ⟶ A₁} {q : A₁ ⟶ A₀} {f : A₁ ⟶ A₂} {r : A₂ ⟶ A₃} {s : A₃ ⟶ A₂}
    {x : A₀ ⟶ A₄} {y : A₄ ⟶ A₃}
    (hpq : p ≫ q = 𝟙 A₀) (hrs : r ≫ s = 𝟙 A₂) (key : q ≫ x ≫ y = f ≫ r) :
    p ≫ f = x ≫ y ≫ s := by
  rw [← Category.comp_id f, ← hrs, ← reassoc_of% key, reassoc_of% hpq]

/-- **A transport along an identification of objects cancels the restriction it induces.** The
transport `CategoryTheory.eqToHom` of an equality `U = V` of objects, read on sections of a
presheaf `P` and then composed with the transport of the resulting equality of sections in the
other direction, is the identity. Both factors are `eqToHom`s, so the content is that their
endpoints match. -/
theorem map_op_eqToHom_comp_transport {𝒞 : Type*} [Category* 𝒞] {A : Type*} [Category* A]
    (P : 𝒞ᵒᵖ ⥤ A) {U V : 𝒞} (h : U = V) (h' : P.obj (op U) = P.obj (op V)) :
    P.map (eqToHom h).op ≫ eqToHom h' = 𝟙 (P.obj (op V)) := by
  subst h
  simp

/-- **The algebra of the compatibility of the level legs.** The shape in which the compatibility
clause of the level presentation is assembled: the naturality `hnat` of the leg at the later level
moves it past the transition, the geometric identity `hgeo` replaces the two level crossings by the
base-change comparison and a transport, and `hid` cancels that transport against the restriction it
induces. Stated in an arbitrary category and applied by `exact`, for the reason recorded on
`Stacks.EtaleCohomology.comp_eq_of_conjugate`. -/
theorem assoc_cancel_of_naturality_of_transport {𝒜 : Type w} [Category.{w'} 𝒜]
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : 𝒜}
    {d : A₀ ⟶ A₁} {m : A₁ ⟶ A₂} {s'' : A₂ ⟶ A₃} {x : A₃ ⟶ A₄} {E : A₄ ⟶ A₅}
    {s' : A₁ ⟶ A₆} {w : A₆ ⟶ A₃} {z : A₆ ⟶ A₇} {y : A₇ ⟶ A₅} {e : A₅ ⟶ A₄}
    (hnat : m ≫ s'' = s' ≫ w) (hgeo : w ≫ x = z ≫ y ≫ e) (hid : e ≫ E = 𝟙 A₅) :
    d ≫ m ≫ s'' ≫ x ≫ E = d ≫ s' ≫ z ≫ y := by
  rw [reassoc_of% hnat, reassoc_of% hgeo, hid, Category.comp_id]

/-- **Substituting in the middle of a composite.** The shape in which the cocycle law of
`Stacks.EtaleCohomology.systemDirShift` is assembled: `hnat` is the naturality of the comparison of
the iterated direct images in the map being shifted, and `hcoh` is the associativity of that
comparison. Stated in an arbitrary category and applied by `exact`. -/
theorem comp_assoc_substitute {𝒜 : Type w} [Category.{w'} 𝒜] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : 𝒜}
    {f : A₀ ⟶ A₁} {g : A₁ ⟶ A₂} {p : A₂ ⟶ A₃} {q : A₃ ⟶ A₄} {t : A₄ ⟶ A₅}
    {r : A₂ ⟶ A₆} {s : A₆ ⟶ A₄} {u : A₆ ⟶ A₇} {v : A₇ ⟶ A₅}
    (hnat : p ≫ q = r ≫ s) (hcoh : u ≫ v = s ≫ t) :
    f ≫ g ≫ p ≫ q ≫ t = f ≫ g ≫ r ≫ u ≫ v := by
  rw [reassoc_of% hnat, hcoh]

/-- **The two whiskerings of an isomorphism of functors cancel.** For an isomorphism
`α : G₁ ≅ G₂` of functors and a presheaf `P` on the target, restricting a map along `α.inv` and
then along `α.hom` returns it. -/
theorem whiskerRight_natTransOp_cancel {𝒞 : Type*} [Category* 𝒞] {𝒟 : Type*} [Category* 𝒟]
    {A : Type*} [Category* A] {G₁ G₂ : 𝒞 ⥤ 𝒟} (α : G₁ ≅ G₂) (P : 𝒟ᵒᵖ ⥤ A)
    {Q : 𝒞ᵒᵖ ⥤ A} (q : Q ⟶ G₁.op ⋙ P) :
    (q ≫ Functor.whiskerRight (NatTrans.op α.inv) P) ≫
        Functor.whiskerRight (NatTrans.op α.hom) P = q := by
  ext U
  change (q.app U ≫ P.map (α.inv.app U.unop).op) ≫ P.map (α.hom.app U.unop).op = q.app U
  rw [Category.assoc, ← P.map_comp, ← op_comp, Iso.hom_inv_id_app, op_id]
  exact (whisker_eq _ (P.map_id _)).trans (Category.comp_id _)

/-- **Compatibility of a family of maps out of cocycle data survives composition with a map of the
target.** The condition
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianCocycleSystem.IsCompatible`
imposes is stated against a transport along the cocone identity of the colimit site, and that
transport is natural in the presheaf by
`Stacks.WeakSites.ColimitSiteCohomology.eqToHom_comp_whiskerLeft_op_comp`; nothing is assumed of
the data beyond the cocycle law. -/
theorem isCompatible_comp {E : InverseSystemOfFiniteSites.{v₁, u₁, w₁}}
    (M : InverseSystemOfFiniteSites.AbelianCocycleSystem.{v₁, u₁, w₁, t₁} E)
    {C : Type w₁} [SmallCategory C] (uC : ∀ i, E.C i ⥤ C)
    (hu : ∀ {i j : E.I} (a : i ⟶ j), E.u a ⋙ uC i = uC j)
    {H H' : Cᵒᵖ ⥤ Ab.{max u₁ v₁ w₁ t₁}} (φ : H ⟶ H')
    (g : ∀ i, (M.obj i).obj ⟶ (uC i).op ⋙ H)
    (hg : M.IsCompatible uC hu H g) :
    M.IsCompatible uC hu H' (fun i => g i ≫ Functor.whiskerLeft (uC i).op φ) := by
  intro j k a
  refine (hg a =≫ Functor.whiskerLeft (uC j).op φ).trans ?_
  simp only [Category.assoc, Functor.whiskerLeft_comp]
  exact whisker_eq _ (whisker_eq _
    (Stacks.WeakSites.ColimitSiteCohomology.eqToHom_comp_whiskerLeft_op_comp (hu a) φ))

/-! ### The shift of a map of direct images along an arrow of the index -/


variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{u}} (c : Cone D)
  (F : Stacks.EtaleCohomology.EtaleSheafSystem D AddCommGrpCat.{u + 1})
  (H : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})

/-- **The shift of a map of direct images along an arrow of the index.** Given
`ρ : F_k ⟶ f_{k, *}H`, the map `F_l ⟶ f_{l, *}H` obtained by composing the direct-image transition
`Stacks.EtaleCohomology.systemDirTransition` of the system with the direct image of `ρ` and the
comparison `Stacks.EtaleCohomology.coneDirectImageCompAb` of the direct images along the
factorisation of the projections of the cone.

This is the right-hand side of the compatibility condition
`Stacks.EtaleCohomology.compatible_iff_systemDirTransition` names, packaged so that the condition
reads `σ l = systemDirShift a (σ k)`; its cocycle law `systemDirShift_comp` is what lets a family
given on the levels of [Stacks, Tag 0EYL] be reindexed by `Iᵒᵖ`. -/
def systemDirShift {k l : Iᵒᵖ} (α : k ⟶ l)
    (ρ : F.obj k ⟶ (Stacks.EtaleCohomology.smallEtalePushforwardAb (c.π.app k)).obj H) :
    F.obj l ⟶ (Stacks.EtaleCohomology.smallEtalePushforwardAb (c.π.app l)).obj H :=
  Stacks.EtaleCohomology.systemDirTransition D AddCommGrpCat.{u + 1} F α ≫
    (Stacks.EtaleCohomology.systemPushforward D AddCommGrpCat.{u + 1} α).map ρ ≫
      (Stacks.EtaleCohomology.coneDirectImageCompAb c α).hom.app H

/-- **The cocycle law of the shift.** Shifting along a composite is shifting twice. The two
ingredients are the cocycle law `Stacks.EtaleCohomology.systemDirTransition_comp` of the system's
own transition datum and the associativity
`Stacks.EtaleCohomology.smallEtalePushforwardComp'_assoc` of the comparison of direct images, read
at the sheaf; nothing is assumed.

This is what makes the compatibility condition of a family *transitive*, and hence what carries a
family given at the levels of [Stacks, Tag 0EYL] to one indexed by `Iᵒᵖ`. -/
theorem systemDirShift_comp {k l m : Iᵒᵖ} (α : k ⟶ l) (β : l ⟶ m)
    (ρ : F.obj k ⟶ (Stacks.EtaleCohomology.smallEtalePushforwardAb (c.π.app k)).obj H) :
    systemDirShift c F H (α ≫ β) ρ = systemDirShift c F H β (systemDirShift c F H α ρ) := by
  have hcoh := congrArg (fun z => NatTrans.app (Iso.hom z) H)
    (Stacks.EtaleCohomology.smallEtalePushforwardComp'_assoc (c.π.app k) (D.map α) (D.map β)
      (c.π.app l) (c.w α).symm (D.map (α ≫ β)) (D.map_comp α β) (c.π.app m)
      (c.w β).symm (c.w (α ≫ β)).symm AddCommGrpCat.{u + 1})
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at hcoh
  have hnat := (Stacks.EtaleCohomology.systemPushforwardComp D AddCommGrpCat.{u + 1}
    α β).hom.naturality ρ
  simp only [systemDirShift, Stacks.EtaleCohomology.systemDirTransition_comp, Functor.map_comp,
    Category.assoc]
  exact Stacks.EtaleCohomology.comp_assoc_substitute hnat.symm hcoh

/-- **The transpose of a family of legs out of the inverse images.** The map
`F_i ⟶ f_{i, *}H` adjoint to `ι_i : f_i^{-1}F_i ⟶ H` across
`Stacks.EtaleCohomology.smallEtaleAdjunctionAb`. -/
def systemDirLeg (ι : ∀ i : Iᵒᵖ,
      (Stacks.EtaleCohomology.smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ H) (i : Iᵒᵖ) :
    F.obj i ⟶ (Stacks.EtaleCohomology.smallEtalePushforwardAb (c.π.app i)).obj H :=
  (Stacks.EtaleCohomology.smallEtaleAdjunctionAb (c.π.app i)).homEquiv (F.obj i) H (ι i)

/-- **The transpose of a compatible family of legs is compatible with the shift.** This is
`Stacks.EtaleCohomology.compatible_iff_systemDirTransition` read at the transposed family, the
transposition being an equivalence; nothing is assumed. -/
theorem systemDirLeg_compat
    (ι : ∀ i : Iᵒᵖ,
      (Stacks.EtaleCohomology.smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ H)
    (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (Stacks.EtaleCohomology.conePullbackComp c a).inv.app (F.obj j) ≫
        (Stacks.EtaleCohomology.smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫ ι i = ι j)
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    systemDirLeg c F H ι j = systemDirShift c F H a (systemDirLeg c F H ι i) := by
  refine (Stacks.EtaleCohomology.compatible_iff_systemDirTransition c F H
    (systemDirLeg c F H ι) a).mp ?_
  simp only [systemDirLeg, Equiv.symm_apply_apply]
  exact hι a

/-- **The shift is natural in the target.** Shifting a map and then pushing forward a map of the
target is shifting the composite: the naturality of
`Stacks.EtaleCohomology.coneDirectImageCompAb` in the sheaf. This is what carries the factorisation
condition of the universal property from the stage of a level to an arbitrary index. -/
theorem systemDirShift_comp_map (H' : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt)
      AddCommGrpCat.{u + 1}) {k l : Iᵒᵖ} (α : k ⟶ l)
    (ρ : F.obj k ⟶ (Stacks.EtaleCohomology.smallEtalePushforwardAb (c.π.app k)).obj H)
    (χ : H ⟶ H') :
    systemDirShift c F H' α
        (ρ ≫ (Stacks.EtaleCohomology.smallEtalePushforwardAb (c.π.app k)).map χ) =
      systemDirShift c F H α ρ ≫
        (Stacks.EtaleCohomology.smallEtalePushforwardAb (c.π.app l)).map χ := by
  have hnat := (Stacks.EtaleCohomology.coneDirectImageCompAb c α).hom.naturality χ
  simp only [systemDirShift, Functor.map_comp, Category.assoc]
  exact whisker_eq _ (whisker_eq _ hnat)


end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology.AffineEtaleModel

/-! ### Reading an abelian sheaf of the raised small affine étale site on Mathlib's site -/

variable (B : AlgebraicGeometry.BigEtaleSite.{u₂}) (S : AlgebraicGeometry.Scheme.{u₂})
  (hS : B.Contains S)

/-- **An abelian sheaf on the raised small affine étale site of `S`, read on Mathlib's small étale
site of `S`.** The two restrictions
`Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict` and
`Stacks.EtaleCohomology.AffineEtaleModel.modelRestrict` are equivalences of sheaf categories, so a
preimage exists; this is the chosen one, taken one restriction at a time so that no comparison of a
composite of functors with its factors occurs. -/
def crossPreimage (H : Sheaf (precoverage B S hS).toGrothendieck Ab.{u₂ + 1}) :
    Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology S) Ab.{u₂ + 1} :=
  (Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict S).objPreimage
    ((modelRestrict B S hS).objPreimage H)

/-- **The identification of an abelian sheaf on the raised small affine étale site with the
restriction of `Stacks.EtaleCohomology.AffineEtaleModel.crossPreimage`.** -/
def crossPreimageIso (H : Sheaf (precoverage B S hS).toGrothendieck Ab.{u₂ + 1}) :
    (modelRestrict B S hS).obj
      ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict S).obj
        (crossPreimage B S hS H)) ≅ H :=
  (modelRestrict B S hS).mapIso
      ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict S).objObjPreimageIso
        ((modelRestrict B S hS).objPreimage H)) ≪≫
    (modelRestrict B S hS).objObjPreimageIso H

/-- **Every abelian sheaf on the raised small affine étale site of `S` is the restriction of one
on Mathlib's small étale site of `S`.** The essential surjectivity of the two restrictions
`Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict` and
`Stacks.EtaleCohomology.AffineEtaleModel.modelRestrict`. -/
theorem exists_crossPreimage (H : Sheaf (precoverage B S hS).toGrothendieck
    Ab.{u₂ + 1}) :
    ∃ H₀ : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology S) Ab.{u₂ + 1},
      Nonempty ((modelRestrict B S hS).obj
        ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict S).obj H₀) ≅ H) :=
  ⟨crossPreimage B S hS H, ⟨crossPreimageIso B S hS H⟩⟩

end Stacks.EtaleCohomology.AffineEtaleModel

namespace Stacks.EtaleCohomology.AffineLimitCohomology

/-! ### The level crossing against the level transition -/


open Stacks.EtaleCohomology.QcSeparatedColimit (levelIndex levelToSmallEtale transitionScheme)

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), AlgebraicGeometry.IsAffineHom (D.map a)]

/-- **The transition datum of the level-side crossing, unfolded.** The component of
`Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeCrossing_transition` is, by its
definition as a conjugate, the inverse of the level crossing at the earlier level, the transport
along the on-the-nose cocone identity
`Stacks.EtaleCohomology.AffineLimitCohomology.levelCrossing_transition`, and the level crossing at
the later level. -/
theorem levelBaseChangeCrossing_transition_hom_app_conjugate {k j : (sys D c B hD hX hc).I}
    (a : k ⟶ j)
    (Y : (sys D c B hD hX hc).C j) :
    (levelBaseChangeCrossing_transition D c B hD hX hc a).hom.app Y =
      (levelCrossingIso D c B hD hX hc k).inv.app (((sys D c B hD hX hc).u a).obj Y) ≫
        eqToHom (Functor.congr_obj (levelCrossing_transition D c B hD hX hc a) Y) ≫
          (levelCrossingIso D c B hD hX hc j).hom.app Y := by
  change (levelCrossingIso D c B hD hX hc k).inv.app (((sys D c B hD hX hc).u a).obj Y) ≫
      (eqToIso (levelCrossing_transition D c B hD hX hc a)).hom.app Y ≫
        (levelCrossingIso D c B hD hX hc j).hom.app Y = _
  rw [eqToIso.hom, eqToHom_app]

/-- **THE GEOMETRIC IDENTITY the compatibility of the level legs rests on.** For an arrow
`a : k ⟶ j` of the index of the system of [Stacks, Tag 0EYL], the level crossing at `k`, read after
the transition functor and followed by the base change of the level-transition identification
`Stacks.EtaleCohomology.AffineLimitCohomology.levelTransitionIso`, is the transport along the
on-the-nose cocone identity, the level crossing at `j`, and the comparison
`Stacks.EtaleCohomology.smallEtaleBaseChangeComp'` of base change along the later projection with
base change along the earlier one after the transition.

This is
`Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeCrossing_transition_hom_app` with the
conjugation of its left-hand side undone, so that each of the two level crossings appears once and
on its own side. Nothing is assumed, and no new descent argument occurs. -/
theorem levelCrossingIso_comp_map_levelTransitionIso {k j : (sys D c B hD hX hc).I} (a : k ⟶ j)
    (Y : (sys D c B hD hX hc).C j) :
    (levelCrossingIso D c B hD hX hc k).hom.app (((sys D c B hD hX hc).u a).obj Y) ≫
        (Stacks.EtaleCohomology.smallEtaleBaseChange
            (c.π.app (levelIndex D c B hD hX hc k))).map
          ((levelTransitionIso D c B hD hX hc a).hom.app Y) =
      eqToHom (Functor.congr_obj (levelCrossing_transition D c B hD hX hc a) Y) ≫
        (levelCrossingIso D c B hD hX hc j).hom.app Y ≫
          (Stacks.EtaleCohomology.smallEtaleBaseChangeComp'
              (c.π.app (levelIndex D c B hD hX hc k))
              (transitionScheme D c B hD hX hc a)
              (c.π.app (levelIndex D c B hD hX hc j))
              (conePi_transition D c B hD hX hc a)).hom.app
            ((levelEtaleSite D c B hD hX hc j).obj Y) :=
  Stacks.EtaleCohomology.comp_eq_of_conjugate
    ((levelCrossingIso D c B hD hX hc k).hom_inv_id_app _)
    ((Stacks.EtaleCohomology.smallEtaleBaseChangeComp'
        (c.π.app (levelIndex D c B hD hX hc k))
        (transitionScheme D c B hD hX hc a)
        (c.π.app (levelIndex D c B hD hX hc j))
        (conePi_transition D c B hD hX hc a)).inv_hom_id_app _)
    ((levelBaseChangeCrossing_transition_hom_app_conjugate D c B hD hX hc a Y).symm.trans
      (levelBaseChangeCrossing_transition_hom_app D c B hD hX hc a Y))

variable (F : Stacks.EtaleCohomology.EtaleSheafSystem D AddCommGrpCat.{max u v + 1})
  (𝓕 : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1})
  (σ : ∀ n : (sys D c B hD hX hc).I, F.obj (levelIndex D c B hD hX hc n) ⟶
    (Stacks.EtaleCohomology.smallEtalePushforwardAb
      (c.π.app (levelIndex D c B hD hX hc n))).obj 𝓕)

/-- **The legs of the level presentation.** For a family of maps of direct images
`F_n ⟶ p_{n, *}𝓕` indexed by the levels of [Stacks, Tag 0EYL], the map of presheaves on the level
`n` obtained by restricting along the level crossing and transporting along the identification
`Stacks.EtaleCohomology.AffineLimitCohomology.levelCrossingIso` of the level, read on the limit,
with base change along the projection of the cone.

The type is well formed with no transport in it:
`Stacks.EtaleCohomology.AffineEtaleModel.toModel` composed with `CategoryTheory.AsSmall.down` is
`Stacks.EtaleCohomology.AffineLimitCohomology.limitToSmallEtale` composed with
`AlgebraicGeometry.SmallEtale.toEtaleSite` **on the nose**, so the two readings of the limit's site
agree definitionally. -/
def levelCocycleLeg (n : (sys D c B hD hX hc).I) :
    ((levelCocycleSystem D c B hD hX hc F).obj n).obj ⟶
      (toLimitSmall D c B hD hX hc n).op ⋙
        ((AffineEtaleModel.modelRestrict B c.pt hX).obj
          ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕)).obj :=
  Functor.whiskerLeft (levelEtaleSite D c B hD hX hc n).op (σ n).hom ≫
    Functor.whiskerRight (NatTrans.op (levelCrossingIso D c B hD hX hc n).hom) 𝓕.obj

/-- The component of `Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleLeg` at an object
`Y` of the level `n` is the component of `σ n` at the image of `Y` in Mathlib's small étale site,
followed by the restriction of `𝓕` along the level crossing at `Y`. -/
theorem levelCocycleLeg_app (n : (sys D c B hD hX hc).I) (Y : (sys D c B hD hX hc).C n) :
    (levelCocycleLeg D c B hD hX hc F 𝓕 σ n).app (op Y) =
      (σ n).hom.app (op ((levelEtaleSite D c B hD hX hc n).obj Y)) ≫
        𝓕.obj.map ((levelCrossingIso D c B hD hX hc n).hom.app Y).op :=
  rfl

/-- A map of direct images is determined at a level by the leg it builds, read on sections. -/
private theorem eq_of_levelCocycleLeg_eq (n : (sys D c B hD hX hc).I)
    (ρ' : F.obj (levelIndex D c B hD hX hc n) ⟶
      (Stacks.EtaleCohomology.smallEtalePushforwardAb
        (c.π.app (levelIndex D c B hD hX hc n))).obj 𝓕)
    (ψ : ((levelCocycleSystem D c B hD hX hc F).obj n).obj ⟶
      (toLimitSmall D c B hD hX hc n).op ⋙
        ((AffineEtaleModel.modelRestrict B c.pt hX).obj
          ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕)).obj)
    (h : levelCocycleLeg D c B hD hX hc F 𝓕 σ n = ψ)
    (hψ : ∀ Y : (sys D c B hD hX hc).C n, ψ.app (op Y) =
      ρ'.hom.app (op ((levelEtaleSite D c B hD hX hc n).obj Y)) ≫
        𝓕.obj.map ((levelCrossingIso D c B hD hX hc n).hom.app Y).op) :
    σ n = ρ' :=
  hom_ext_of_levelRestrictionAb D c B hD hX hc n _ _ fun Y =>
    (Iso.cancel_iso_hom_right _ _
      (𝓕.obj.mapIso (Iso.op (Iso.app (levelCrossingIso D c B hD hX hc n) Y)))).mp
      (((levelCocycleLeg_app D c B hD hX hc F 𝓕 σ n Y).symm.trans
        (congrArg (fun z => NatTrans.app z (op Y)) h)).trans (hψ Y))

/-- **The compatibility of the level legs, read on sections, is the compatibility of the family of
direct images.** Over an object `Y` of a level, the right-hand side of the compatibility condition
`...AbelianCocycleSystem.IsCompatible` imposes on the legs is the right-hand side of the
direct-image compatibility `Stacks.EtaleCohomology.systemDirShift` names, followed by the transport
along the level crossing at the later level.

Nothing is assumed: the identity is the naturality of the family in the object of the site, the
geometric identity `levelCrossingIso_comp_map_levelTransitionIso`, and the cancellation of the
transport along the cocone identity against the restriction it induces. -/
theorem levelCocycleLeg_compat_app {k j : (sys D c B hD hX hc).I} (a : k ⟶ j)
    (Y : (sys D c B hD hX hc).C j) :
    ((levelCocycleSystem D c B hD hX hc F).map a ≫
        Functor.whiskerLeft ((sys D c B hD hX hc).u a).op
          (levelCocycleLeg D c B hD hX hc F 𝓕 σ k) ≫
          eqToHom (Stacks.WeakSites.ColimitSiteCohomology.restrict_eq (sys D c B hD hX hc)
            (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc) a
            ((AffineEtaleModel.modelRestrict B c.pt hX).obj
              ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj
                𝓕)).obj)).app (op Y) =
      (Stacks.EtaleCohomology.systemDirShift c F 𝓕
            ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map a) (σ k)).hom.app
          (op ((levelEtaleSite D c B hD hX hc j).obj Y)) ≫
        𝓕.obj.map ((levelCrossingIso D c B hD hX hc j).hom.app Y).op := by
  have hnat := (σ k).hom.naturality ((levelTransitionIso D c B hD hX hc a).hom.app Y).op
  have hgeo : 𝓕.obj.map ((Stacks.EtaleCohomology.smallEtaleBaseChange
            (c.π.app (levelIndex D c B hD hX hc k))).map
          ((levelTransitionIso D c B hD hX hc a).hom.app Y)).op ≫
        𝓕.obj.map ((levelCrossingIso D c B hD hX hc k).hom.app
          (((sys D c B hD hX hc).u a).obj Y)).op =
      𝓕.obj.map ((Stacks.EtaleCohomology.smallEtaleBaseChangeComp'
              (c.π.app (levelIndex D c B hD hX hc k))
              (transitionScheme D c B hD hX hc a)
              (c.π.app (levelIndex D c B hD hX hc j))
              (conePi_transition D c B hD hX hc a)).hom.app
            ((levelEtaleSite D c B hD hX hc j).obj Y)).op ≫
        𝓕.obj.map ((levelCrossingIso D c B hD hX hc j).hom.app Y).op ≫
          𝓕.obj.map (eqToHom
            (Functor.congr_obj (levelCrossing_transition D c B hD hX hc a) Y)).op := by
    rw [← 𝓕.obj.map_comp, ← 𝓕.obj.map_comp, ← 𝓕.obj.map_comp, ← op_comp, ← op_comp, ← op_comp,
      levelCrossingIso_comp_map_levelTransitionIso]
    simp only [Category.assoc]
  have hid : 𝓕.obj.map (eqToHom
          (Functor.congr_obj (levelCrossing_transition D c B hD hX hc a) Y)).op ≫
        (eqToHom (Stacks.WeakSites.ColimitSiteCohomology.restrict_eq (sys D c B hD hX hc)
          (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc) a
          ((AffineEtaleModel.modelRestrict B c.pt hX).obj
            ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj
              𝓕)).obj)).app (op Y) = 𝟙 _ := by
    rw [eqToHom_app]
    exact Stacks.EtaleCohomology.map_op_eqToHom_comp_transport 𝓕.obj _ _
  simp only [NatTrans.comp_app, Functor.op_obj, unop_op, levelCocycleSystem_map,
    Stacks.EtaleCohomology.systemDirShift, ObjectProperty.FullSubcategory.comp_hom,
    Stacks.EtaleCohomology.AffineLimitCohomology.systemPushforward_map_hom_app]
  exact Stacks.EtaleCohomology.assoc_cancel_of_naturality_of_transport hnat hgeo hid

/-- **The legs of the level presentation are compatible exactly when the family of direct images
is.** The compatibility condition
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianCocycleSystem.IsCompatible`
imposes at an arrow of the index of [Stacks, Tag 0EYL] holds for the legs built from a family
precisely when that family satisfies the direct-image compatibility of
`Stacks.EtaleCohomology.systemDirShift` at the corresponding arrow of `Iᵒᵖ`.

Both directions are needed and both are the one computation `levelCocycleLeg_compat_app`: the
transport along the level crossing is invertible, which gives one direction, and a map of abelian
sheaves on Mathlib's small étale site of a stage is determined by its values on the objects coming
from the level — `Stacks.EtaleCohomology.AffineLimitCohomology.hom_ext_of_levelRestrictionAb` —
which gives the other. -/
theorem levelCocycleLeg_compat_iff {k j : (sys D c B hD hX hc).I} (a : k ⟶ j) :
    levelCocycleLeg D c B hD hX hc F 𝓕 σ j =
        (levelCocycleSystem D c B hD hX hc F).map a ≫
          Functor.whiskerLeft ((sys D c B hD hX hc).u a).op
            (levelCocycleLeg D c B hD hX hc F 𝓕 σ k) ≫
            eqToHom (Stacks.WeakSites.ColimitSiteCohomology.restrict_eq (sys D c B hD hX hc)
              (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc) a
              ((AffineEtaleModel.modelRestrict B c.pt hX).obj
                ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj
                  𝓕)).obj) ↔
      σ j = Stacks.EtaleCohomology.systemDirShift c F 𝓕
        ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map a) (σ k) := by
  refine ⟨fun h => eq_of_levelCocycleLeg_eq D c B hD hX hc F 𝓕 σ j _ _ h fun Y => ?_,
    fun h => NatTrans.ext (funext fun ⟨Y⟩ => ?_)⟩
  · exact levelCocycleLeg_compat_app D c B hD hX hc F 𝓕 σ a Y
  · rw [levelCocycleLeg_compat_app D c B hD hX hc F 𝓕 σ a Y, ← h]
    rfl

/-- **Composing the legs with a map of the target.** Composing the legs built from a family with
the restriction of a map of abelian sheaves on Mathlib's small étale site of the limit gives the
legs built from the family followed by the direct images of that map. -/
theorem levelCocycleLeg_comp
    (H₀ : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1})
    (χ : 𝓕 ⟶ H₀) (n : (sys D c B hD hX hc).I) :
    levelCocycleLeg D c B hD hX hc F 𝓕 σ n ≫
        Functor.whiskerLeft (toLimitSmall D c B hD hX hc n).op
          ((AffineEtaleModel.modelRestrict B c.pt hX).map
            ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).map χ)).hom =
      levelCocycleLeg D c B hD hX hc F H₀
        (fun m => σ m ≫ (Stacks.EtaleCohomology.smallEtalePushforwardAb
          (c.π.app (levelIndex D c B hD hX hc m))).map χ) n := by
  refine NatTrans.ext (funext fun U => ?_)
  obtain ⟨Y⟩ := U
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, levelCocycleLeg_app,
    ObjectProperty.FullSubcategory.comp_hom]
  exact whisker_eq _ (χ.hom.naturality ((levelCrossingIso D c B hD hX hc n).hom.app Y).op)

/-- **The legs determine the family of direct images they are built from.** The construction of the
legs is injective at each level: restriction along the level crossing is faithful
(`Stacks.EtaleCohomology.AffineLimitCohomology.hom_ext_of_levelRestrictionAb`) and the transport
along `levelCrossingIso` is invertible. -/
theorem levelCocycleLeg_inj
    (H₀ : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1})
    (ρ ρ' : ∀ n : (sys D c B hD hX hc).I, F.obj (levelIndex D c B hD hX hc n) ⟶
      (Stacks.EtaleCohomology.smallEtalePushforwardAb
        (c.π.app (levelIndex D c B hD hX hc n))).obj H₀)
    (n : (sys D c B hD hX hc).I)
    (h : levelCocycleLeg D c B hD hX hc F H₀ ρ n =
      levelCocycleLeg D c B hD hX hc F H₀ ρ' n) :
    ρ n = ρ' n := by
  exact eq_of_levelCocycleLeg_eq D c B hD hX hc F H₀ ρ n _ _ h
    (levelCocycleLeg_app D c B hD hX hc F H₀ ρ' n)

/-- **The fullness half of the level crossing on abelian sheaves.** Every map between the
restrictions to a level of [Stacks, Tag 0EYL] of two abelian sheaves on Mathlib's small étale site
of the level's stage is the restriction of a map of those sheaves. This is the other half of
`Stacks.EtaleCohomology.AffineLimitCohomology.isEquivalence_levelEtaleRestrictionAb` from the
faithfulness `hom_ext_of_levelRestrictionAb` the tree already carries. -/
theorem exists_map_of_levelRestrictionAb (n : (sys D c B hD hX hc).I)
    (G : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology
      (D.obj (levelIndex D c B hD hX hc n))) AddCommGrpCat.{max u v + 1})
    (ψ : (levelEtaleRestrictAb D c B hD hX hc n).obj
        (F.obj (levelIndex D c B hD hX hc n)) ⟶
      (levelEtaleRestrictAb D c B hD hX hc n).obj G) :
    ∃ ρ : F.obj (levelIndex D c B hD hX hc n) ⟶ G,
      Functor.whiskerLeft (levelEtaleSite D c B hD hX hc n).op ρ.hom = ψ.hom :=
  let := isEquivalence_levelEtaleRestrictionAb D c B hD hX hc n
  ⟨(levelEtaleRestrictAb D c B hD hX hc n).preimage ψ,
    congrArg (fun z => z.hom) ((levelEtaleRestrictAb D c B hD hX hc n).map_preimage ψ)⟩

/-- **Every leg on a level comes from a map of direct images.** Given an arbitrary map of
presheaves of the shape a leg of the level presentation has, there is a map of direct images whose
leg it is. Together with `levelCocycleLeg_inj` this says the construction of the legs is a
bijection, which is what lets the universal property be transported from the levels to the
system. -/
theorem exists_levelCocycleLeg_app
    (H₀ : Sheaf (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1})
    (n : (sys D c B hD hX hc).I)
    (q : ((levelCocycleSystem D c B hD hX hc F).obj n).obj ⟶
      (toLimitSmall D c B hD hX hc n).op ⋙
        ((AffineEtaleModel.modelRestrict B c.pt hX).obj
          ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj H₀)).obj) :
    ∃ ρ : F.obj (levelIndex D c B hD hX hc n) ⟶
        (Stacks.EtaleCohomology.smallEtalePushforwardAb
          (c.π.app (levelIndex D c B hD hX hc n))).obj H₀,
      Functor.whiskerLeft (levelEtaleSite D c B hD hX hc n).op ρ.hom ≫
        Functor.whiskerRight (NatTrans.op (levelCrossingIso D c B hD hX hc n).hom) H₀.obj = q := by
  obtain ⟨ρ, hρ⟩ := exists_map_of_levelRestrictionAb D c B hD hX hc F n
    ((Stacks.EtaleCohomology.smallEtalePushforwardAb
      (c.π.app (levelIndex D c B hD hX hc n))).obj H₀)
    ⟨q ≫ Functor.whiskerRight
      (NatTrans.op (levelCrossingIso D c B hD hX hc n).inv) H₀.obj⟩
  exact ⟨ρ, (hρ =≫ _).trans (Stacks.EtaleCohomology.whiskerRight_natTransOp_cancel
    (levelCrossingIso D c B hD hX hc n) H₀.obj q)⟩

/-- **The universal property of the level presentation.** Let `𝓕` be an abelian sheaf on
Mathlib's small étale site of the limit presenting `colim_i f_i^{-1}F_i` in the sense of
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation`, with compatible legs
`ι`. Then every family of maps out of the level cocycle data into an abelian sheaf `H` on the
raised small affine étale site of the limit that is compatible with the transitions factors
uniquely through the legs `Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleLeg`. -/
theorem existsUnique_desc_levelCocycleLeg
    (ι : ∀ i : Iᵒᵖ,
      (Stacks.EtaleCohomology.smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hpres : Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓕 F ι)
    (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (Stacks.EtaleCohomology.conePullbackComp c a).inv.app (F.obj j) ≫
        (Stacks.EtaleCohomology.smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫ ι i = ι j)
    (H : Sheaf (AffineEtaleModel.precoverage B c.pt hX).toGrothendieck
      Ab.{max u v + 1})
    (g : ∀ j, ((levelCocycleSystem D c B hD hX hc F).obj j).obj ⟶
      (toLimitSmall D c B hD hX hc j).op ⋙ H.obj)
    (hg : (levelCocycleSystem D c B hD hX hc F).IsCompatible
      (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc) H.obj g) :
    ∃! h : (AffineEtaleModel.modelRestrict B c.pt hX).obj
        ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕) ⟶ H,
      ∀ j, levelCocycleLeg D c B hD hX hc F 𝓕
          (fun n => Stacks.EtaleCohomology.systemDirLeg c F 𝓕 ι (levelIndex D c B hD hX hc n)) j ≫
        Functor.whiskerLeft (toLimitSmall D c B hD hX hc j).op h.hom = g j := by
  obtain ⟨H₀, hH₀⟩ := AffineEtaleModel.exists_crossPreimage.{max u v} B c.pt hX H
  obtain ⟨e⟩ := hH₀
  have hg₀ : (levelCocycleSystem D c B hD hX hc F).IsCompatible
      (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc)
      ((AffineEtaleModel.modelRestrict B c.pt hX).obj
        ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj H₀)).obj
      (fun n => g n ≫ Functor.whiskerLeft (toLimitSmall D c B hD hX hc n).op e.inv.hom) :=
    Stacks.EtaleCohomology.isCompatible_comp (levelCocycleSystem D c B hD hX hc F)
      (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc) e.inv.hom g hg
  choose σ' hleg₀ using fun n => exists_levelCocycleLeg_app D c B hD hX hc F H₀ n
    (g n ≫ Functor.whiskerLeft (toLimitSmall D c B hD hX hc n).op e.inv.hom)
  have hσ'c : ∀ {k j : (sys D c B hD hX hc).I} (a : k ⟶ j), σ' j =
      Stacks.EtaleCohomology.systemDirShift c F H₀
        ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map a) (σ' k) := by
    intro k j a
    refine (levelCocycleLeg_compat_iff D c B hD hX hc F H₀ σ' a).mp ?_
    rw [show levelCocycleLeg D c B hD hX hc F H₀ σ' j = _ from hleg₀ j,
      show levelCocycleLeg D c B hD hX hc F H₀ σ' k = _ from hleg₀ k]
    exact hg₀ a
  have hτ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      Stacks.EtaleCohomology.systemDirShift c F H₀
          ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.counitIso.app j).hom
          (σ' ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.inverse.obj j)) =
        Stacks.EtaleCohomology.systemDirShift c F H₀ a (Stacks.EtaleCohomology.systemDirShift c F H₀
          ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.counitIso.app i).hom
          (σ' ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.inverse.obj i))) := by
    intro i j a
    rw [hσ'c ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.inverse.map a),
      ← Stacks.EtaleCohomology.systemDirShift_comp, ← Stacks.EtaleCohomology.systemDirShift_comp]
    exact congrArg (Stacks.EtaleCohomology.systemDirShift c F H₀ · _) (Subsingleton.elim _ _)
  have hτlev : ∀ n : (sys D c B hD hX hc).I,
      Stacks.EtaleCohomology.systemDirShift c F H₀
        ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.counitIso.app
          (levelIndex D c B hD hX hc n)).hom
        (σ' ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.inverse.obj
          (levelIndex D c B hD hX hc n))) = σ' n := by
    intro n
    refine (congrArg (Stacks.EtaleCohomology.systemDirShift c F H₀ _)
      (hσ'c ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.unitIso.app n).hom)).trans ?_
    rw [← Stacks.EtaleCohomology.systemDirShift_comp]
    exact (congrArg (Stacks.EtaleCohomology.systemDirShift c F H₀ · (σ' n))
      (Subsingleton.elim _ ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map
        (𝟙 n)))).trans (hσ'c (𝟙 n)).symm
  obtain ⟨χ, hχ, huniq⟩ :=
    Stacks.EtaleCohomology.existsUnique_desc_dir_of_isPullbackColimitPresentation c F 𝓕 ι hpres H₀
      (fun i => Stacks.EtaleCohomology.systemDirShift c F H₀
        ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.counitIso.app i).hom
        (σ' ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.inverse.obj i))) hτ
  have hfun : (fun m : (sys D c B hD hX hc).I =>
      Stacks.EtaleCohomology.systemDirLeg c F 𝓕 ι (levelIndex D c B hD hX hc m) ≫
        (Stacks.EtaleCohomology.smallEtalePushforwardAb
          (c.π.app (levelIndex D c B hD hX hc m))).map χ) = σ' :=
    funext fun m => (hχ (levelIndex D c B hD hX hc m)).trans (hτlev m)
  refine ⟨(AffineEtaleModel.modelRestrict B c.pt hX).map
      ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).map χ) ≫ e.hom,
    fun n => ?_, ?_⟩
  · have hstep : levelCocycleLeg D c B hD hX hc F H₀
          (fun m => Stacks.EtaleCohomology.systemDirLeg c F 𝓕 ι (levelIndex D c B hD hX hc m) ≫
            (Stacks.EtaleCohomology.smallEtalePushforwardAb
              (c.π.app (levelIndex D c B hD hX hc m))).map χ) n =
        g n ≫ Functor.whiskerLeft (toLimitSmall D c B hD hX hc n).op e.inv.hom :=
      (congrArg (fun ρ => levelCocycleLeg D c B hD hX hc F H₀ ρ n) hfun).trans (hleg₀ n)
    rw [ObjectProperty.FullSubcategory.comp_hom, Functor.whiskerLeft_comp, ← Category.assoc,
      levelCocycleLeg_comp, hstep, Category.assoc, ← Functor.whiskerLeft_comp,
      ← ObjectProperty.FullSubcategory.comp_hom, e.inv_hom_id,
      ObjectProperty.FullSubcategory.id_hom]
    exact Category.comp_id _
  · intro y hy
    obtain ⟨χy, hχy⟩ : ∃ χy : 𝓕 ⟶ H₀, (AffineEtaleModel.modelRestrict B c.pt hX).map
        ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).map χy) =
          y ≫ e.inv :=
      ⟨(Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict.{max u v} c.pt ⋙
          AffineEtaleModel.modelRestrict.{max u v} B c.pt hX).preimage (y ≫ e.inv),
        (Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict.{max u v} c.pt ⋙
          AffineEtaleModel.modelRestrict.{max u v} B c.pt hX).map_preimage _⟩
    have hstep : ∀ n : (sys D c B hD hX hc).I, levelCocycleLeg D c B hD hX hc F H₀
        (fun m => Stacks.EtaleCohomology.systemDirLeg c F 𝓕 ι (levelIndex D c B hD hX hc m) ≫
          (Stacks.EtaleCohomology.smallEtalePushforwardAb
            (c.π.app (levelIndex D c B hD hX hc m))).map χy) n =
      g n ≫ Functor.whiskerLeft (toLimitSmall D c B hD hX hc n).op e.inv.hom := by
      intro n
      rw [← levelCocycleLeg_comp, hχy, ObjectProperty.FullSubcategory.comp_hom,
        Functor.whiskerLeft_comp, ← Category.assoc, hy n]
    have hlev : ∀ n : (sys D c B hD hX hc).I,
        Stacks.EtaleCohomology.systemDirLeg c F 𝓕 ι (levelIndex D c B hD hX hc n) ≫
          (Stacks.EtaleCohomology.smallEtalePushforwardAb
            (c.π.app (levelIndex D c B hD hX hc n))).map χy = σ' n :=
      fun n => levelCocycleLeg_inj D c B hD hX hc F H₀ _ σ' n
        ((hstep n).trans (hleg₀ n).symm)
    have hall : ∀ i : Iᵒᵖ, Stacks.EtaleCohomology.systemDirLeg c F 𝓕 ι i ≫
        (Stacks.EtaleCohomology.smallEtalePushforwardAb (c.π.app i)).map χy =
      Stacks.EtaleCohomology.systemDirShift c F H₀
        ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.counitIso.app i).hom
        (σ' ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.inverse.obj i)) := fun i =>
      ((Stacks.EtaleCohomology.systemDirLeg_compat c F 𝓕 ι hι _ =≫ _).trans
          (Stacks.EtaleCohomology.systemDirShift_comp_map c F 𝓕 H₀ _ _ χy).symm).trans
        (congrArg (Stacks.EtaleCohomology.systemDirShift c F H₀ _) (hlev _))
    rw [← huniq χy hall, hχy, Category.assoc, e.inv_hom_id, Category.comp_id]


/-- **The level cocycle data of a presented system is presented.** Let `(X_i)` be an inverse
system of schemes over a nonempty directed index with affine transition morphisms, all objects of
a big étale site `B`, let `X` be the vertex of a limit cone, let `F` be a system of abelian sheaves
on Mathlib's small étale sites of the `X_i` in the sense of [Stacks, Tag 0EZL], and let
`ι_i : f_i^{-1}F_i ⟶ 𝓕` be a compatible family exhibiting `𝓕 = colim_i f_i^{-1}F_i`. Then the
cocycle data `Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleSystem` that `F` becomes on
the levels of [Stacks, Tag 0EYL] is presented, in the sense of
`...AbelianCocycleSystem.IsColimitPresentation`, by the restriction of `𝓕` to the raised small
affine étale site of `X`, with the legs
`Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleLeg` of the transposed family. -/
theorem isColimitPresentation_levelCocycleSystem
    (ι : ∀ i : Iᵒᵖ,
      (Stacks.EtaleCohomology.smallEtalePullbackAb (c.π.app i)).obj (F.obj i) ⟶ 𝓕)
    (hpres : Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓕 F ι)
    (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (Stacks.EtaleCohomology.conePullbackComp c a).inv.app (F.obj j) ≫
        (Stacks.EtaleCohomology.smallEtalePullbackAb (c.π.app i)).map (F.map a) ≫ ι i = ι j) :
    (levelCocycleSystem D c B hD hX hc F).IsColimitPresentation
      (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc)
      (AffineEtaleModel.precoverage B c.pt hX)
      ((AffineEtaleModel.modelRestrict B c.pt hX).obj
        ((Stacks.EtaleCohomology.MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕))
      (levelCocycleLeg D c B hD hX hc F 𝓕
        (fun n => Stacks.EtaleCohomology.systemDirLeg c F 𝓕 ι (levelIndex D c B hD hX hc n))) :=
  ⟨fun a => (levelCocycleLeg_compat_iff D c B hD hX hc F 𝓕 _ a).mpr
    (Stacks.EtaleCohomology.systemDirLeg_compat c F 𝓕 ι hι _),
    fun H g hg => existsUnique_desc_levelCocycleLeg D c B hD hX hc F 𝓕 ι hpres hι H g hg⟩


end Stacks.EtaleCohomology.AffineLimitCohomology

end
