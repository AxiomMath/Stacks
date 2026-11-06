module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleTransitionBaseChangeAssociativity

/-!
# The separatedness clause of Stacks 09YQ in degree zero, and the hypothesis `H0`

`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_zero_iff` splits the
degree-zero statement of [Stacks, Tag 09YQ] into two clauses about **global sections**: every
global section of the colimit sheaf `𝒢` on the limit `X` is the image of a global section of some
`F_i` under `...PresentedSystem.legSection`, and a global section of `F_i` killed by its leg is
killed by a transition `...etaleSectionsTransition` to some further stage. The first clause is
`...AffineLimitCohomology.exists_etaleSectionsRestriction_leg_eq_of_levelSectionsColimit`.

**This file proves the second clause and assembles `H0`** — the degree-zero hypothesis of
`...SmallEtaleLimitCohomology.isCohomologyColimit_of_degreeZero_of_affineOpensAcyclic` — at the
geometry of [Stacks, Tag 09YQ]: a nonempty directed index, affine transition morphisms, all stages
and the limit objects of a big étale site, a limit cone, and every stage quasi-compact and
quasi-separated, which is the tag's own hypothesis on the `X_i`.

## Main results

* `Stacks.EtaleCohomology.AffineLimitCohomology.levelDirTransition_restrict_eq_zero_of_eq_on_datum`
  — **the interchange, and the sheaf condition at the later level**: if the transitions to a level
  `m` of the restrictions of a section to the objects of a covering datum all vanish, then the
  transition of that section to `m` vanishes over the whole base change of `V₀` there.
* `Stacks.EtaleCohomology.AffineLimitCohomology.objectSectionsLeg_top_eq` — the map on sections of
  a covering datum taken at the object of the open `⊤` of a stage **is** the leg on global
  sections.
* `Stacks.EtaleCohomology.AffineLimitCohomology.exists_levelDirTransition_top_eq_zero` and
  `exists_etaleSectionsTransition_eq_zero_of_level` — **the separatedness clause at a level**, in
  the vocabulary of `...levelDirTransition` and then in that of
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.etaleSectionsTransition`.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.legSection_etaleSectionsTransition` and
  `etaleSectionsTransition_comp` — the **two cocone laws** of a presented system, read in degree
  zero on global sections. They are the fields `leg_transition` and `transition_comp` of
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem` conjugated by
  `CategoryTheory.Sheaf.H.equiv₀`, and nothing else; no identity law on the system is used or
  available.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_zero_of_isLimit` —
  **`H0`.**

## How the separatedness clause goes

Let `s` be a global section of `F_i` with `legSection i s = 0`.

**The index.** The levels of [Stacks, Tag 0EYL] are indexed by `(sys …).I`, which
`Stacks.EtaleCohomology.affineEtaleSiteColimit` equips with an *equivalence* to `Iᵒᵖ` and not an
equality, so the argument is run at the level `indexEquiv.inverse.obj i` and `s` must first be
transitioned along the counit `levelIndex (indexEquiv.inverse.obj i) ⟶ i`. That costs the cocone
law `legSection_etaleSectionsTransition` — the transitioned section is again killed by its leg —
and, at the end, the cocycle law `etaleSectionsTransition_comp`, which folds the counit back into
the transition the clause asks for. Both are degree-zero readings of fields `PresentedSystem`
already carries.

**The object.** A quasi-compact quasi-separated stage is not an object of its own raised small
affine étale site unless it is affine, so the degree-zero step
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab` is run over the
étale object `Stacks.EtaleCohomology.opensEtaleObj` of the open `⊤` of the stage, which is
quasi-compact exactly because the stage is. Its base changes to the lower stages and to the limit
are terminal objects of Mathlib's small étale sites there (`transitionBaseChangeTopIso`,
`toLimitBaseChangeTopIso`), and `objectSectionsLeg_top_eq` identifies the step's map on sections
with the leg on global sections; so `legSection i s = 0` is exactly the hypothesis of the step's
separatedness half at `t` and `0`.

**The interchange.** What that half returns is an agreement *after restricting to the objects
`W₀ k` of the datum and then transitioning to a later level `m`*, and the sheaf condition which
turns an agreement into an equality of sections can only consume the other order. The pinning
lemma `Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleMap_app_apply` interchanges them;
`Stacks.EtaleCohomology.AffineLimitCohomology.transitionBaseChangeEtaleObjIso` identifies the
object the transitioned section lives over with the one
`...QcSeparatedColimit.OneHypercoverDatum.isLevelDatum m (b ≫ a)` covers, and
`toEtaleSite_map_fVn_comp_transitionBaseChangeEtaleObjIso_hom` carries the legs of the datum
across that identification. The sheaf condition itself is
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_eq_of_eq_on_oneHypercoverOf` at the underlying
sheaf of sets, which `CategoryTheory.sheafCompose` along `CategoryTheory.forget` supplies with the
same sections, which is legitimate here since nothing in the sheaf condition is a colimit.

**Every geometric square in the argument is free.** All the objects that occur — the object of the
open `⊤`, its base changes, the terminal objects — have monomorphic structure morphism, so
`Stacks.EtaleCohomology.etale_hom_ext_of_mono` identifies any two morphisms into them and no fibre
product is ever computed.

## What is assumed

Beyond the standing hypotheses of [Stacks, Tag 09YQ] the statements here assume exactly
`[∀ i : Iᵒᵖ, CompactSpace (D.obj i)]` and `[∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]`, which is
the tag's own hypothesis that every `X_i` is quasi-compact and quasi-separated. `H0` carries **no
`Mono` hypothesis** — the one obligation of the one-hypercover comparison is discharged inside, an
open immersion being a monomorphism — and no sheafification or `Ext` instance binder: those are
found by instance search at a variable index. `IsAffineHom (c.π.app _)`, which
`...exists_oneHypercoverOf_datum` asks for as an instance, is supplied from `hc` by
`Stacks.EtaleCohomology.QcqsLimitCohomology.isAffineHom_limitProjection`. **No identity law** on
the system of [Stacks, Tag 0EZL] is used or available anywhere in the file.

No `@[stacks]` attribute is placed: what the tag asserts in every degree is the conclusion of the
dévissage `isCohomologyColimit_of_degreeZero_of_affineOpensAcyclic`, whose other three hypotheses
are proved elsewhere, and the registration belongs on the statement that discharges them all.

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

universe w v u

namespace Stacks.EtaleCohomology

/-- **Two restrictions against two, on a section, from one commuting square.** For a presheaf of
abelian groups, restricting a section along `q` and then along `p` is restricting it along `s` and
then along `r`, as soon as `p ≫ q = r ≫ s`.

`Stacks.EtaleCohomology.presheafMap_op_apply_eq_of_comp_eq` is the statement for a *three*-fold
factorisation `p ≫ q = r ≫ s ≫ m`, which is the shape the pinning of the leg produces; the
squares below have two restrictions on each side and instantiating that one at `m = 𝟙` would leave
a transport along the identity to cancel. Stated over a variable category and applied by `exact`,
for the reason recorded on `Stacks.EtaleCohomology.comp_eq_of_eq_of_naturality`. -/
theorem presheafMap_op_apply_eq_of_comp_eq' {A : Type*} [Category* A]
    (P : Aᵒᵖ ⥤ AddCommGrpCat.{w}) {X Y Z T : A} (p : X ⟶ Y) (q : Y ⟶ Z) (r : X ⟶ T) (s : T ⟶ Z)
    (h : p ≫ q = r ≫ s) (x : ToType (P.obj (op Z))) :
    P.map p.op (P.map q.op x) = P.map r.op (P.map s.op x) := by
  simp only [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, h]

/-- A morphism of abelian groups sends a section equal to zero to zero. -/
private theorem hom_apply_eq_zero {M N : AddCommGrpCat.{w}} (f : M ⟶ N) {x : ToType M}
    (h : x = 0) : f x = 0 := by
  simp [h]

namespace AffineLimitCohomology

open Stacks.EtaleCohomology.QcSeparatedColimit (levelIndex transitionScheme
  toLimitBaseChangeEtaleObj transitionBaseChangeEtaleObj OneHypercoverDatum)
open Stacks.EtaleCohomology.SmallEtaleLimitCohomology (conePi transportLeg)

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt) (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-! ### The base changes of the object of the open `⊤` of a stage -/

/-- **The base change to a lower stage of the object of the open `⊤` of a stage is the terminal
object of Mathlib's small étale site there.** `transitionBaseChangeOpensIso` at the open `⊤`,
whose preimage is again `⊤`, followed by `Stacks.EtaleCohomology.opensToEtaleTopIso`. -/
def transitionBaseChangeTopIso {i₀ : (sys D c B hD hX hc).I}
    {n : (sys D c B hD hX hc).I} (a : n ⟶ i₀) :
    (SmallEtale.toEtaleSite B (D.obj (levelIndex D c B hD hX hc n)) (hD _)).obj
        (transitionBaseChangeEtaleObj D c B hD hX hc
          (opensEtaleObj B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _) ⊤) a) ≅
      Scheme.Etale.mk (𝟙 (D.obj (levelIndex D c B hD hX hc n))) :=
  transitionBaseChangeOpensIso D c B hD hX hc ⊤ a ≪≫
    opensToEtaleTopIso (D.obj (levelIndex D c B hD hX hc n))

/-- **The base change to the limit of the object of the open `⊤` of a stage is the terminal object
of Mathlib's small étale site of the limit.** `toLimitBaseChangeOpensIso` at the open `⊤`, whose
preimage is again `⊤`, followed by `Stacks.EtaleCohomology.opensToEtaleTopIso`. -/
def toLimitBaseChangeTopIso {i₀ : (sys D c B hD hX hc).I} :
    (SmallEtale.toEtaleSite B c.pt hX).obj
        (toLimitBaseChangeEtaleObj D c B hD hX hc
          (opensEtaleObj B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _) ⊤)) ≅
      Scheme.Etale.mk (𝟙 c.pt) :=
  toLimitBaseChangeOpensIso D c B hD hX hc (⊤ : (D.obj (levelIndex D c B hD hX hc i₀)).Opens) ≪≫
    opensToEtaleTopIso c.pt

section Etale

variable (F : EtaleSheafSystem D AddCommGrpCat.{max u v + 1})
  (𝓕 : Sheaf (Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{max u v + 1})

/-! ### The interchange and the sheaf condition at the later level -/

/-- **From an agreement on the objects of the covering datum to an equality of sections over the
whole base change: the interchange and the sheaf condition.** Let `E` be a one-hypercover datum
over an étale object `V₀` of a stage `X_{i₀}` with monomorphic structure morphism, let `a : n ⟶ i₀`
and `b : m ⟶ n` be arrows of the index of the levels of [Stacks, Tag 0EYL], and let `t` be a
section of `F_n` over the base change of `V₀` to `X_n` whose restriction to every object `W₀ k` of
the datum is killed by the transition `...levelCocycleMap` to the level `m`. Then the transition
`...levelDirTransition` of `t` itself vanishes, as a section over the base change of `V₀` to
`X_m`.

This is the step the separatedness half of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab` needs and the
one the development did not have. Its hypothesis is *restrict to the cover, then transition*; the
sheaf condition can only consume *transition, then restrict*, and the pinning lemma
`Stacks.EtaleCohomology.AffineLimitCohomology.levelCocycleMap_app_apply` is what interchanges the
two. The covering is the field `isLevelDatum` of the datum at the composite arrow `b ≫ a`, read
through `Stacks.EtaleCohomology.AffineLimitCohomology.transitionBaseChangeEtaleObjIso` and
`toEtaleSite_map_fVn_comp_transitionBaseChangeEtaleObjIso_hom`; the sheaf condition is
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_eq_of_eq_on_oneHypercoverOf` at the underlying
sheaf of sets, which `CategoryTheory.sheafCompose` along `CategoryTheory.forget` supplies with the
same sections.

Nothing is assumed beyond the `Mono` on `V₀`, which the covering datum does not supply and which
its consumer discharges; no identity law on the system is used or available. -/
theorem levelDirTransition_restrict_eq_zero_of_eq_on_datum
    {i₀ : (sys D c B hD hX hc).I}
    {V₀ : SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _)}
    (hV₀ : Mono (B.inclusion.map V₀.obj.hom))
    (E : OneHypercoverDatum D c B hD hX hc i₀ V₀)
    {n m : (sys D c B hD hX hc).I} (a : n ⟶ i₀) (b : m ⟶ n)
    (t : ToType ((F.obj (levelIndex D c B hD hX hc n)).obj.obj
      (op ((SmallEtale.toEtaleSite B (D.obj (levelIndex D c B hD hX hc n)) (hD _)).obj
        (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a)))))
    (hk : ∀ k : E.κ',
      (levelCocycleMap D c B hD hX hc F b).app
          (op (((sys D c B hD hX hc).u a).obj (E.W₀ k)))
          ((F.obj (levelIndex D c B hD hX hc n)).obj.map
            ((SmallEtale.toEtaleSite B (D.obj (levelIndex D c B hD hX hc n)) (hD _)).map
              (E.fVn n a k)).op t) = 0) :
    (F.obj (levelIndex D c B hD hX hc m)).obj.map
        (transitionBaseChangeEtaleObjIso D c B hD hX hc V₀ a b).hom.op
        ((levelDirTransition D c B hD hX hc F b).hom.app
          (op ((SmallEtale.toEtaleSite B (D.obj (levelIndex D c B hD hX hc n)) (hD _)).obj
            (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a))) t) = 0 := by
  have hsheaf : Presheaf.IsSheaf
      (SmallEtale.topology B (D.obj (levelIndex D c B hD hX hc m)) (hD _))
      ((levelAmbientSheaf D c B hD hX hc F m).obj ⋙ forget AddCommGrpCat.{max u v + 1}) :=
    ((sheafCompose (SmallEtale.topology B (D.obj (levelIndex D c B hD hX hc m)) (hD _))
      (forget AddCommGrpCat.{max u v + 1})).obj (levelAmbientSheaf D c B hD hX hc F m)).property
  refine Stacks.WeakSites.ColimitGlobalSections.sectionOver_eq_of_eq_on_oneHypercoverOf
    (E.isLevelDatum m (b ≫ a)) hsheaf (fun k => ?_)
  have hpin := levelCocycleMap_app_apply D c B hD hX hc F b
    (((sys D c B hD hX hc).u a).obj (E.W₀ k))
    ((SmallEtale.toEtaleSite B (D.obj (levelIndex D c B hD hX hc n)) (hD _)).map
      (E.fVn n a k)) t
  have hmerge := presheafMap_op_apply_eq_of_comp_eq (F.obj (levelIndex D c B hD hX hc m)).obj
    ((SmallEtale.toEtaleSite B (D.obj (levelIndex D c B hD hX hc m)) (hD _)).map
      (E.fVn m (b ≫ a) k))
    (transitionBaseChangeEtaleObjIso D c B hD hX hc V₀ a b).hom
    ((levelEtaleSite D c B hD hX hc m).map
      (eqToHom (Functor.congr_obj ((sys D c B hD hX hc).comp b a) (E.W₀ k))))
    ((levelTransitionIso D c B hD hX hc b).hom.app (((sys D c B hD hX hc).u a).obj (E.W₀ k)))
    ((smallEtaleBaseChange (transitionScheme D c B hD hX hc b)).map
      ((SmallEtale.toEtaleSite B (D.obj (levelIndex D c B hD hX hc n)) (hD _)).map
        (E.fVn n a k)))
    (toEtaleSite_map_fVn_comp_transitionBaseChangeEtaleObjIso_hom D c B hD hX hc hV₀ E a b k)
    ((levelDirTransition D c B hD hX hc F b).hom.app
      (op ((SmallEtale.toEtaleSite B (D.obj (levelIndex D c B hD hX hc n)) (hD _)).obj
        (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a))) t)
  exact (hmerge.trans (hom_apply_eq_zero _ (hpin.symm.trans (hk k)))).trans
    (hom_apply_eq_zero _ rfl).symm

/-! ### The map on sections of the datum at the open `⊤`, and the leg on global sections -/

variable (ιe : ∀ i : Iᵒᵖ,
  (etaleAbelianInverseImage.{max u v, max u v + 1} (conePi c i)).obj (F.obj i) ⟶ 𝓕)

/-- **The map on sections of the covering datum at the object of the open `⊤` of a stage is the
leg on global sections.** For the étale object of the open `⊤` of a stage `X_{i₀}`, a section `s₀`
of `F_n` over the terminal object of Mathlib's small étale site of a lower stage `X_n`, read over
the base change of that object by `transitionBaseChangeTopIso`, is carried by
`Stacks.EtaleCohomology.AffineLimitCohomology.objectSectionsLeg` to the leg of `ι_n` on **global**
sections, read over the base change to the limit by `toLimitBaseChangeTopIso`.

So the hypothesis of the separatedness half of the degree-zero step at this datum is exactly the
vanishing of `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem.legSection`.

Both sides are the transpose `Stacks.EtaleCohomology.etaleTransposeSection` of `ι_n` over the
terminal object followed by one restriction: on the left by the definition of `objectSectionsLeg`
and the naturality of the transpose in the object, on the right by
`Stacks.EtaleCohomology.etaleSectionsRestriction_comp_eq`. The two restrictions agree because both
are morphisms into the base change of the terminal object, whose structure morphism is a
monomorphism (`Stacks.EtaleCohomology.mono_hom_smallEtaleBaseChange_etaleMkId`), so
`Stacks.EtaleCohomology.etale_hom_ext_of_mono` identifies them and no fibre product is
computed. -/
theorem objectSectionsLeg_top_eq {i₀ n : (sys D c B hD hX hc).I} (a : n ⟶ i₀)
    (s₀ : ToType ((F.obj (levelIndex D c B hD hX hc n)).obj.obj
      (op (Scheme.Etale.mk (𝟙 (D.obj (levelIndex D c B hD hX hc n))))))) :
    objectSectionsLeg D c B hD hX hc F 𝓕 ιe
        (opensEtaleObj B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _) ⊤) n a
        ((F.obj (levelIndex D c B hD hX hc n)).obj.map
          (transitionBaseChangeTopIso D c B hD hX hc a).hom.op s₀) =
      𝓕.obj.map (toLimitBaseChangeTopIso D c B hD hX hc (i₀ := i₀)).hom.op
        ((ιe (levelIndex D c B hD hX hc n)).hom.app (op (Scheme.Etale.mk (𝟙 c.pt)))
          (etaleSectionsRestriction.{max u v, max u v + 1}
            (conePi c (levelIndex D c B hD hX hc n))
            (F.obj (levelIndex D c B hD hX hc n)) s₀)) := by
  have hnat := ConcreteCategory.congr_hom
    (etaleTransposeSection_naturality.{max u v + 1, max u v}
      (conePi c (levelIndex D c B hD hX hc n)) (ιe (levelIndex D c B hD hX hc n))
      (transitionBaseChangeTopIso D c B hD hX hc a).hom) s₀
  have hsr := ConcreteCategory.congr_hom
    (etaleSectionsRestriction_comp_eq (conePi c (levelIndex D c B hD hX hc n))
      (ιe (levelIndex D c B hD hX hc n))) s₀
  simp only [ConcreteCategory.comp_apply] at hnat hsr
  have hsq : (toLimitBaseChangeEtaleObjIso D c B hD hX hc
          (opensEtaleObj B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _) ⊤) a).hom ≫
        (smallEtaleBaseChange (conePi c (levelIndex D c B hD hX hc n))).map
          (transitionBaseChangeTopIso D c B hD hX hc a).hom =
      (toLimitBaseChangeTopIso D c B hD hX hc (i₀ := i₀)).hom ≫
        (isTerminalSmallEtaleBaseChangeEtaleMkId.{max u v}
          (conePi c (levelIndex D c B hD hX hc n))).from (Scheme.Etale.mk (𝟙 c.pt)) :=
    etale_hom_ext_of_mono
      (mono_hom_smallEtaleBaseChange_etaleMkId (D.obj (levelIndex D c B hD hX hc n))
        (conePi c (levelIndex D c B hD hX hc n))) _ _
  rw [hsr]
  refine Eq.trans (congrArg (𝓕.obj.map (toLimitBaseChangeEtaleObjIso D c B hD hX hc
    (opensEtaleObj B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _) ⊤) a).hom.op) hnat) ?_
  exact presheafMap_op_apply_eq_of_comp_eq' 𝓕.obj _ _ _ _ hsq _

/-! ### The separatedness at a level, on global sections -/

/-- **The separatedness clause of the degree-zero statement, at a level.** Let `(X_i)` be an
inverse system of schemes over a nonempty directed index with affine transition morphisms, all
objects of a big étale site `B` and all quasi-compact and quasi-separated, let `X` be the vertex of
a limit cone, let `F` be a system of abelian sheaves on Mathlib's small étale sites of the `X_i` in
the sense of [Stacks, Tag 0EZL] and let `ι_i : f_i^{-1}F_i ⟶ 𝓕` be legs whose level cocycle data is
presented on the limit. If a global section `s₀` of `F_n` at a stage is killed by its leg on global
sections, then its transition `...levelDirTransition` to some further stage `X_m` vanishes, read
over the terminal object of Mathlib's small étale site there.

This is the separatedness half of `datumIsColimit_of_realization` at the étale object of the open
`⊤` of the stage — quasi-compact exactly because the stage is, quasi-separated because the stage
is, and with monomorphic structure morphism because an open immersion is a monomorphism — whose
hypothesis is supplied by `objectSectionsLeg_top_eq` and whose conclusion is turned into a
statement over the whole stage by `levelDirTransition_restrict_eq_zero_of_eq_on_datum`. The
one-hypercover datum is produced by
`Stacks.EtaleCohomology.QcSeparatedColimit.exists_oneHypercoverOf_datum`, the affineness of the
projection of the cone coming from `hc`.

The arrow of the index at which the datum is taken is the **identity** of the level, which costs no
identity law on the system: the transition that occurs in the conclusion is the one along the new
arrow `b`, and the datum's own arrow enters only through the objects it indexes. -/
theorem exists_levelDirTransition_top_eq_zero
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (h : EtaleLevelSectionsColimit D c B hD hX hc F 𝓕 (transportLeg F 𝓕 ιe))
    (n : (sys D c B hD hX hc).I)
    (s₀ : ToType ((F.obj (levelIndex D c B hD hX hc n)).obj.obj
      (op (Scheme.Etale.mk (𝟙 (D.obj (levelIndex D c B hD hX hc n)))))))
    (hleg : (ιe (levelIndex D c B hD hX hc n)).hom.app (op (Scheme.Etale.mk (𝟙 c.pt)))
        (etaleSectionsRestriction.{max u v, max u v + 1}
          (conePi c (levelIndex D c B hD hX hc n))
          (F.obj (levelIndex D c B hD hX hc n)) s₀) = 0) :
    ∃ (m : (sys D c B hD hX hc).I) (b : m ⟶ n),
      (F.obj (levelIndex D c B hD hX hc m)).obj.map
          ((isTerminalSmallEtaleBaseChangeEtaleMkId.{max u v}
              (transitionScheme D c B hD hX hc b)).from
            (Scheme.Etale.mk (𝟙 (D.obj (levelIndex D c B hD hX hc m))))).op
          ((levelDirTransition D c B hD hX hc F b).hom.app
            (op (Scheme.Etale.mk (𝟙 (D.obj (levelIndex D c B hD hX hc n))))) s₀) = 0 := by
  have : IsAffineHom (c.π.app (levelIndex D c B hD hX hc n)) :=
    Stacks.EtaleCohomology.QcqsLimitCohomology.isAffineHom_limitProjection D c hc _
  have := compactSpace_opensEtaleObj B (D.obj (levelIndex D c B hD hX hc n)) (hD _) ⊤
    isCompact_univ
  have := quasiSeparatedSpace_opensEtaleObj B (D.obj (levelIndex D c B hD hX hc n)) (hD _) ⊤
  obtain ⟨E⟩ := Stacks.EtaleCohomology.QcSeparatedColimit.exists_oneHypercoverOf_datum
    D c B hD hX hc n (opensEtaleObj B (D.obj (levelIndex D c B hD hX hc n)) (hD _) ⊤)
  have hV₀ := mono_hom_opensEtaleObj B (D.obj (levelIndex D c B hD hX hc n)) (hD _) ⊤
  have hzero : objectSectionsLeg D c B hD hX hc F 𝓕 ιe
      (opensEtaleObj B (D.obj (levelIndex D c B hD hX hc n)) (hD _) ⊤) n (𝟙 n)
      ((F.obj (levelIndex D c B hD hX hc n)).obj.map
        (transitionBaseChangeTopIso D c B hD hX hc (𝟙 n)).hom.op s₀) = 0 :=
    (objectSectionsLeg_top_eq D c B hD hX hc F 𝓕 ιe (𝟙 n) s₀).trans (hom_apply_eq_zero _ hleg)
  obtain ⟨m, b, hagree⟩ := (datumIsColimit_of_realization D c B hD hX hc
    (levelCocycleSystem D c B hD hX hc F)
    ((AffineEtaleModel.modelRestrict B c.pt hX).obj
      ((MayerVietoris.mayerVietorisRestrict c.pt).obj 𝓕))
    (levelPullbackLeg D c B hD hX hc F 𝓕 (transportLeg F 𝓕 ιe)) h E
    (datumRealization D c B hD hX hc F 𝓕 ιe hV₀ E)).2 n (𝟙 n) _ 0
    (hzero.trans (hom_apply_eq_zero _ (hom_apply_eq_zero _ rfl)).symm)
  refine ⟨m, b, ?_⟩
  have hk : ∀ k : E.κ',
      (levelCocycleMap D c B hD hX hc F b).app
        (op (((sys D c B hD hX hc).u (𝟙 n)).obj (E.W₀ k)))
        ((F.obj (levelIndex D c B hD hX hc n)).obj.map
          ((SmallEtale.toEtaleSite B (D.obj (levelIndex D c B hD hX hc n)) (hD _)).map
            (E.fVn n (𝟙 n) k)).op
          ((F.obj (levelIndex D c B hD hX hc n)).obj.map
            (transitionBaseChangeTopIso D c B hD hX hc (𝟙 n)).hom.op s₀)) = 0 := fun k =>
    (hagree k).trans (hom_apply_eq_zero _ (hom_apply_eq_zero _ (hom_apply_eq_zero _ rfl)))
  have h2a := levelDirTransition_restrict_eq_zero_of_eq_on_datum D c B hD hX hc F hV₀ E
    (𝟙 n) b ((F.obj (levelIndex D c B hD hX hc n)).obj.map
      (transitionBaseChangeTopIso D c B hD hX hc (𝟙 n)).hom.op s₀) hk
  have hnat2 : (levelDirTransition D c B hD hX hc F b).hom.app
        (op ((SmallEtale.toEtaleSite B (D.obj (levelIndex D c B hD hX hc n)) (hD _)).obj
          (transitionBaseChangeEtaleObj D c B hD hX hc
            (opensEtaleObj B (D.obj (levelIndex D c B hD hX hc n)) (hD _) ⊤) (𝟙 n))))
        ((F.obj (levelIndex D c B hD hX hc n)).obj.map
          (transitionBaseChangeTopIso D c B hD hX hc (𝟙 n)).hom.op s₀) =
      (F.obj (levelIndex D c B hD hX hc m)).obj.map
        ((smallEtaleBaseChange (transitionScheme D c B hD hX hc b)).map
          (transitionBaseChangeTopIso D c B hD hX hc (𝟙 n)).hom).op
        ((levelDirTransition D c B hD hX hc F b).hom.app
          (op (Scheme.Etale.mk (𝟙 (D.obj (levelIndex D c B hD hX hc n))))) s₀) := by
    have hn := ConcreteCategory.congr_hom
      ((levelDirTransition D c B hD hX hc F b).hom.naturality
        (transitionBaseChangeTopIso D c B hD hX hc (𝟙 n)).hom.op) s₀
    rw [Functor.sheafPushforwardContinuous_obj_obj_map] at hn
    exact (ConcreteCategory.comp_apply
        ((F.obj (levelIndex D c B hD hX hc n)).obj.map
          (transitionBaseChangeTopIso D c B hD hX hc (𝟙 n)).hom.op)
        ((levelDirTransition D c B hD hX hc F b).hom.app
          (op ((SmallEtale.toEtaleSite B (D.obj (levelIndex D c B hD hX hc n)) (hD _)).obj
            (transitionBaseChangeEtaleObj D c B hD hX hc
              (opensEtaleObj B (D.obj (levelIndex D c B hD hX hc n)) (hD _) ⊤) (𝟙 n)))))
        s₀).symm.trans
      (hn.trans (ConcreteCategory.comp_apply
        ((levelDirTransition D c B hD hX hc F b).hom.app
          (op (Scheme.Etale.mk (𝟙 (D.obj (levelIndex D c B hD hX hc n))))))
        ((F.obj (levelIndex D c B hD hX hc m)).obj.map
          ((smallEtaleBaseChange (transitionScheme D c B hD hX hc b)).map
            (transitionBaseChangeTopIso D c B hD hX hc (𝟙 n)).hom).op) s₀))
  have hsq : (transitionBaseChangeEtaleObjIso D c B hD hX hc
          (opensEtaleObj B (D.obj (levelIndex D c B hD hX hc n)) (hD _) ⊤) (𝟙 n) b).hom ≫
        (smallEtaleBaseChange (transitionScheme D c B hD hX hc b)).map
          (transitionBaseChangeTopIso D c B hD hX hc (𝟙 n)).hom =
      (transitionBaseChangeTopIso D c B hD hX hc (b ≫ 𝟙 n)).hom ≫
        (isTerminalSmallEtaleBaseChangeEtaleMkId.{max u v}
            (transitionScheme D c B hD hX hc b)).from
          (Scheme.Etale.mk (𝟙 (D.obj (levelIndex D c B hD hX hc m)))) :=
    etale_hom_ext_of_mono
      (mono_hom_smallEtaleBaseChange_etaleMkId (D.obj (levelIndex D c B hD hX hc n))
        (transitionScheme D c B hD hX hc b)) _ _
  have hbig := ((congrArg (ConcreteCategory.hom
      ((F.obj (levelIndex D c B hD hX hc m)).obj.map
        (transitionBaseChangeEtaleObjIso D c B hD hX hc
          (opensEtaleObj B (D.obj (levelIndex D c B hD hX hc n)) (hD _) ⊤) (𝟙 n) b).hom.op))
      hnat2).symm.trans h2a)
  have hmerge := presheafMap_op_apply_eq_of_comp_eq'
    (F.obj (levelIndex D c B hD hX hc m)).obj
    (transitionBaseChangeEtaleObjIso D c B hD hX hc
      (opensEtaleObj B (D.obj (levelIndex D c B hD hX hc n)) (hD _) ⊤) (𝟙 n) b).hom
    ((smallEtaleBaseChange (transitionScheme D c B hD hX hc b)).map
      (transitionBaseChangeTopIso D c B hD hX hc (𝟙 n)).hom)
    (transitionBaseChangeTopIso D c B hD hX hc (b ≫ 𝟙 n)).hom
    ((isTerminalSmallEtaleBaseChangeEtaleMkId.{max u v}
        (transitionScheme D c B hD hX hc b)).from
      (Scheme.Etale.mk (𝟙 (D.obj (levelIndex D c B hD hX hc m)))))
    hsq ((levelDirTransition D c B hD hX hc F b).hom.app
      (op (Scheme.Etale.mk (𝟙 (D.obj (levelIndex D c B hD hX hc n))))) s₀)
  have hfin := hmerge.symm.trans hbig
  have hinv := presheafMap_op_hom_inv_apply (F.obj (levelIndex D c B hD hX hc m)).obj
    (transitionBaseChangeTopIso D c B hD hX hc (b ≫ 𝟙 n)).symm
    ((F.obj (levelIndex D c B hD hX hc m)).obj.map
      ((isTerminalSmallEtaleBaseChangeEtaleMkId.{max u v}
          (transitionScheme D c B hD hX hc b)).from
        (Scheme.Etale.mk (𝟙 (D.obj (levelIndex D c B hD hX hc m))))).op
      ((levelDirTransition D c B hD hX hc F b).hom.app
        (op (Scheme.Etale.mk (𝟙 (D.obj (levelIndex D c B hD hX hc n))))) s₀))
  exact hinv.symm.trans (hom_apply_eq_zero _ hfin)

/-! ### The separatedness clause at a level, in the vocabulary of the transition on sections -/

variable [∀ i : Iᵒᵖ, HasSheafify (Scheme.smallEtaleTopology (D.obj i)) AddCommGrpCat.{max u v + 1}]

/-- **The separatedness clause at a level, read as the transition on global sections.**
`exists_levelDirTransition_top_eq_zero` with its conclusion rewritten as
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.etaleSectionsTransition`, which is the vocabulary
the degree-zero statement
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_zero_iff` asks for.

The two halves of the rewriting are `Stacks.EtaleCohomology.etaleSectionsRestriction_comp_eq`,
which reads the transition on global sections as the transpose over the terminal object followed by
one restriction, and the bridge
`Stacks.EtaleCohomology.AffineLimitCohomology.levelDirTransition_hom_app`, which identifies that
transpose with the direct-image transition of the system at the levels. -/
theorem exists_etaleSectionsTransition_eq_zero_of_level
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (h : EtaleLevelSectionsColimit D c B hD hX hc F 𝓕 (transportLeg F 𝓕 ιe))
    (n : (sys D c B hD hX hc).I)
    (s₀ : ToType ((F.obj (levelIndex D c B hD hX hc n)).obj.obj
      (op (Scheme.Etale.mk (𝟙 (D.obj (levelIndex D c B hD hX hc n)))))))
    (hleg : (ιe (levelIndex D c B hD hX hc n)).hom.app (op (Scheme.Etale.mk (𝟙 c.pt)))
        (etaleSectionsRestriction.{max u v, max u v + 1}
          (conePi c (levelIndex D c B hD hX hc n))
          (F.obj (levelIndex D c B hD hX hc n)) s₀) = 0) :
    ∃ (m : (sys D c B hD hX hc).I) (b : m ⟶ n),
      SmallEtaleLimitCohomology.etaleSectionsTransition F
        ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map b) s₀ = 0 := by
  obtain ⟨m, b, hb⟩ := exists_levelDirTransition_top_eq_zero D c B hD hX hc F 𝓕 ιe h n s₀ hleg
  refine ⟨m, b, ?_⟩
  have hrestr := ConcreteCategory.congr_hom
    (etaleSectionsRestriction_comp_eq (transitionScheme D c B hD hX hc b)
      (systemTransitionMap F
        ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map b))) s₀
  have hbridge := ConcreteCategory.congr_hom
    (levelDirTransition_hom_app D c B hD hX hc F b
      (Scheme.Etale.mk (𝟙 (D.obj (levelIndex D c B hD hX hc n))))) s₀
  refine hrestr.trans ((ConcreteCategory.comp_apply _ _ s₀).trans ?_)
  exact (congrArg (ConcreteCategory.hom ((F.obj (levelIndex D c B hD hX hc m)).obj.map
    ((isTerminalSmallEtaleBaseChangeEtaleMkId.{max u v}
        (transitionScheme D c B hD hX hc b)).from
      (Scheme.Etale.mk (𝟙 (D.obj (levelIndex D c B hD hX hc m))))).op))
    hbridge.symm).trans hb

end Etale

end AffineLimitCohomology

namespace SmallEtaleLimitCohomology

/-! ### The two cocone laws of a presented system, in degree zero -/

section DegreeZeroCocone

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (Scheme.smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  [∀ i : Iᵒᵖ, HasExt.{u + 1} (Sheaf (Scheme.smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1})]
  {c : Cone D}
  [HasSheafify (Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})]
  {P : (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) →
      (𝒢 : Sheaf (Scheme.smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}) →
      (∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢) → Prop}

/-- **The cocone law of a presented system in degree zero, on global sections.** The leg of a
stage, applied to the transition of a global section from a later stage, is the leg of the later
stage: `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem.leg_comp_transition` in
degree zero, conjugated by the additive equivalence `CategoryTheory.Sheaf.H.equiv₀` through
`PresentedSystem.legSection_eq` and `etaleSectionsTransition_eq`.

Nothing is assumed: the cocone law is a field of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem` in every degree, and
`Sheaf.H.equiv₀` is an equivalence. -/
theorem legSection_etaleSectionsTransition (E : PresentedSystem P) {i j : Iᵒᵖ} (a : i ⟶ j)
    (x : ToType ((E.sys.obj j).obj.obj (op (Scheme.Etale.mk (𝟙 (D.obj j)))))) :
    E.legSection i (etaleSectionsTransition E.sys a x) = E.legSection j x := by
  have h1 := congrArg (Sheaf.H.equiv₀ E.sheaf (etaleMkIdIsTerminal c.pt))
    (E.leg_comp_transition a 0
      ((Sheaf.H.equiv₀ (E.sys.obj j) (etaleMkIdIsTerminal (D.obj j))).symm x))
  rw [E.legSection_eq i, E.legSection_eq j, etaleSectionsTransition_eq E.sys a,
    (Sheaf.H.equiv₀ (E.sys.obj j) (etaleMkIdIsTerminal (D.obj j))).apply_symm_apply] at h1
  exact h1

/-- **The cocycle law of a presented system in degree zero, on global sections.** The transitions
of global sections compose: `...PresentedSystem.transition_comp` in degree zero, conjugated by
`CategoryTheory.Sheaf.H.equiv₀` through `etaleSectionsTransition_eq`.

This is a cocycle law and **not** an identity law: it says nothing about the transition along an
identity arrow, and [Stacks, Tag 0EZL] imposes nothing about it either. -/
theorem etaleSectionsTransition_comp (E : PresentedSystem P) {i j k : Iᵒᵖ} (b : i ⟶ j)
    (a : j ⟶ k) (x : ToType ((E.sys.obj k).obj.obj (op (Scheme.Etale.mk (𝟙 (D.obj k)))))) :
    etaleSectionsTransition E.sys b (etaleSectionsTransition E.sys a x) =
      etaleSectionsTransition E.sys (b ≫ a) x := by
  have h1 := congrArg (Sheaf.H.equiv₀ (E.sys.obj i) (etaleMkIdIsTerminal (D.obj i)))
    (E.transition_comp b a 0
      ((Sheaf.H.equiv₀ (E.sys.obj k) (etaleMkIdIsTerminal (D.obj k))).symm x))
  simp only [etaleSectionsTransition_eq, AddEquiv.apply_symm_apply] at h1
  exact h1

end DegreeZeroCocone

/-! ### The degree-zero hypothesis of the dévissage, at the geometry of Stacks 09YQ -/

section Main

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D) (B : BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt) (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]

include B hD hX hc in
/-- **`H0`: [Stacks, Tag 09YQ] in degree zero, at the tag's own geometry.** Let `I` be a nonempty
directed index, let `(X_i)` be an inverse system of schemes over `Iᵒᵖ` with **affine** transition
morphisms, every `X_i` **quasi-compact and quasi-separated**, all of them and the vertex `X` of a
**limit** cone objects of a big étale site `B`. Then for every presented system `E` — a system of
abelian sheaves on Mathlib's small étale sites of the `X_i` in the sense of [Stacks, Tag 0EZL],
together with a sheaf on `X` and legs exhibiting it as `colim_i f_i^{-1}F_i` — the statement of
[Stacks, Tag 09YQ] holds in degree zero: the global sections of the sheaf on `X` are the filtered
colimit of the global sections of the `F_i` along the legs.

This is the degree-zero hypothesis `H0` of
`...SmallEtaleLimitCohomology.isCohomologyColimit_of_degreeZero_of_affineOpensAcyclic`, the last
of that dévissage's four hypotheses; the other three are `haff`
(`...QcqsLimitCohomology.subsingleton_H_smallEtaleOpensRestrict_of_pullbackPresentation`), `hsub`
(`...AffineLimitCohomology.sectionsDifference_of_pullbackPresentation`) and `H0EXZ`
(`...SmallEtaleLimitCohomology.hasPointwiseInjectiveEmbeddings`).

It is `isCohomologyColimit_zero_iff` with its two clauses supplied: the surjectivity by
`...exists_etaleSectionsRestriction_leg_eq_of_levelSectionsColimit` and the separatedness by
`exists_etaleSectionsTransition_eq_zero_of_level` above, both out of the one input
`...EtaleLevelSectionsColimit`, which `...levelSectionsColimit_of_pullbackPresentation` extracts
from the field `pres` of the presented system through
`...isColimitPresentation_iff` and `...isCompatibleFamily_iff`.

Nothing is assumed beyond the tag's own hypotheses. In particular there is no `Mono` hypothesis, no
sheafification or `Ext` instance binder, and **no identity law** on the system of
[Stacks, Tag 0EZL]: the development is built without one throughout, and
`...isColimitPresentation_zeroTransitionSystem` exhibits presented data whose identity transition
is zero on a nonzero sheaf, so no such law is available to assume. -/
theorem isCohomologyColimit_zero_of_isLimit
    (E : PresentedSystem (c := c) IsColimitPresentation) : IsCohomologyColimit E 0 := by
  obtain ⟨hcompat, hpres⟩ := (isColimitPresentation_iff E.sys E.sheaf E.ι).mp E.pres
  have hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (conePullbackComp c a).inv.app (E.sys.obj j) ≫
          (smallEtalePullbackAb (c.π.app i)).map (E.sys.map a) ≫
            transportLeg E.sys E.sheaf E.ι i =
        transportLeg E.sys E.sheaf E.ι j :=
    fun a => (isCompatibleFamily_iff E.sys E.sheaf E.ι).mp hcompat a
  have h := AffineLimitCohomology.levelSectionsColimit_of_pullbackPresentation D c B hD hX hc
    E.sys E.sheaf (transportLeg E.sys E.sheaf E.ι) hpres hι
  refine (isCohomologyColimit_zero_iff E).mpr ⟨fun y => ?_, fun i s hs => ?_⟩
  · obtain ⟨j, t, ht⟩ :=
      AffineLimitCohomology.exists_etaleSectionsRestriction_leg_eq_of_levelSectionsColimit
        D c B hD hX hc E.sys E.sheaf E.ι h y
    exact ⟨j, t, (ConcreteCategory.comp_apply _ _ t).trans ht⟩
  · obtain ⟨m, b, hb⟩ :=
      AffineLimitCohomology.exists_etaleSectionsTransition_eq_zero_of_level D c B hD hX hc
        E.sys E.sheaf E.ι h
        ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.inverse.obj i)
        (etaleSectionsTransition E.sys
          ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.counitIso.app i).hom s)
        ((ConcreteCategory.comp_apply _ _ _).symm.trans
          ((legSection_etaleSectionsTransition E
            ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.counitIso.app i).hom s).trans hs))
    exact ⟨QcSeparatedColimit.levelIndex D c B hD hX hc m,
      (affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map b ≫
        ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.counitIso.app i).hom,
      (etaleSectionsTransition_comp E _ _ s).symm.trans hb⟩

end Main

end SmallEtaleLimitCohomology

end Stacks.EtaleCohomology

end

