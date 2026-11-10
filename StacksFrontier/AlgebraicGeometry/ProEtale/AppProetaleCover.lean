module

public import StacksFrontier.AlgebraicGeometry.ProEtale.AppProetaleAlgebras
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.FaithfullyFlatCover
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.WeaklyEtaleIndEtaleExtension

/-!
# From the ring-level Proposition 097Z to a pro-étale cover by affine ind-étale objects

Proposition 097Z is a statement about rings: a weakly étale ring map `A → B` admits a faithfully
flat, ind-étale `B → B'` for which `A → B'` is ind-étale.  The use made of it in the theory of
the small pro-étale site is geometric: `AlgebraicGeometry.ProEtale.HasAppCover`, which says that
every affine object of the small pro-étale site of an affine scheme `S` is covered, in the
pro-étale topology, by a single object of the site `S_app` of Stacks 098X.  This file is the
translation between the two.

`HasAppCover` is the hypothesis of the dense-subsite half of Stacks 098X and, through it, of
Stacks 09BL (3).  The ring-level 097Z is available in two forms: the unconditional
`AlgebraicGeometry.ProEtale.exists_faithfullyFlat_indEtale_extension`, and
`AlgebraicGeometry.ProEtale.exists_faithfullyFlat_indEtale_of_weaklyEtale`, which assumes Lemma
097X and Proposition 097G.  Either gives `HasAppCover`, and hence, from the first, `HasAppCover`
and the dense-subsite conclusion of Stacks 098X for the unrestricted small pro-étale site hold
unconditionally.

## Main results

* `AlgebraicGeometry.ProEtale.weaklyEtale_appTop_of_isAffine` — a weakly étale morphism of
  affine schemes is weakly étale on global sections.
* `AlgebraicGeometry.ProEtale.hasAppCover_of_exists_faithfullyFlat_indEtale` — the
  ring-level Proposition 097Z for the single base ring `Γ(S, ⊤)` implies `HasAppCover S`.
* `AlgebraicGeometry.ProEtale.hasAppCover_of_upstream` — the same conclusion from Lemma 097X and
  Proposition 097G, by composing with the ring-level 097Z.
* `AlgebraicGeometry.ProEtale.hasAppCover` — `HasAppCover` itself, with nothing assumed, from
  the unconditional ring-level 097Z.
* `AlgebraicGeometry.ProEtale.AppProetale.inclusion_isCoverDense` and
  `AlgebraicGeometry.ProEtale.AppProetale.inclusion_isDenseSubsite` — cover density and, for the
  induced topology, the dense-subsite conclusion of Stacks 098X for the unrestricted small
  pro-étale site of an affine scheme, with nothing assumed.
* `AlgebraicGeometry.ProEtale.appInclusion_isCoverDense_of_upstream`,
  `AlgebraicGeometry.ProEtale.appInclusion_isDenseSubsite_of_upstream`,
  `AlgebraicGeometry.ProEtale.AppProetale.topology_le_inducedTopology_of_upstream`,
  `AlgebraicGeometry.ProEtale.isRightAdjoint_proetaleInverseImage_of_upstream` and
  `AlgebraicGeometry.ProEtale.isRightAdjoint_proetaleInverseImage_of_upstream_of_isRightAdjoint`
  — cover-density, the dense-subsite half of Stacks 098X, the containment of topologies, and
  two forms of Stacks 09BL (3), each with the hypothesis `HasAppCover` replaced by Lemma 097X
  and Proposition 097G.

## Implementation notes

Given `V` affine over the affine `S`, the ring map `Γ(S, ⊤) → Γ(V.left, ⊤)` is weakly étale by
`weaklyEtale_appTop_of_isAffine`; the ring-level 097Z produces `B'`, and the covering object is
`AlgebraicGeometry.ProEtale.appOfIndEtaleAlgebra` of the ind-étale `Γ(S, ⊤)`-algebra `B'`, whose
underlying scheme is `Spec B'`.

The covering morphism `Spec B' ⟶ V.left` is written as `Stacks.Smooth.homEquivOfIsAffine.symm`
of `Γ(V.left, ⊤) → B' ≅ Γ(Spec B', ⊤)`, so that its map on global sections is that composite on
the nose, as in `AlgebraicGeometry.ProEtale.appOfIndEtaleAlgebraHom`; both the triangle over `S`
and the three properties of the morphism are then computed from the ring data.  The triangle
is recovered from its image on global sections by `AlgebraicGeometry.ext_of_isAffine`, which
needs `S` affine; on global sections it is the scalar-tower identity
`algebraMap Γ(S, ⊤) B' = algebraMap Γ(V.left, ⊤) B' ∘ algebraMap Γ(S, ⊤) Γ(V.left, ⊤)`.

The covering morphism is *surjective* because `B'` is faithfully flat over `Γ(V.left, ⊤)`: only
the surjectivity half of
`AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine` is extracted.
Flatness is not taken from there and is never used on its own, because the covering criterion
asks for weak étaleness, surjectivity and quasi-compactness, and flatness is already a field of
`AlgebraicGeometry.WeaklyEtale`.  The morphism is quasi-compact because both schemes are affine,
and weakly étale because `B'` is ind-étale over `Γ(V.left, ⊤)`
(`AlgebraicGeometry.ProEtale.weaklyEtale_specMap_of_ind_etale`).  A single such morphism is a
pro-étale covering by `AlgebraicGeometry.Scheme.Hom.singleton_mem_propQCPrecoverage`, and the
precoverage of the small pro-étale site is the comap of the big one along the forgetful functor,
so membership there is membership of the image singleton upstairs.

Translating between the two spellings of ind-étaleness is
`AlgebraicGeometry.ProEtale.indEtale_iff_ind_etale_underMk`.

Nothing here carries a `@[stacks]` attribute.  `HasAppCover` *is* the geometric form of
Proposition 097Z, and `hasAppCover` proves it with nothing assumed, but it is a consequence of
097Z and not 097Z itself: the tag sits on the ring-level statement
`AlgebraicGeometry.ProEtale.exists_faithfullyFlat_indEtale_extension`, which is where the
mathematics of the proposition is.  The same applies to
`AppProetale.inclusion_isDenseSubsite` and Stacks 098X: it proves the conclusion of the tag for
the topology *induced* by the inclusion, whereas 098X states it for the topology generated by
the standard pro-étale coverings, and only `AppProetale.topology_le_inducedTopology` — one half
of the identification — is available; the tag is carried, for the small pro-étale site of a
chosen big site, by
`AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.isEquivalence_restriction`.  The five
compositions at the end of the file carry 097X and 097G as hypotheses and so claim nothing
either.

## References

* [Stacks Project, Tag 097Z](https://stacks.math.columbia.edu/tag/097Z)
* [Stacks Project, Tag 097X](https://stacks.math.columbia.edu/tag/097X)
* [Stacks Project, Tag 097G](https://stacks.math.columbia.edu/tag/097G)
* [Stacks Project, Tag 097N](https://stacks.math.columbia.edu/tag/097N)
* [Stacks Project, Tag 098X](https://stacks.math.columbia.edu/tag/098X)
* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.ProEtale

/-! ## From the scheme level to the ring level -/

/-- A morphism of affine schemes is weakly étale iff the spectrum of its map on global sections
is. -/
private theorem weaklyEtale_iff_specMap_appTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) : WeaklyEtale f ↔ WeaklyEtale (Spec.map f.appTop) :=
  MorphismProperty.arrow_mk_iso_iff (P := @WeaklyEtale) (arrowIsoSpecΓOfIsAffine f)

/-- A weakly étale morphism of affine schemes is weakly étale on global sections. -/
public theorem weaklyEtale_appTop_of_isAffine {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [WeaklyEtale f] :
    @Algebra.WeaklyEtale ↥Γ(Y, ⊤) ↥Γ(X, ⊤) _ _ f.appTop.hom.toAlgebra := by
  rw [← weaklyEtale_specMap_iff]
  exact (weaklyEtale_iff_specMap_appTop f).mp ‹WeaklyEtale f›

/-! ## Proposition 097Z at the level of the small pro-étale site -/

/-- Let `S` be an affine scheme such that every weakly étale `Γ(S, ⊤)`-algebra `B` admits a
faithfully flat ind-étale `B → B'` with `Γ(S, ⊤) → B'` ind-étale. Then every affine object of
the small pro-étale site of `S` is covered, in the pro-étale topology, by a single affine
ind-étale object; that is, `AlgebraicGeometry.ProEtale.HasAppCover S` holds. -/
public theorem hasAppCover_of_exists_faithfullyFlat_indEtale (S : Scheme.{u}) [IsAffine S]
    (h097Z : ∀ (B : Type u) [CommRing B] [Algebra ↥Γ(S, ⊤) B],
      Algebra.WeaklyEtale ↥Γ(S, ⊤) B →
      ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra B B') (_ : Algebra ↥Γ(S, ⊤) B'),
        ∃ _ : IsScalarTower ↥Γ(S, ⊤) B B', Module.FaithfullyFlat B B' ∧
          StacksDraft.IndEtale B B' ∧ StacksDraft.IndEtale ↥Γ(S, ⊤) B') :
    HasAppCover S := by
  intro V hV
  have hleft : IsAffine ((𝟭 Scheme.{u}).obj V.left) := hV
  have hright : IsAffine ((Functor.fromPUnit S).obj V.right) := ‹IsAffine S›
  let : Algebra ↥Γ(S, ⊤) ↥Γ(V.left, ⊤) := (V.hom.appTop).hom.toAlgebra
  obtain ⟨B', _, _, _, _, hff, hindV, hindS⟩ :=
    h097Z ↥Γ(V.left, ⊤) (weaklyEtale_appTop_of_isAffine V.hom)
  let BA : IndEtaleAlgebra ↥Γ(S, ⊤) :=
    ⟨Under.mk (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) B')),
      indEtale_iff_ind_etale_underMk.mp hindS⟩
  let q : Spec (CommRingCat.of B') ⟶ V.left :=
    Stacks.Smooth.homEquivOfIsAffine.symm
      (CommRingCat.ofHom (algebraMap ↥Γ(V.left, ⊤) B') ≫
        (Scheme.ΓSpecIso (CommRingCat.of B')).inv)
  have hq : q.appTop = CommRingCat.ofHom (algebraMap ↥Γ(V.left, ⊤) B') ≫
      (Scheme.ΓSpecIso (CommRingCat.of B')).inv :=
    Stacks.Smooth.homEquivOfIsAffine.apply_symm_apply _
  have hbij : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of B')).inv.hom :=
    ConcreteCategory.bijective_of_isIso _
  have hffr : q.appTop.hom.FaithfullyFlat := by
    rw [hq]
    exact RingHom.FaithfullyFlat.stableUnderComposition _ _
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)
      (RingHom.FaithfullyFlat.of_bijective hbij)
  have hsurj : Surjective q :=
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine q).mpr hffr).2
  have hqc : QuasiCompact q := inferInstance
  have hwq : WeaklyEtale q := by
    refine (weaklyEtale_iff_specMap_appTop q).mpr ?_
    rw [hq, Spec.map_comp]
    have hB : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(V.left, ⊤) B'))) :=
      weaklyEtale_specMap_of_ind_etale _ (indEtale_iff_ind_etale_underMk.mp hindV)
    infer_instance
  have htri : q ≫ V.hom = appOfIndEtaleAlgebraHom S BA := by
    refine ext_of_isAffine ?_
    rw [Scheme.Hom.comp_appTop, hq, appTop_appOfIndEtaleAlgebraHom]
    change _ ≫ _ ≫ _ = CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) B') ≫ _
    rw [← Category.assoc]
    congr 1
    exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq ↥Γ(S, ⊤) ↥Γ(V.left, ⊤) B').symm
  let p : (AppProetale.inclusion S).obj (appOfIndEtaleAlgebra S BA) ⟶ V :=
    MorphismProperty.Over.homMk q htri
  have hmem : Presieve.map (Scheme.ProEt.forget S ⋙ Over.forget S) (Presieve.singleton p) ∈
      Scheme.proetalePrecoverage ((Scheme.ProEt.forget S ⋙ Over.forget S).obj V) := by
    have hmap : (Scheme.ProEt.forget S ⋙ Over.forget S).map p = q := rfl
    rw [Presieve.map_singleton, hmap]
    exact @Scheme.Hom.singleton_mem_propQCPrecoverage @WeaklyEtale _ _ q hwq hsurj hqc
  exact ⟨appOfIndEtaleAlgebra S BA, p, Precoverage.generate_mem_toGrothendieck hmem⟩

/-- Granted Lemma 097X (`h097X`) and Proposition 097G (`h097G`), every affine object of the small
pro-étale site of an affine scheme is covered, in the pro-étale topology, by a single affine
ind-étale object. -/
public theorem hasAppCover_of_upstream (S : Scheme.{u}) [IsAffine S]
    (h097X : ∀ (R T : Type u) [CommRing R] [CommRing T] [Algebra R T],
      (∀ q : Ideal T, ∀ [q.IsPrime],
        letI := (Ideal.ResidueField.map (q.comap (algebraMap R T)) q
          (algebraMap R T) rfl).toAlgebra
        Algebra.IsAlgebraic (q.comap (algebraMap R T)).ResidueField q.ResidueField) →
      ∃ (C E : Type u) (_ : CommRing C) (_ : CommRing E) (_ : Algebra R C) (_ : Algebra T E)
          (_ : Algebra C E) (_ : Algebra R E) (_ : IsScalarTower R C E)
          (_ : IsScalarTower R T E),
        Module.FaithfullyFlat R C ∧ StacksDraft.IndEtale R C ∧
          Module.FaithfullyFlat T E ∧ StacksDraft.IndEtale T E ∧
          (∀ (m : Ideal E) [m.IsMaximal], (m.comap (algebraMap C E)).IsMaximal) ∧
          (∀ (n : Ideal C) [n.IsMaximal], StrictlyHenselianLocalRing (Localization.AtPrime n)))
    (h097G : ∀ (R T : Type u) [CommRing R] [CommRing T] [Algebra R T],
      Algebra.IdentifiesLocalRings R T →
      ∃ (T' : Type u) (_ : CommRing T') (_ : Algebra T T') (_ : Algebra R T')
          (_ : IsScalarTower R T T'),
        Module.FaithfullyFlat T T' ∧ Algebra.IsIndZariski T T' ∧ Algebra.IsIndZariski R T') :
    HasAppCover S :=
  hasAppCover_of_exists_faithfullyFlat_indEtale S fun B _ _ hAB ↦
    exists_faithfullyFlat_indEtale_of_weaklyEtale _ B hAB h097X h097G

/-! ## Proposition 097Z, and the dense subsite of Stacks 098X, with nothing assumed -/

/-- Every affine object of the small pro-étale site of an affine scheme `S` is covered, in the
pro-étale topology, by a single affine ind-étale object. -/
public theorem hasAppCover (S : Scheme.{u}) [IsAffine S] : HasAppCover S :=
  hasAppCover_of_exists_faithfullyFlat_indEtale S fun B _ inst hAB ↦ by
    have halg : ((algebraMap ↥Γ(S, ⊤) B).toAlgebra : Algebra ↥Γ(S, ⊤) B) = inst :=
      Algebra.algebra_ext _ _ fun _ ↦ rfl
    have hAB' : let := (algebraMap ↥Γ(S, ⊤) B).toAlgebra; Algebra.WeaklyEtale ↥Γ(S, ⊤) B := by
      rwa [halg]
    obtain ⟨B', hB', g, hgff, hindBB', hindAB'⟩ :=
      exists_faithfullyFlat_indEtale_extension (algebraMap ↥Γ(S, ⊤) B) hAB'
    let _ : CommRing B' := hB'
    let _ : Algebra B B' := g.toAlgebra
    let _ : Algebra ↥Γ(S, ⊤) B' := (g.comp (algebraMap ↥Γ(S, ⊤) B)).toAlgebra
    exact ⟨B', hB', inferInstance, inferInstance, IsScalarTower.of_algebraMap_eq' rfl,
      RingHom.faithfullyFlat_algebraMap_iff.mp hgff,
      indEtale_of_indEtaleUnder B B' hindBB',
      indEtale_of_indEtaleUnder ↥Γ(S, ⊤) B' hindAB'⟩

/-- The affine ind-étale objects are cover-dense in the small pro-étale site of an affine
scheme. -/
public instance AppProetale.inclusion_isCoverDense (S : Scheme.{u}) [IsAffine S] :
    (AppProetale.inclusion S).IsCoverDense (Scheme.ProEt.topology S) :=
  appInclusion_isCoverDense S (hasAppCover S)

/-- The affine ind-étale objects form a dense subsite of the small pro-étale site
`AlgebraicGeometry.Scheme.ProEt` of an affine scheme, for the topology induced on them by the
inclusion. -/
public theorem AppProetale.inclusion_isDenseSubsite (S : Scheme.{u}) [IsAffine S] :
    (AppProetale.inclusion S).IsDenseSubsite
      ((AppProetale.inclusion S).inducedTopology (Scheme.ProEt.topology S))
      (Scheme.ProEt.topology S) :=
  appInclusion_isDenseSubsite S (hasAppCover S)

/-! ## The compositions: Stacks 098X and Stacks 09BL (3) from Lemma 097X and Proposition 097G -/

section Upstream

variable (h097X : ∀ (R T : Type u) [CommRing R] [CommRing T] [Algebra R T],
    (∀ q : Ideal T, ∀ [q.IsPrime],
      letI := (Ideal.ResidueField.map (q.comap (algebraMap R T)) q
        (algebraMap R T) rfl).toAlgebra
      Algebra.IsAlgebraic (q.comap (algebraMap R T)).ResidueField q.ResidueField) →
    ∃ (C E : Type u) (_ : CommRing C) (_ : CommRing E) (_ : Algebra R C) (_ : Algebra T E)
        (_ : Algebra C E) (_ : Algebra R E) (_ : IsScalarTower R C E)
        (_ : IsScalarTower R T E),
      Module.FaithfullyFlat R C ∧ StacksDraft.IndEtale R C ∧
        Module.FaithfullyFlat T E ∧ StacksDraft.IndEtale T E ∧
        (∀ (m : Ideal E) [m.IsMaximal], (m.comap (algebraMap C E)).IsMaximal) ∧
        (∀ (n : Ideal C) [n.IsMaximal], StrictlyHenselianLocalRing (Localization.AtPrime n)))
  (h097G : ∀ (R T : Type u) [CommRing R] [CommRing T] [Algebra R T],
    Algebra.IdentifiesLocalRings R T →
    ∃ (T' : Type u) (_ : CommRing T') (_ : Algebra T T') (_ : Algebra R T')
        (_ : IsScalarTower R T T'),
      Module.FaithfullyFlat T T' ∧ Algebra.IsIndZariski T T' ∧ Algebra.IsIndZariski R T')

include h097X h097G

/-- The affine ind-étale objects are cover-dense in the small pro-étale site of an affine
scheme, granted Lemma 097X and Proposition 097G. -/
public theorem appInclusion_isCoverDense_of_upstream (S : Scheme.{u}) [IsAffine S] :
    (AppProetale.inclusion S).IsCoverDense (Scheme.ProEt.topology S) :=
  appInclusion_isCoverDense S (hasAppCover_of_upstream S h097X h097G)

/-- Granted Lemma 097X and Proposition 097G, the affine ind-étale objects form a dense subsite of
the small pro-étale site of an affine scheme, for the topology induced on them by the
inclusion. -/
public theorem appInclusion_isDenseSubsite_of_upstream (S : Scheme.{u}) [IsAffine S] :
    (AppProetale.inclusion S).IsDenseSubsite
      ((AppProetale.inclusion S).inducedTopology (Scheme.ProEt.topology S))
      (Scheme.ProEt.topology S) :=
  appInclusion_isDenseSubsite S (hasAppCover_of_upstream S h097X h097G)

/-- The topology generated by the finite standard pro-étale covering families of affine ind-étale
objects is contained in the topology induced by the inclusion, granted Lemma 097X and Proposition
097G. -/
public theorem AppProetale.topology_le_inducedTopology_of_upstream (S : Scheme.{u})
    [IsAffine S] :
    AppProetale.topology S ≤
      (AppProetale.inclusion S).inducedTopology (Scheme.ProEt.topology S) :=
  AppProetale.topology_le_inducedTopology S (hasAppCover_of_upstream S h097X h097G)

/-- Granted Lemma 097X and Proposition 097G, and given a continuous left adjoint `W` of the
base-change functor `appBaseChange i` on the affine ind-étale sites, the pro-étale inverse image
along a morphism `i` of affine schemes is itself a right adjoint (Stacks 09BL (3)). -/
public theorem isRightAdjoint_proetaleInverseImage_of_upstream {Z X : Scheme.{u}} [IsAffine X]
    [IsAffine Z] (i : Z ⟶ X) (W : AppProetale Z ⥤ AppProetale X)
    (hW : W.IsContinuous ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z))
      ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X)))
    (adj : W ⊣ appBaseChange i) :
    (Functor.sheafPullbackConstruction.sheafPullback (Scheme.proetaleBaseChange i)
      (Type (max (u + 1) w)) (Scheme.ProEt.topology X)
      (Scheme.ProEt.topology Z)).IsRightAdjoint :=
  isRightAdjoint_proetaleInverseImage_of_hasAppCover i
    (hasAppCover_of_upstream X h097X h097G) (hasAppCover_of_upstream Z h097X h097G) W hW adj

/-- Granted Lemma 097X and Proposition 097G, if the base-change functor `appBaseChange i` on the
affine ind-étale sites is a right adjoint whose left adjoint is continuous, then the pro-étale
inverse image along the morphism `i` of affine schemes is itself a right adjoint
(Stacks 09BL (3)). -/
public theorem isRightAdjoint_proetaleInverseImage_of_upstream_of_isRightAdjoint
    {Z X : Scheme.{u}} [IsAffine X] [IsAffine Z] (i : Z ⟶ X)
    [(appBaseChange i).IsRightAdjoint]
    (hW : ((appBaseChange i).leftAdjoint).IsContinuous
      ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z))
      ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X))) :
    (Functor.sheafPullbackConstruction.sheafPullback (Scheme.proetaleBaseChange i)
      (Type (max (u + 1) w)) (Scheme.ProEt.topology X)
      (Scheme.ProEt.topology Z)).IsRightAdjoint :=
  isRightAdjoint_proetaleInverseImage_of_isRightAdjoint_appBaseChange i
    (hasAppCover_of_upstream X h097X h097G) (hasAppCover_of_upstream Z h097X h097G) hW

end Upstream

end AlgebraicGeometry.ProEtale

end
