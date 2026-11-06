module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CoproductChartRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSchemeSourceRepresentable
public import StacksFrontier.AlgebraicGeometry.Size.Coverings
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValued
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.CategoryTheory.Sites.SlicePost.Continuous

/-!
# Algebraicity from an atlas by affine schemes (Stacks 0AIS, observation (2))

Let `S` be a scheme contained in a big fppf site `B`. Observation (2) of **Stacks 0AIS** is a
sanity check on the set-theoretic condition: a family `{Xᵢ ⟶ X}` as in Definition 0AIM in which
every `Xᵢ` is an *affine scheme* makes `X` an algebraic space.

The source argues by passing to a larger big fppf site, in which the coproduct `∐ Xᵢ` and the
relation `∐ Xᵢ ×_X Xⱼ` are representable, forming the quotient `X' = U'/R'` there, and
descending the conclusion by Stacks 04W1. The argument here stays inside the chosen site and
builds the scheme atlas by hand, which is what makes the descent step unnecessary: the
set-theoretic condition supplies an object `U` of the site surjecting onto `X`; each member
`Xᵢ` of the family is represented by an affine object `Uᵢ` of the site whose size is bounded by
that of `U`, because an affine scheme mapping to `X` factors fppf-locally through a member of
the family; and the coproduct of one such `Uᵢ` for each point of `U` is again an object of the
site, the size cutoff being a strong prelimit. That coproduct maps to `X` surjectively and
étale-ly, and is the scheme atlas that the definition of an algebraic space asks for.

## Main results

* `AlgebraicGeometry.FormalSpace.isAlgebraicSpace_of_affineSchemeAtlas`: **Stacks 0AIS**,
  observation (2).

## Implementation notes

An affine scheme in the atlas need not itself be an object of the chosen big site. It is
therefore presented by its functor of points restricted to that site
(`Stacks.Groupoids.points`), followed by sheafification in the value universe of formal
algebraic spaces.

**Where the diagonal comes from.** The algebraic-space condition
`AlgebraicGeometry.Space.IsAlgebraicSpaceULift` asks for a representable diagonal, and for a
formal algebraic space that is **Stacks 0AIP**, which this module does not import.
It is not needed: the scheme atlas built here is representable by objects of the site, so
**Stacks 0BGR** — `AlgebraicGeometry.Space.isAlgebraicSpaceULift_of_relative_surjective_etale`
— delivers the whole algebraic-space condition, the diagonal included. Representability of the
members of the atlas is **Stacks 0AHV**
(`AlgebraicGeometry.Space.relativelyRepresentableULift_of_isEtale_of_schemeSource`): each is a
morphism out of an object of the site which is representable by algebraic spaces and étale.
Representability of the atlas itself is
`AlgebraicGeometry.FormalSpace.exists_chart_of_size_le`, whose uniform size bound is the size
estimate against `U` below.

## References

* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u
universe u₁ v₁

namespace AlgebraicGeometry.FormalSpace

private local instance schemeCutoff_isClosedUnderIsomorphisms
    (B : AlgebraicGeometry.BigFppfSite.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (AlgebraicGeometry.schemeSizeBelow B.cutoff) where
  of_iso {X Y} e h := by
    change X.size < B.cutoff at h
    change Y.size < B.cutoff
    rwa [← Scheme.size_congr e]

private local instance schemeCutoff_isClosedUnderLimitsOfShape_walkingCospan
    (B : AlgebraicGeometry.BigFppfSite.{u}) :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (AlgebraicGeometry.schemeSizeBelow B.cutoff) WalkingCospan :=
  .mk' (by
    rintro _ ⟨F, hF⟩
    change (limit F).size < B.cutoff
    rw [Scheme.size_congr (HasLimit.isoOfNatIso (diagramIsoCospan F))]
    exact Scheme.size_pullback_lt _ _ (hF .left) (hF .right))

attribute [local instance] AlgebraicGeometry.Space.schemeCutoff_hasPullbacks

private theorem isSheaf_points
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : Over S) :
    Presheaf.IsSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS)
      (Stacks.Groupoids.points (Over.post B.inclusion) U) := by
  let Q := Scheme.fppfPrecoverage.comap B.inclusion
  have htop : B.topology ≤ Q.toGrothendieck := by
    apply Precoverage.toGrothendieck_mono
    rintro _ _ ⟨E, rfl, hE⟩
    exact B.isFppfCovering_of_isCovering hE
  have : B.inclusion.IsContinuous Q.toGrothendieck Scheme.fppfTopology :=
    Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
      (F := B.inclusion) (J := Q) (K := Scheme.fppfPrecoverage) le_rfl
  have : (Over.post B.inclusion).IsContinuous (Q.toGrothendieck.over (B.obj hS))
      (Scheme.fppfTopology.over S) :=
    Functor.isContinuous_overPost_of_preservesPullbacks _ _ B.inclusion (B.obj hS)
  apply Presheaf.IsSheaf.of_le (J := B.topology.over (B.obj hS))
    (K := Q.toGrothendieck.over (B.obj hS)) (fun T R hR => htop _ hR)
  exact (Over.post (X := B.obj hS) B.inclusion).op_comp_isSheaf_of_isSheaf _
    (Scheme.fppfTopology.over S) (yoneda.obj U)
    ((isSheaf_iff_isSheaf_of_type _ _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))

private noncomputable def restrictedSchemeSheaf
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Over S ⥤ Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1)) :=
  ObjectProperty.lift _
    (uliftYoneda.{u + 1} ⋙ (Functor.whiskeringLeft _ _ _).obj
      (Over.post (X := B.obj hS) B.inclusion).op) (fun U => by
    change Presheaf.IsSheaf _ (Stacks.Groupoids.points _ U ⋙ uliftFunctor.{u + 1, u})
    rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff,
      ← isSheaf_iff_isSheaf_of_type]
    exact isSheaf_points B S hS U)

private noncomputable def pointsYonedaIso
    {C : Type v₁} [Category.{u} C] {S : Scheme.{u}} (F : C ⥤ Over S)
    [F.Full] [F.Faithful] (U : C) : Stacks.Groupoids.points F (F.obj U) ≅ yoneda.obj U := by
  let hF : F.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful F
  refine NatIso.ofComponents (fun _ => Equiv.toIso hF.homEquiv.symm) ?_
  intro X Y f
  ext g
  simp [Stacks.Groupoids.points, hF, Functor.FullyFaithful.homEquiv,
    Functor.FullyFaithful.ofFullyFaithful]

private noncomputable def restrictedSchemeSheafObjIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS) :
    ((restrictedSchemeSheaf B S hS).obj ((Over.post B.inclusion).obj U)).obj ≅
      uliftYoneda.{u + 1}.obj U :=
  Functor.isoWhiskerRight (pointsYonedaIso (Over.post B.inclusion) U) uliftFunctor

private theorem restrictedSchemeSheaf_map_mono
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : Over S} (f : U ⟶ V) [Mono f] :
    Mono ((restrictedSchemeSheaf B S hS).map f) := by
  apply (sheafToPresheaf _ _).mono_of_mono_map
  show Mono (Functor.whiskerLeft _ (uliftYoneda.{u + 1}.map f))
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro T
  apply ConcreteCategory.mono_of_injective
  exact fun x y h => ULift.ext ((cancel_mono f).mp (congrArg ULift.down h))

private theorem mk_globalSections_le (V : Scheme.{u}) :
    Cardinal.mk Γ(V, ⊤) ≤ 2 ^ V.size := by
  let r : Γ(V, ⊤) → ∀ U : V.affineOpens, Γ(V, U.1) :=
    fun x U => V.presheaf.map (Opposite.op (homOfLE le_top)) x
  have hr : Function.Injective r := by
    intro x y h
    apply V.IsSheaf.section_ext
    intro p hp
    obtain ⟨U, hU, hpU, _⟩ := exists_isAffineOpen_mem_and_subset hp
    exact ⟨U, le_top, hpU, congrFun h ⟨U, hU⟩⟩
  apply (Cardinal.mk_le_of_injective hr).trans
  rw [Cardinal.mk_pi]
  apply (Cardinal.prod_le_prod _ (fun _ => V.size) V.mk_sections_le_size).trans
  rw [Cardinal.prod_const']
  calc
    V.size ^ Cardinal.mk V.affineOpens ≤ V.size ^ V.size :=
      Cardinal.power_le_power_left (Cardinal.aleph0_pos.trans_le V.aleph0_le_size).ne'
        V.mk_affineOpens_le_size
    _ = 2 ^ V.size := Cardinal.power_self_eq V.aleph0_le_size

private theorem exists_affine_factor_of_size_lt
    (B : AlgebraicGeometry.BigFppfSite.{u}) {V T : Scheme.{u}} [IsAffine T]
    (hV : B.Contains V) (p : V ⟶ T) :
    ∃ (W : Scheme.{u}) (a : V ⟶ W) (j : W ⟶ T),
      IsAffine W ∧ B.Contains W ∧ Mono j ∧ a ≫ j = p := by
  let A := p.appTop.hom.range
  let r : Γ(T, ⊤) ⟶ CommRingCat.of A :=
    CommRingCat.ofHom p.appTop.hom.rangeRestrict
  let i : CommRingCat.of A ⟶ Γ(V, ⊤) := CommRingCat.ofHom A.subtype
  let W := Spec (CommRingCat.of A)
  let a : V ⟶ W := V.toSpecΓ ≫ Spec.map i
  let j : W ⟶ T := Spec.map r ≫ T.isoSpec.inv
  have hj : Mono j := by
    have := IsClosedImmersion.spec_of_surjective r p.appTop.hom.rangeRestrict_surjective
    dsimp [j]
    infer_instance
  refine ⟨W, a, j, inferInstance, ?_, hj, ?_⟩
  · show W.size < B.cutoff
    rw [Scheme.size_Spec]
    exact max_lt B.aleph0_lt_cutoff ((Cardinal.mk_subtype_le _).trans_lt
      ((mk_globalSections_le V).trans_lt (B.cutoff_isStrongPrelimit hV)))
  · dsimp [a, j]
    rw [Category.assoc, ← Category.assoc (Spec.map i), ← Spec.map_comp,
      show r ≫ i = p.appTop from rfl,
      ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp

private theorem exists_affine_representative_of_epi
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : Over S) [IsAffine T.left]
    (V : AlgebraicGeometry.BigFppfOver B S hS)
    (hV : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1)))
    (eV : hV.obj ≅ uliftYoneda.{u + 1}.obj V)
    (f : hV ⟶ (restrictedSchemeSheaf B S hS).obj T) [Epi f] :
    ∃ W : AlgebraicGeometry.BigFppfOver B S hS,
      IsAffine W.left.obj ∧
        Nonempty (((restrictedSchemeSheaf B S hS).obj T).obj ≅
          uliftYoneda.{u + 1}.obj W) := by
  let H := restrictedSchemeSheaf B S hS
  let F := Over.post (X := B.obj hS) B.inclusion
  let fp : uliftYoneda.{u + 1}.obj V ⟶ (H.obj T).obj := eV.inv ≫ f.hom
  let p : F.obj V ⟶ T := (uliftYonedaEquiv fp).down
  obtain ⟨W, a, j, hWa, hW, hj, haj⟩ :=
    exists_affine_factor_of_size_lt B V.left.property p.left
  let C : Over S := Over.mk (j ≫ T.hom)
  let j' : C ⟶ T := Over.homMk j
  let a' : F.obj V ⟶ C := Over.homMk a ((Category.assoc a j T.hom).symm.trans
    ((congrArg (· ≫ T.hom) haj).trans (Over.w p)))
  have haj' : a' ≫ j' = p := Over.OverMorphism.ext haj
  let g : hV ⟶ H.obj C :=
    ⟨eV.hom ≫ uliftYonedaEquiv.symm (ULift.up a')⟩
  have hgf : g ≫ H.map j' = f := by
    apply Sheaf.hom_ext
    apply (cancel_epi eV.inv).mp
    show eV.inv ≫ (eV.hom ≫ uliftYonedaEquiv.symm (ULift.up a')) ≫
      (H.map j').hom = fp
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    apply uliftYonedaEquiv.injective
    show ULift.up ((F.map (𝟙 V) ≫ a') ≫ j') = ULift.up p
    rw [F.map_id, Category.id_comp, haj']
  have : Epi (H.map j') := epi_of_epi_fac hgf
  have : Mono j' := Over.mono_of_mono_left j'
  have : Mono (H.map j') := restrictedSchemeSheaf_map_mono B S hS j'
  have : IsIso (H.map j') := isIso_of_mono_of_epi _
  let W' : AlgebraicGeometry.BigFppfOver B S hS :=
    Over.mk (Y := B.obj hW) (X := B.obj hS) ⟨j ≫ T.hom⟩
  exact ⟨W', hWa, ⟨(sheafToPresheaf _ _).mapIso (asIso (H.map j')).symm ≪≫
    restrictedSchemeSheafObjIso B S hS W'⟩⟩

private theorem exists_affine_representative
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1)))
    (hset : AlgebraicGeometry.FormalSpace.SatisfiesSetTheoreticCondition B S hS X)
    (T : Over S) [IsAffine T.left]
    (eT : X ≅ (presheafToSheaf (AlgebraicGeometry.BigFppfOver.topology B S hS)
      (Type (u + 1))).obj
      (Stacks.Groupoids.points (Over.post B.inclusion) T ⋙ uliftFunctor.{u + 1, u})) :
    ∃ W : AlgebraicGeometry.BigFppfOver B S hS,
      IsAffine W.left.obj ∧ Nonempty (X.obj ≅ uliftYoneda.{u + 1}.obj W) := by
  obtain ⟨V, R, hV, hR, ⟨eV⟩, _, f, hf, _⟩ := hset
  let H := restrictedSchemeSheaf B S hS
  let e : X ≅ H.obj T := eT ≪≫ (sheafificationIso (H.obj T)).symm
  have : Epi f := hf
  obtain ⟨W, hW, ⟨eW⟩⟩ := exists_affine_representative_of_epi B S hS T V hV eV
    (f ≫ e.hom)
  exact ⟨W, hW, ⟨(sheafToPresheaf _ _).mapIso e ≪≫ eW⟩⟩

private theorem relative_of_representable_source_pullback_test
    {C D : Type*} [Category* C] [Category* D] [HasPullbacks D]
    (Y : C ⥤ D) [Y.Full] [Y.Faithful]
    (P : MorphismProperty C) [P.IsMultiplicative] [P.RespectsIso]
    {F G : D} (f : F ⟶ G) {U : C} (e : Y.obj U ≅ F)
    (hrep : Y.relativelyRepresentable (e.hom ≫ f))
    (hlocal : ∀ (T : C) (q : Y.obj T ⟶ G) (V : C)
      (φ : Y.obj V ⟶ pullback q f),
      P.relative Y φ → P.relative Y (φ ≫ pullback.fst q f)) :
    P.relative Y (e.hom ≫ f) := by
  refine ⟨hrep, fun T V q a p hp => ?_⟩
  have hp' : IsPullback (Y.map p) (a ≫ e.hom) q f :=
    hp.flip.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  have ht := hlocal T q V hp'.isoPullback.hom ((P.relative Y).of_isIso _)
  rw [hp'.isoPullback_hom_fst] at ht
  exact MorphismProperty.of_relative_map ht

private lemma isFpqcCovering_of_fppfCovering {T : Scheme.{u}}
    (E : FppfCovering T) : IsFpqcCovering E.X E.f := by
  refine ⟨E.flat, fun U hU => ?_⟩
  obtain ⟨n, a, V, hV, hcover⟩ := E.exists_finite_affineOpens_cover ⟨U, hU⟩
  refine ⟨n, a, V, hV, fun i => ?_, hcover.symm⟩
  rw [← hcover]
  exact fun x hx => Set.mem_iUnion.mpr ⟨i, hx⟩

private lemma isLocallySurjective_of_isPullback
    {C : Type*} [Category.{u} C] (J : GrothendieckTopology C)
    {F G T P : Cᵒᵖ ⥤ Type (u + 1)} {f : F ⟶ G} {g : T ⟶ G}
    {p : P ⟶ F} {q : P ⟶ T} (hpb : IsPullback p q f g)
    (hf : Presheaf.IsLocallySurjective J f) :
    Presheaf.IsLocallySurjective J q := by
  refine ⟨fun {U} s => J.superset_covering ?_ (hf.imageSieve_mem (g.app _ s))⟩
  rintro V i ⟨x, hx⟩
  let mF : uliftYoneda.{u + 1}.obj V ⟶ F := uliftYonedaEquiv.symm x
  let mT : uliftYoneda.{u + 1}.obj V ⟶ T := uliftYonedaEquiv.symm (T.map i.op s)
  have hw : mF ≫ f = mT ≫ g := by
    apply uliftYonedaEquiv.injective
    simpa [uliftYonedaEquiv_comp, mF, mT] using
      hx.trans (NatTrans.naturality_apply g i.op s).symm
  refine ⟨uliftYonedaEquiv (hpb.lift mF mT hw), ?_⟩
  rw [← uliftYonedaEquiv_comp, hpb.lift_snd]
  exact uliftYonedaEquiv.apply_symm_apply _

private lemma isFppfCovering_iff
    (B : AlgebraicGeometry.BigFppfSite.{u}) {T : B.Schemes} (E : PreZeroHypercover.{u + 1} T) :
    AlgebraicGeometry.IsFppfCovering ⟨T, E⟩ ↔
      (∀ x : T.obj, ∃ i, x ∈ Set.range (E.f i).hom) ∧
        ∀ i, Flat (E.f i).hom ∧ LocallyOfFinitePresentation (E.f i).hom := by
  rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
    PreZeroHypercover.presieve₀, Presieve.map_ofArrows,
    Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  exact Iff.rfl

/-- A covering sieve of an object `U` of the big fppf site over `S` contains the family of a flat
cover of `U` by locally finitely presented morphisms. -/
private lemma exists_fppf_cover_le_sieve
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U : AlgebraicGeometry.BigFppfOver B S hS} {R : Sieve U}
    (hR : R ∈ AlgebraicGeometry.BigFppfOver.topology B S hS U) :
    ∃ E : PreZeroHypercover.{u + 1} U.left,
      ((∀ x : U.left.obj, ∃ i, x ∈ Set.range (E.f i).hom) ∧
        ∀ i, Flat (E.f i).hom ∧ LocallyOfFinitePresentation (E.f i).hom) ∧
      ∀ j, R (Over.homMk (E.f j) : Over.mk (E.f j ≫ U.hom) ⟶ U) := by
  rw [GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨E, hE, hER⟩ := Space.exists_covering_refining_sieve B hR
  exact ⟨E, (isFppfCovering_iff B E).mp (B.isFppfCovering_of_isCovering hE),
    fun j => (Sieve.overEquiv_iff _ _).mp (hER _ _ ⟨j⟩)⟩

private lemma exists_fppfCovering_of_isLocallySurjective
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.BigFppfOver B S hS} (f : X ⟶ Y)
    (hf : Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS)
      (uliftYoneda.{u + 1}.map f)) :
    ∃ E : FppfCovering.{u + 1} Y.left.obj,
      ∀ j, ∃ a : E.X j ⟶ X.left.obj, a ≫ f.left.hom = E.f j := by
  obtain ⟨E, hEF, hER⟩ := exists_fppf_cover_le_sieve B S hS (hf.imageSieve_mem (ULift.up (𝟙 Y)))
  refine ⟨⟨E.I₀, fun j => (E.X j).obj, fun j => (E.f j).hom,
    fun j => (hEF.2 j).1, fun j => (hEF.2 j).2, hEF.1⟩, fun j => ?_⟩
  obtain ⟨a, ha⟩ := hER j
  exact ⟨a.down.left.hom, congrArg (fun k => k.down.left.hom) ha⟩

private alias size_le_of_compact_of_fppf_factorsThrough :=
    AlgebraicGeometry.size_le_of_compact_of_fppf_factorsThrough

private theorem affineChart_size_le
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Z : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1))}
    (U V : AlgebraicGeometry.BigFppfOver B S hS) [IsAffine V.left.obj]
    (eV : Z.obj ≅ uliftYoneda.{u + 1}.obj V)
    (t : uliftYoneda.{u + 1}.obj U ⟶ X.obj)
    (ht : Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS) t)
    (f : Z ⟶ X)
    (hf : (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} f.hom) :
    V.left.obj.size ≤ U.left.obj.size := by
  let Y := uliftYoneda.{u + 1} (C := AlgebraicGeometry.BigFppfOver B S hS)
  let W := hf.rep.pullback t
  let p : W ⟶ U := hf.rep.snd t
  let a : W ⟶ V := Y.preimage (hf.rep.fst t ≫ eV.hom)
  have : Etale p.left.hom := hf.property_snd t
  have ha : Presheaf.IsLocallySurjective
      (AlgebraicGeometry.BigFppfOver.topology B S hS) (Y.map a) := by
    have := isLocallySurjective_of_isPullback
      (AlgebraicGeometry.BigFppfOver.topology B S hS) (hf.rep.isPullback t).flip ht
    dsimp only [a]
    rw [Y.map_preimage]
    infer_instance
  obtain ⟨E, hE⟩ := exists_fppfCovering_of_isLocallySurjective B S hS a ha
  choose g hg using hE
  exact size_le_of_compact_of_fppf_factorsThrough p.left.hom a.left.hom E g hg

/-- Let `fᵢ : Xᵢ ⟶ X` be a family of morphisms of sheaves of types for a Grothendieck topology
`J` such that the induced morphism `∐ Xᵢ ⟶ X` is locally surjective. Then for every object `U`
and every section `x` of `X` over `U`, the supremum over `i` of the image sieves of `x` along
the `fᵢ` is a `J`-covering sieve of `U`. -/
public lemma family_imageSieve_mem
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    [HasSheafify J (Type (max u₁ v₁))]
    [HasColimitsOfSize.{max u₁ v₁, max u₁ v₁} (Sheaf J (Type (max u₁ v₁)))]
    {I : Type (max u₁ v₁)} (Xi : I → Sheaf J (Type (max u₁ v₁)))
    (X : Sheaf J (Type (max u₁ v₁))) (f : ∀ i, Xi i ⟶ X)
    (hf : Sheaf.IsLocallySurjective (Sigma.desc f))
    (U : C) (x : X.obj.obj (Opposite.op U)) :
    (⨆ i, Presheaf.imageSieve (f i).hom x) ∈ J U := by
  let Q : Cᵒᵖ ⥤ Type (max u₁ v₁) := {
    obj T := Σ i, (Xi i).obj.obj T
    map a := ↾fun s => ⟨s.1, (Xi s.1).obj.map a s.2⟩ }
  let q : Q ⟶ X.obj := {
    app T := ↾fun s => (f s.1).hom.app T s.2
    naturality T T' a := by
      ext s
      exact NatTrans.naturality_apply (f s.1).hom a s.2 }
  let incl (i : I) : (Xi i).obj ⟶ Q := {
    app T := ↾fun s => ⟨i, s⟩ }
  let A : Sheaf J (Type (max u₁ v₁)) := (presheafToSheaf J _).obj Q
  let a (i : I) : Xi i ⟶ A := ⟨incl i ≫ toSheafify J Q⟩
  let d : A ⟶ X := ⟨sheafifyLift J q X.property⟩
  have had : Sigma.desc a ≫ d = Sigma.desc f := by
    refine Sigma.hom_ext _ _ fun i => ?_
    simp only [Sigma.ι_desc_assoc, Sigma.ι_desc]
    apply Sheaf.hom_ext
    show (incl i ≫ toSheafify J Q) ≫ sheafifyLift J q X.property = (f i).hom
    rw [Category.assoc, toSheafify_sheafifyLift]
    rfl
  have : Epi d := epi_of_epi_fac had
  have : Sheaf.IsLocallySurjective d := (Sheaf.isLocallySurjective_iff_epi d).mpr inferInstance
  have hq : Presheaf.IsLocallySurjective J q := by
    rw [← toSheafify_sheafifyLift J q X.property]
    exact Presheaf.isLocallySurjective_comp J _ d.hom
  refine J.superset_covering ?_ (hq.imageSieve_mem x)
  rintro V g ⟨⟨i, s⟩, hs⟩
  exact (le_iSup (fun i => Presheaf.imageSieve (f i).hom x) i) _ ⟨s, hs⟩

private lemma mk_points_le (T : Scheme.{u}) :
    Cardinal.mk T ≤ 2 ^ T.size := by
  let m : T → Set T.affineOpens := fun x => {A | x ∈ A.1}
  have hm : Function.Injective m := by
    intro x y h
    apply (T.isBasis_affineOpens.eq_iff).mpr
    rintro _ ⟨A, hA, rfl⟩
    exact Set.ext_iff.mp h ⟨A, hA⟩
  exact (Cardinal.mk_le_of_injective hm).trans
    (Cardinal.mk_set.le.trans
      (Cardinal.power_le_power_left (by simp) T.mk_affineOpens_le_size))

/-- In the big fppf site over `S`, a family `fᵢ : Vᵢ ⟶ U` whose underlying morphisms of
schemes are flat and locally of finite presentation, and whose images jointly cover the points
of `U`, generates a covering sieve of `U`. -/
public lemma fppf_ofArrows_mem
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} {U : AlgebraicGeometry.BigFppfOver B S hS}
    (V : I → AlgebraicGeometry.BigFppfOver B S hS) (f : ∀ i, V i ⟶ U)
    (hflat : ∀ i, Flat (f i).left.hom)
    (hlfp : ∀ i, LocallyOfFinitePresentation (f i).left.hom)
    (hcov : ∀ x : U.left.obj, ∃ i, x ∈ Set.range (f i).left.hom) :
    Sieve.ofArrows V f ∈ AlgebraicGeometry.BigFppfOver.topology B S hS U := by
  let E : PreZeroHypercover.{u + 1} U.left := {
    I₀ := ULift.{u + 1} I
    X i := (V i.down).left
    f i := (f i.down).left }
  have hE : AlgebraicGeometry.IsFppfCovering ⟨U.left, E⟩ :=
    (isFppfCovering_iff B E).mpr ⟨fun x => (hcov x).elim fun i hi => ⟨⟨i⟩, hi⟩,
      fun i => ⟨hflat i.down, hlfp i.down⟩⟩
  obtain ⟨⟨T, F⟩, hF, heq, hequiv⟩ := B.fppf_has_representative ⟨U.left, E⟩ hE
  cases heq
  have hmem : Sieve.generate E.presieve₀ ∈ B.topology U.left := by
    rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hequiv]
    exact Precoverage.generate_mem_toGrothendieck ⟨F, rfl, hF⟩
  rw [GrothendieckTopology.mem_over_iff]
  apply B.topology.superset_covering _ hmem
  apply (Sieve.generate_le_iff _ _).mpr
  rw [Presieve.ofArrows_le_iff]
  exact fun i => (Sieve.overEquiv_iff _ _).mpr ⟨V i.down, Over.homMk (𝟙 _) (by simp [E, Over.w]),
    f i.down, ⟨i.down⟩, by ext; simp [E]⟩

/-- Étaleness after representable base change is local on the source for open covers: let
`kᵢ : Vᵢ ⟶ W` be open immersions in the big fppf site over `S` whose images jointly cover `W`,
and let `q` be a relatively representable morphism from the functor of points of `W` to a
presheaf `X`. If each composite `Vᵢ ⟶ W ⟶ X` is étale after every base change along a
represented point, then so is `q`. -/
public lemma etale_of_openCover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} {W : AlgebraicGeometry.BigFppfOver B S hS}
    (V : I → AlgebraicGeometry.BigFppfOver B S hS) (k : ∀ i, V i ⟶ W)
    (hk : ∀ i, IsOpenImmersion (k i).left.hom)
    (hcov : ∀ w : W.left.obj, ∃ i, w ∈ Set.range (k i).left.hom)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (q : uliftYoneda.{u + 1}.obj W ⟶ X)
    (hrep : uliftYoneda.{u + 1}.relativelyRepresentable q)
    (hf : ∀ i, (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
        (uliftYoneda.map (k i) ≫ q)) :
    (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} q := by
  let C := AlgebraicGeometry.BigFppfOver B S hS
  let A := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let Y := uliftYoneda.{u + 1} (C := C)
  refine ⟨hrep, fun T Z g a p hp => ?_⟩
  let l : Z ⟶ W := Y.preimage a
  have hl : Y.map l = a := Y.map_preimage a
  let D : W.left.obj.OpenCover := {
    I₀ := I
    X i := (V i).left.obj
    f i := (k i).left.hom
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨hcov, hk⟩ }
  let pb (i : I) := (IsPullback.of_hasPullback (k i) l).map A
  let e (i : I) := (pb i).isoPullback
  have hr (i : I) : IsOpenImmersion (pullback.snd (k i) l).left.hom :=
    MorphismProperty.of_isPullback (pb i) (hk i)
  let E : Z.left.obj.OpenCover := {
    I₀ := I
    X i := (pullback (k i) l).left.obj
    f i := (pullback.snd (k i) l).left.hom
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨?_, hr⟩
      intro z
      obtain ⟨i, y, hy⟩ := Scheme.Cover.exists_eq (D.pullback₂ l.left.hom) z
      refine ⟨i, (e i).inv y, ?_⟩
      have he : (e i).inv ≫ (pullback.snd (k i) l).left.hom =
          pullback.snd (k i).left.hom l.left.hom := (pb i).isoPullback_inv_snd
      show (pullback.snd (k i) l).left.hom ((e i).inv y) = z
      exact (congrArg (fun a : pullback (k i).left.hom l.left.hom ⟶ Z.left.obj => a y)
        he).trans hy }
  have : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u})
  show Etale p.left.hom
  apply IsZariskiLocalAtSource.of_openCover (P := @Etale.{u}) E
  intro i
  have hp' : IsPullback a (Y.map p) q g := hp
  have hs := (IsPullback.of_hasPullback (k i) l).map Y
  rw [hl] at hs
  have hc := hs.paste_vert hp'
  rw [← Y.map_comp] at hc
  exact (hf i).property g (Y.map (pullback.fst (k i) l))
    (pullback.snd (k i) l ≫ p) hc

/-- A relatively representable morphism of presheaves on the big fppf site over `S` which is
locally surjective for the fppf topology is surjective after every base change along a
represented point. -/
public lemma relative_surjective_of_locallySurjective
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (f : F ⟶ G)
    (hrep : uliftYoneda.{u + 1}.relativelyRepresentable f)
    (hf : Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS) f) :
    (MorphismProperty.inverseImage (@Surjective : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} f := by
  refine ⟨hrep, fun T V g a p hp => ?_⟩
  obtain ⟨E, hE⟩ := exists_fppfCovering_of_isLocallySurjective B S hS p
    (isLocallySurjective_of_isPullback _ hp hf)
  refine ⟨fun y => ?_⟩
  obtain ⟨j, x, rfl⟩ := E.jointly_surjective y
  obtain ⟨a, ha⟩ := hE j
  exact ⟨a x, by
    show p.left.hom (a x) = (E.f j) x
    rw [← Scheme.Hom.comp_apply, ha]⟩

private local instance etale_respectsIso : MorphismProperty.RespectsIso (@Etale.{u}) := .mk _
  (fun e f hf => by have := hf; infer_instance)
  (fun e f hf => by have := hf; infer_instance)

private local instance inverseImage_etale_isMultiplicative
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).IsMultiplicative where
  id_mem V := by
    change Etale (𝟙 V.left.obj)
    infer_instance
  comp_mem a b ha hb := by
    change Etale (a.left.hom ≫ b.left.hom)
    have : Etale a.left.hom := ha
    have : Etale b.left.hom := hb
    infer_instance

/-- **A morphism out of an object of the site which is representable by algebraic spaces and
étale is representable by objects of the site, and étale after every represented base change.**
Representability by objects of the site is Stacks 0AHV,
`AlgebraicGeometry.Space.relativelyRepresentableULift_of_isEtale_of_schemeSource`, and a
represented base change is étale because the base change of the morphism along the test point
is. -/
public theorem relative_etale_of_isEtale_of_schemeSource
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (V : AlgebraicGeometry.BigFppfOver B S hS) (g : uliftYoneda.{u + 1}.obj V ⟶ X)
    (hg : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g)
    (het : AlgebraicGeometry.Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ k ↦ AlgebraicGeometry.Space.IsEtaleULift.{u + 1} B S hS k.hom) g hg) :
    (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} g := by
  let P : MorphismProperty (AlgebraicGeometry.BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  have : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  have : P.IsMultiplicative := inverseImage_etale_isMultiplicative B S hS
  have hrel := AlgebraicGeometry.Space.relativelyRepresentableULift_of_isEtale_of_schemeSource
    B S hS g V (Iso.refl _) hg het
  simpa using relative_of_representable_source_pullback_test uliftYoneda.{u + 1} P g
    (Iso.refl _) (by simpa using hrel) (fun T q V φ hφ => het T q V φ hφ)

/-- Every point of `U` lies in the image of the base change along `t'` of a member of a family
of étale charts whose image sieves jointly cover `t'`. -/
public theorem exists_mem_range_snd_of_imageSieve_mem
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (U : AlgebraicGeometry.BigFppfOver B S hS) (t' : uliftYoneda.{u + 1}.obj U ⟶ X)
    {I : Type (u + 1)} (Ui : I → AlgebraicGeometry.BigFppfOver B S hS)
    (gi : ∀ i, uliftYoneda.{u + 1}.obj (Ui i) ⟶ X)
    (hgi : ∀ i, (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} (gi i))
    (hcov : (⨆ i, Presheaf.imageSieve (gi i) (uliftYonedaEquiv t')) ∈
      AlgebraicGeometry.BigFppfOver.topology B S hS U) (x : U.left.obj) :
    ∃ i, x ∈ Set.range ((hgi i).rep.snd t').left.hom := by
  let C := AlgebraicGeometry.BigFppfOver B S hS
  let Y := uliftYoneda.{u + 1} (C := C)
  obtain ⟨E, hEF, hER⟩ := exists_fppf_cover_le_sieve B S hS hcov
  obtain ⟨j, y, hy⟩ := hEF.1 x
  let T : C := Over.mk (E.f j ≫ U.hom)
  let b : T ⟶ U := Over.homMk (E.f j)
  have hb : (⨆ i, Presheaf.imageSieve (gi i) (uliftYonedaEquiv t')) b := hER j
  simp only [iSup, Sieve.sSup_apply, Set.mem_range] at hb
  obtain ⟨_, ⟨i, rfl⟩, z, hz⟩ := hb
  let m : Y.obj T ⟶ Y.obj (Ui i) := uliftYonedaEquiv.symm z
  have hw : m ≫ gi i = Y.map b ≫ t' := by
    apply uliftYonedaEquiv.injective
    rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hz.trans (uliftYonedaEquiv_naturality.{u + 1} t' b.op)
  let a : T ⟶ (hgi i).rep.pullback t' := Y.preimage
    (((hgi i).rep.isPullback t').lift m (Y.map b) hw)
  have hab : a ≫ (hgi i).rep.snd t' = b := by
    apply Y.map_injective
    rw [Y.map_comp, Y.map_preimage]
    exact ((hgi i).rep.isPullback t').lift_snd _ _ _
  refine ⟨i, a.left.hom y, ?_⟩
  rwa [← Scheme.Hom.comp_apply, ← show (a ≫ (hgi i).rep.snd t').left.hom =
    a.left.hom ≫ ((hgi i).rep.snd t').left.hom from rfl, hab]

/-- A morphism `q` out of an object of the site is locally surjective when its composites with a
family of morphisms agree with the composites of a locally surjective `t'` with a jointly
surjective family of étale maps. -/
public theorem isLocallySurjective_of_comp_eq_of_fppf_cover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    {U W : AlgebraicGeometry.BigFppfOver B S hS} (t' : uliftYoneda.{u + 1}.obj U ⟶ X)
    (ht' : Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS) t')
    (q : uliftYoneda.{u + 1}.obj W ⟶ X)
    {I : Type u} (V : I → AlgebraicGeometry.BigFppfOver B S hS) (p : ∀ i, V i ⟶ U)
    (r : ∀ i, V i ⟶ W) (hp : ∀ i, Etale (p i).left.hom)
    (hpcov : ∀ x : U.left.obj, ∃ i, x ∈ Set.range (p i).left.hom)
    (hr : ∀ i, uliftYoneda.{u + 1}.map (r i) ≫ q = uliftYoneda.{u + 1}.map (p i) ≫ t') :
    Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS) q := by
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  let Y := uliftYoneda.{u + 1} (C := AlgebraicGeometry.BigFppfOver B S hS)
  have hmem : Sieve.ofArrows V p ∈ J U := fppf_ofArrows_mem B S hS V p
    (fun i => by have := hp i; infer_instance) (fun i => by have := hp i; infer_instance) hpcov
  have hsmall : Presheaf.IsLocallySurjective J (Sigma.desc (fun i => Y.map (p i))) :=
    (GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map
      J p).mp hmem
  let a : ∐ (fun i => Y.obj (V i)) ⟶ Y.obj W := Sigma.desc (fun i => Y.map (r i))
  have hafac : a ≫ q = Sigma.desc (fun i => Y.map (p i)) ≫ t' := by
    refine Sigma.hom_ext _ _ fun i => ?_
    simpa only [a, Sigma.ι_desc_assoc] using hr i
  have : Presheaf.IsLocallySurjective J (a ≫ q) := by
    rw [hafac]
    infer_instance
  exact Presheaf.isLocallySurjective_of_isLocallySurjective J a q

/-- **An fppf sheaf receiving a surjection from an object of the site and a jointly surjective
family of étale charts out of affine objects of the site is an algebraic space.** Let `X` be a
sheaf on the big fppf site of `S` with values in `Type (u + 1)`, let `t' : h_U ⟶ X` be a locally
surjective morphism out of the sheaf represented by an object `U` of the site, and let
`gᵢ : h_{Uᵢ} ⟶ X` be a family, indexed by an arbitrary type, of morphisms out of affine objects
of the site which are representable by objects of the site and étale, and which jointly cover
the section `t'` of `X`. Then `X` is an algebraic space over `S`.

This is the argument of Stacks 0AIS, observation (2), with the members of the family given as
objects of the site from the start. The surjection `t'` bounds every member by the size of `U`,
an affine scheme mapping étale-ly to `X` being covered fppf-locally by a scheme étale over `U`;
one member for each point of `U` already covers, and the coproduct of those is an object of the
site because the cutoff is a strong prelimit. That coproduct is a surjective étale chart
representable by objects of the site, so Stacks 0BGR applies. -/
public theorem isAlgebraicSpaceULift_of_affineEtaleFamily
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1)))
    (U : AlgebraicGeometry.BigFppfOver B S hS) (t' : uliftYoneda.{u + 1}.obj U ⟶ X.obj)
    (ht' : Presheaf.IsLocallySurjective (AlgebraicGeometry.BigFppfOver.topology B S hS) t')
    {I : Type (u + 1)} (Ui : I → AlgebraicGeometry.BigFppfOver B S hS)
    (hUi : ∀ i, IsAffine (Ui i).left.obj)
    (gi : ∀ i, uliftYoneda.{u + 1}.obj (Ui i) ⟶ X.obj)
    (hgi : ∀ i, (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} (gi i))
    (hcov : (⨆ i, Presheaf.imageSieve (gi i) (uliftYonedaEquiv t')) ∈
      AlgebraicGeometry.BigFppfOver.topology B S hS U) :
    AlgebraicGeometry.Space.IsAlgebraicSpaceULift.{u + 1} B S hS X.obj := by
  classical
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  let C := AlgebraicGeometry.BigFppfOver B S hS
  let Y := uliftYoneda.{u + 1} (C := C)
  let P : MorphismProperty C :=
    MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  have hsize (i : I) : (Ui i).left.obj.size ≤ U.left.obj.size := by
    have : IsAffine (Ui i).left.obj := hUi i
    let Z : Sheaf J (Type (u + 1)) :=
      ⟨Y.obj (Ui i), (AlgebraicGeometry.Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1}
        B S hS (Ui i)).isSheaf⟩
    exact affineChart_size_le B S hS U (Ui i) (Iso.refl Z.obj) t' ht'
      (ObjectProperty.homMk (gi i) : Z ⟶ X) (hgi i)
  let Wi (i : I) : C := (hgi i).rep.pullback t'
  let pi (i : I) : Wi i ⟶ U := (hgi i).rep.snd t'
  let ri (i : I) : Wi i ⟶ Ui i := Y.preimage ((hgi i).rep.fst t')
  have hfac (i : I) : Y.map (ri i) ≫ gi i = Y.map (pi i) ≫ t' := by
    rw [Y.map_preimage]
    exact ((hgi i).rep.isPullback t').w
  choose idx hidx using exists_mem_range_snd_of_imageSieve_mem B S hS U t' Ui gi hgi hcov
  obtain ⟨W, k, q, hkq, hk, hkcov, hqrep⟩ :=
    exists_chart_of_size_le B S hS (fun x : U.left.obj => Ui (idx x))
      (fun x => gi (idx x)) (fun x => (hgi (idx x)).rep)
      (B.cutoff_isStrongPrelimit U.left.property) (mk_points_le U.left.obj)
      (fun x => (hsize (idx x)).trans (Cardinal.cantor _).le)
  have hqet : P.relative Y q := etale_of_openCover B S hS _ k hk hkcov q hqrep
    (fun x => (hkq x).symm ▸ hgi (idx x))
  have hqsurj : Presheaf.IsLocallySurjective J q :=
    isLocallySurjective_of_comp_eq_of_fppf_cover B S hS t' ht' q (fun x => Wi (idx x))
      (fun x => pi (idx x)) (fun x => ri (idx x) ≫ k x) (fun x => (hgi (idx x)).property_snd t')
      (fun x => ⟨x, hidx x⟩) fun x => by
        show Y.map (ri (idx x) ≫ k x) ≫ q = Y.map (pi (idx x)) ≫ t'
        rw [Y.map_comp, Category.assoc, show Y.map (k x) ≫ q = gi (idx x) from hkq x]
        exact hfac (idx x)
  exact AlgebraicGeometry.Space.isAlgebraicSpaceULift_of_relative_surjective_etale
    B S hS X.property
    (AlgebraicGeometry.Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS W) q
    (relative_surjective_of_locallySurjective B S hS q hqrep hqsurj) hqet

/-- **Stacks 0AIS, observation (2), the sanity check.** A family `{Xᵢ ⟶ X}` as in
Definition 0AIM — the set-theoretic condition included — in which every `Xᵢ` is an affine
scheme makes `X` an algebraic space.

The affine schemes of the family need not be objects of the chosen site; each is presented by
its restricted functor of points, sheafified. The scheme atlas of the conclusion is assembled
inside the chosen site rather than by descent from a larger one: the set-theoretic condition
gives an object `U` of the site surjecting onto `X`, each `Xᵢ` is then represented by an affine
object of the site of size at most that of `U`, and the coproduct of one such for each point of
`U` is an object of the site because the size cutoff is a strong prelimit.

The diagonal is not a hypothesis: the atlas assembled here is representable by objects of the
site, so Stacks 0BGR gives the algebraic-space condition outright. -/
@[stacks 0AIS "observation (2)"]
public theorem isAlgebraicSpace_of_affineSchemeAtlas
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) (Type (u + 1)))
    (hX : AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpace B S hS X)
    (hAtlas :
      let J := AlgebraicGeometry.BigFppfOver.topology B S hS
      letI : HasColimitsOfSize.{u + 1, u + 1} (Sheaf J (Type (u + 1))) :=
        Sheaf.instHasColimitsOfSize
      ∃ (I : Type (u + 1)) (Xi : I → Sheaf J (Type (u + 1)))
        (f : ∀ i, Xi i ⟶ X),
        (∀ i, AlgebraicGeometry.FormalSpace.IsAffineFormalAlgebraicSpace B S hS (Xi i)) ∧
        (∀ i, ∃ (U : Over S), IsAffine U.left ∧
          Nonempty (Xi i ≅
            (presheafToSheaf J (Type (u + 1))).obj
              (Stacks.Groupoids.points (Over.post B.inclusion) U ⋙
                uliftFunctor.{u + 1, u}))) ∧
        (∀ i, ∃ hfi : AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpacesULift.{u + 1}
            B S hS (f i).hom,
          AlgebraicGeometry.Space.HasPropertyULift.{u + 1} B S hS
            (fun _ _ g ↦ AlgebraicGeometry.Space.IsEtaleULift.{u + 1} B S hS g.hom)
            (f i).hom hfi) ∧
        Sheaf.IsLocallySurjective (Sigma.desc f)) :
    AlgebraicGeometry.Space.IsAlgebraicSpaceULift.{u + 1} B S hS X.obj := by
  classical
  let J := AlgebraicGeometry.BigFppfOver.topology B S hS
  let C := AlgebraicGeometry.BigFppfOver B S hS
  let Y := uliftYoneda.{u + 1} (C := C)
  let P : MorphismProperty C :=
    MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  have : MorphismProperty.IsStableUnderBaseChange
      (@Etale : MorphismProperty Scheme.{u}) := Etale.etale_isStableUnderBaseChange
  have : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  have : P.IsMultiplicative := inverseImage_etale_isMultiplicative B S hS
  have : HasBinaryProducts C := Over.ConstructProducts.over_binaryProduct_of_pullback
  obtain ⟨I, Xi, f, hXi, hschemes, hf, hcover⟩ := hAtlas
  have hrep (i : I) : ∃ U : C, IsAffine U.left.obj ∧
      Nonempty ((Xi i).obj ≅ Y.obj U) := by
    obtain ⟨T, hT, ⟨eT⟩⟩ := hschemes i
    have : IsAffine T.left := hT
    exact exists_affine_representative B S hS (Xi i) (hXi i).1 T eT
  choose Ui hUi eUi using hrep
  let e (i : I) : Y.obj (Ui i) ≅ (Xi i).obj := (Classical.choice (eUi i)).symm
  have he (i : I) : P.relative Y ((e i).hom ≫ (f i).hom) := by
    obtain ⟨hfi, het⟩ := hf i
    exact relative_of_representable_source_pullback_test Y P (f i).hom (e i)
      ((Y.relativelyRepresentable).comp_mem _ _
        (Functor.relativelyRepresentable.of_isIso Y (e i).hom)
        (AlgebraicGeometry.Space.relativelyRepresentableULift_of_isEtale_of_schemeSource
          B S hS (f i).hom (Ui i) (e i) hfi het))
      fun T q V φ hφ => het T q V φ hφ
  obtain ⟨U, R, hU, hR, ⟨eU⟩, _, t, ht, _⟩ := hX.1
  let t' : Y.obj U ⟶ X.obj := eU.inv ≫ t.hom
  have ht' : Presheaf.IsLocallySurjective J t' := by
    have : Sheaf.IsLocallySurjective t := (Sheaf.isLocallySurjective_iff_epi t).mpr ht
    dsimp [t']
    infer_instance
  refine isAlgebraicSpaceULift_of_affineEtaleFamily B S hS X U t' ht' Ui hUi
    (fun i => (e i).hom ≫ (f i).hom) he ?_
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf J (Type (u + 1))) :=
    Sheaf.instHasColimitsOfSize
  refine J.superset_covering ?_ (family_imageSieve_mem J Xi X f hcover U (uliftYonedaEquiv t'))
  refine iSup_le fun i => le_trans ?_ (le_iSup (fun i => Presheaf.imageSieve
    ((e i).hom ≫ (f i).hom) (uliftYonedaEquiv t')) i)
  rintro V g ⟨z, hz⟩
  exact ⟨(e i).inv.app _ z, by simpa using hz⟩

end AlgebraicGeometry.FormalSpace

end
