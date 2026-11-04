module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiLimits
public import StacksFrontier.AlgebraicGeometry.Topologies.BigZariski.Restriction

/-!
# Sheaves on the big Zariski site are compatible systems of sheaves on the small sites

A sheaf on the big Zariski site of a scheme `S` is given by a sheaf on each scheme over `S`
together with comparison maps along the morphisms over `S`, subject to a cocycle identity and
invertibility along open immersions.  This file proves that the canonical restriction functor
realising that description is an equivalence of categories.

The inverse construction takes a compatible system `D` to the presheaf `T ↦ Γ(T, D_T)` on the
big site.  That this presheaf is a sheaf is checked by reducing a big-site covering to one by
opens, using that each `D_T` is a sheaf on the space of `T`; full faithfulness and essential
surjectivity then follow from the identification of sections.

## Main results

* `AlgebraicGeometry.bigZariskiSheafRestriction_isEquivalence` — canonical restriction is
  fully faithful and essentially surjective.
* `AlgebraicGeometry.characterizeSheafBigZariski` — the resulting equivalence of categories.
* `AlgebraicGeometry.characterizeSheafBigZariski_functor` — its functor is the canonical
  restriction functor, not an arbitrary equivalent assignment.

## References

* [Stacks Project, Tag 0213](https://stacks.math.columbia.edu/tag/0213)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u v

namespace AlgebraicGeometry

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

private def dataPushforwardMap (D : BigZariskiSheafData.{u, v} B S hS)
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T) :
    D.sheaf T ⟶ (TopCat.Sheaf.directImage.{u, v}
      (B.inclusion.map f.left).base).obj (D.sheaf T') :=
  (TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v} (B.inclusion.map f.left).base).homEquiv
    (D.sheaf T) (D.sheaf T') (D.pullback f)

private theorem dataPushforwardMap_comp (D : BigZariskiSheafData.{u, v} B S hS)
    {T T' T'' : BigZariskiOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T') :
    dataPushforwardMap B S hS D f ≫
      (TopCat.Sheaf.directImage.{u, v} (B.inclusion.map f.left).base).map
        (dataPushforwardMap B S hS D g) = dataPushforwardMap B S hS D (g ≫ f) :=
  TopCat.Sheaf.inverseImage_adjoint_comp _ _ _ _ _ _ _ _ (D.pullback_comp f g)

/-- The comparison on sections over an open of the target, landing in the sections of the
sheaf on the source over the preimage of that open.  Writing the codomain this way, rather
than as the sections of the direct image, is what lets the rewriting below see the two
composable maps as composable. -/
private def dataPushforwardApp (D : BigZariskiSheafData.{u, v} B S hS)
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T) (V : Opens T.left.obj.carrier) :
    (D.sheaf T).obj.obj (op V) ⟶
      (D.sheaf T').obj.obj (op ((Opens.map (B.inclusion.map f.left).base).obj V)) :=
  (dataPushforwardMap B S hS D f).hom.app (op V)

/-- The section comparison is natural in the open subset. -/
private theorem dataPushforwardApp_naturality (D : BigZariskiSheafData.{u, v} B S hS)
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    {V W : Opens T.left.obj.carrier} (k : V ⟶ W) :
    (D.sheaf T).obj.map k.op ≫ dataPushforwardApp B S hS D f V =
      dataPushforwardApp B S hS D f W ≫
        (D.sheaf T').obj.map ((Opens.map (B.inclusion.map f.left).base).map k).op :=
  (dataPushforwardMap B S hS D f).hom.naturality k.op

/-- The section comparisons compose. -/
private theorem dataPushforwardApp_comp (D : BigZariskiSheafData.{u, v} B S hS)
    {T T' T'' : BigZariskiOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T')
    (W : Opens T.left.obj.carrier) :
    dataPushforwardApp B S hS D f W ≫
        dataPushforwardApp B S hS D g ((Opens.map (B.inclusion.map f.left).base).obj W) =
      dataPushforwardApp B S hS D (g ≫ f) W :=
  congrArg (fun a => a.hom.app (op W)) (dataPushforwardMap_comp B S hS D f g)

private def dataGlobalSectionsMap (D : BigZariskiSheafData.{u, v} B S hS)
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T) :
    (D.sheaf T).obj.obj (op ⊤) ⟶ (D.sheaf T').obj.obj (op ⊤) :=
  (dataPushforwardMap B S hS D f).hom.app (op ⊤)

private theorem dataGlobalSectionsMap_comp (D : BigZariskiSheafData.{u, v} B S hS)
    {T T' T'' : BigZariskiOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T') :
    dataGlobalSectionsMap B S hS D f ≫ dataGlobalSectionsMap B S hS D g =
      dataGlobalSectionsMap B S hS D (g ≫ f) :=
  dataPushforwardApp_comp B S hS D f g ⊤

/-- Restriction along the identity acts as the identity on global sections.  Both the unit of
the adjunction and the comparison map are isomorphisms here, so the map is an idempotent
isomorphism. -/
private theorem dataGlobalSectionsMap_id (D : BigZariskiSheafData.{u, v} B S hS)
    (T : BigZariskiOver B S hS) :
    dataGlobalSectionsMap B S hS D (𝟙 T) = 𝟙 _ := by
  let X := T.left.obj.toTopCat
  let R := TopCat.Sheaf.directImage.{u, v} (𝟙 X)
  let e : R ≅ 𝟭 _ := Functor.sheafPushforwardContinuousId'
    (Opens.mapId X) (Type (max u v)) (Opens.grothendieckTopology X)
  have hRe : R.IsEquivalence := Functor.isEquivalence_of_iso e.symm
  let adj := TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v} (𝟙 X)
  have hunit : IsIso (adj.unit.app (D.sheaf T)) := inferInstance
  have hopen : IsOpenImmersion (B.inclusion.map (𝟙 T : T ⟶ T).left) := by
    rw [show (𝟙 T : T ⟶ T).left = 𝟙 T.left from rfl, B.inclusion.map_id]
    infer_instance
  have hpb : IsIso (D.pullback (𝟙 T)) := D.isIso_pullback (𝟙 T)
  have hm : dataGlobalSectionsMap B S hS D (𝟙 T) =
      (adj.unit.app (D.sheaf T)).hom.app (op ⊤) ≫
        (D.pullback (𝟙 T)).hom.app (op ⊤) :=
    congrArg (fun a => a.hom.app (op ⊤))
      (adj.homEquiv_unit (f := D.pullback (𝟙 T)))
  have h1 : IsIso ((adj.unit.app (D.sheaf T)).hom.app (op ⊤)) :=
    CategoryTheory.Sheaf.isIso_hom_app _ _
  have h2 : IsIso ((D.pullback (𝟙 T)).hom.app (op ⊤)) := CategoryTheory.Sheaf.isIso_hom_app _ _
  have h3 : IsIso (dataGlobalSectionsMap B S hS D (𝟙 T)) := by
    rw [hm]
    exact IsIso.comp_isIso' h1 h2
  have h := dataGlobalSectionsMap_comp B S hS D (𝟙 T) (𝟙 T)
  rw [Category.id_comp] at h
  exact (cancel_mono (dataGlobalSectionsMap B S hS D (𝟙 T))).mp
    (h.trans (Category.id_comp _).symm)

private def dataPresheaf (D : BigZariskiSheafData.{u, v} B S hS) :
    (BigZariskiOver B S hS)ᵒᵖ ⥤ Type (max u v) where
  obj T := (D.sheaf T.unop).obj.obj (op ⊤)
  map f := dataGlobalSectionsMap B S hS D f.unop
  map_id T := dataGlobalSectionsMap_id B S hS D T.unop
  map_comp f g := (dataGlobalSectionsMap_comp B S hS D f.unop g.unop).symm

private theorem bigZariskiSheafRestriction_faithful :
    (bigZariskiSheafRestriction.{u, v} B S hS).Faithful where
  map_injective {F G} {α β} h := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext T
    cases T with
    | op T =>
      ext s
      obtain ⟨t, ht⟩ := (bigZariskiSheafRestriction_sectionEquiv B S hS F T).surjective s
      have hp := congrArg (fun φ : (bigZariskiSheafRestriction B S hS).obj F ⟶
          (bigZariskiSheafRestriction B S hS).obj G =>
        bigZariskiSheafRestriction_sectionEquiv B S hS G T
          ((φ.app T).hom.app (op ⊤) t)) h
      have hN (γ : F ⟶ G) := bigZariskiSheafRestriction_sectionEquiv_naturality B S hS γ T t
      have hh := (hN α).symm.trans (hp.trans (hN β))
      rwa [ht] at hh

private def dataSectionMap (D : BigZariskiSheafData.{u, v} B S hS)
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    (U : Opens T'.left.obj.carrier) (V : Opens T.left.obj.carrier)
    (h : U ≤ (Opens.map (B.inclusion.map f.left).base).obj V) :
    (D.sheaf T).obj.obj (op V) ⟶ (D.sheaf T').obj.obj (op U) :=
  dataPushforwardApp B S hS D f V ≫ (D.sheaf T').obj.map (homOfLE h).op

/-- Restriction maps compose: the comparison for `g ≫ f` on a nested triple of opens is the
composite of the comparisons for `f` and for `g`. -/
private theorem dataSectionMap_comp (D : BigZariskiSheafData.{u, v} B S hS)
    {T T' T'' : BigZariskiOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T')
    (U : Opens T''.left.obj.carrier) (V : Opens T'.left.obj.carrier)
    (W : Opens T.left.obj.carrier)
    (h₁ : V ≤ (Opens.map (B.inclusion.map f.left).base).obj W)
    (h₂ : U ≤ (Opens.map (B.inclusion.map g.left).base).obj V)
    (h₃ : U ≤ (Opens.map (B.inclusion.map (g ≫ f).left).base).obj W) :
    dataSectionMap B S hS D f V W h₁ ≫ dataSectionMap B S hS D g U V h₂ =
      dataSectionMap B S hS D (g ≫ f) U W h₃ := by
  dsimp only [dataSectionMap]
  simp only [Category.assoc]
  rw [← Category.assoc ((D.sheaf T').obj.map (homOfLE h₁).op),
    dataPushforwardApp_naturality]
  simp only [Category.assoc]
  rw [← (D.sheaf T'').obj.map_comp, ← Category.assoc, dataPushforwardApp_comp]
  congr 2

private theorem dataSectionMap_isIso (D : BigZariskiSheafData.{u, v} B S hS)
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    [IsOpenImmersion (B.inclusion.map f.left)] (U : Opens T'.left.obj.carrier)
    (V : Opens T.left.obj.carrier)
    (hV : (Scheme.Hom.isOpenEmbedding (B.inclusion.map f.left)).functor.obj U = V)
    (h : U ≤ (Opens.map (B.inclusion.map f.left).base).obj V) :
    IsIso (dataSectionMap B S hS D f U V h) := by
  subst V
  let ftop : T'.left.obj.toTopCat ⟶ T.left.obj.toTopCat := (B.inclusion.map f.left).base
  let hf : Topology.IsOpenEmbedding ftop := Scheme.Hom.isOpenEmbedding (B.inclusion.map f.left)
  let := hf.functor_isContinuous
  let adj := hf.isOpenMap.adjunction.sheafPushforwardContinuous
    (E := Type (max u v)) (Opens.grothendieckTopology T'.left.obj.toTopCat)
      (Opens.grothendieckTopology T.left.obj.toTopCat)
  let a := (adj.homEquiv (D.sheaf T) (D.sheaf T')).symm
    (dataPushforwardMap B S hS D f)
  have ha : a = (adj.leftAdjointUniq (TopCat.Sheaf.inverseImagePushforwardAdjunction
      (B.inclusion.map f.left).base)).hom.app (D.sheaf T) ≫
        D.pullback f := by
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, ← Adjunction.homEquiv_unit]
    rfl
  have : IsIso (D.pullback f) := D.isIso_pullback f
  have : IsIso a := by
    rw [ha]
    infer_instance
  have he : dataSectionMap B S hS D f U (hf.functor.obj U) h =
      a.hom.app (op U) := by
    dsimp only [a]
    rw [Adjunction.homEquiv_counit]
    rfl
  rw [he]
  show IsIso (((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op U)).map a))
  infer_instance

/-- Restricting on the target before applying the comparison is the same as applying the
comparison for the larger open. -/
private theorem dataSectionMap_restrict (D : BigZariskiSheafData.{u, v} B S hS)
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    (U : Opens T'.left.obj.carrier) {V W : Opens T.left.obj.carrier} (k : W ⟶ V)
    (h : U ≤ (Opens.map (B.inclusion.map f.left).base).obj V)
    (h' : U ≤ (Opens.map (B.inclusion.map f.left).base).obj W) :
    (D.sheaf T).obj.map k.op ≫ dataSectionMap B S hS D f U W h' =
      dataSectionMap B S hS D f U V h := by
  dsimp only [dataSectionMap]
  rw [← Category.assoc, dataPushforwardApp_naturality, Category.assoc,
    ← (D.sheaf T').obj.map_comp]
  congr 2

private theorem dataSectionMap_top (D : BigZariskiSheafData.{u, v} B S hS)
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T) :
    dataSectionMap B S hS D f ⊤ ⊤ le_top = dataGlobalSectionsMap B S hS D f := by
  dsimp only [dataSectionMap, dataGlobalSectionsMap, dataPushforwardApp]
  refine Eq.trans ?_ (Category.comp_id ((dataPushforwardMap B S hS D f).hom.app (op ⊤)))
  congr 1
  exact (D.sheaf T').obj.map_id _

private def smallStructureArrow (T : BigZariskiOver B S hS)
    (X : SmallZariski B T.left.obj T.left.property) :
    (smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom).obj X ⟶ T :=
  Over.homMk X.obj.hom

/-- The whole space of a small-site object lies over its open. -/
private theorem top_le_preimage_smallStructureArrow (T : BigZariskiOver B S hS)
    (X : SmallZariski B T.left.obj T.left.property) :
    ⊤ ≤ (Opens.map (B.inclusion.map (smallStructureArrow B S hS T X).left).base).obj
      ((smallZariskiToOpens B T.left.obj T.left.property).obj X) :=
  fun x _ => ⟨x, rfl⟩

private def dataSmallSectionsMap (D : BigZariskiSheafData.{u, v} B S hS)
    (T : BigZariskiOver B S hS)
    (X : SmallZariski B T.left.obj T.left.property) :
    (D.sheaf T).obj.obj
      (op ((smallZariskiToOpens B T.left.obj T.left.property).obj X)) ⟶
    (dataPresheaf B S hS D).obj
      (op ((smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom).obj X)) :=
  dataSectionMap B S hS D (smallStructureArrow B S hS T X) ⊤ _
    (top_le_preimage_smallStructureArrow B S hS T X)

private theorem dataSmallSectionsMap_isIso (D : BigZariskiSheafData.{u, v} B S hS)
    (T : BigZariskiOver B S hS)
    (X : SmallZariski B T.left.obj T.left.property) :
    IsIso (dataSmallSectionsMap B S hS D T X) := by
  have : IsOpenImmersion (B.inclusion.map (smallStructureArrow B S hS T X).left) :=
    X.property
  apply dataSectionMap_isIso
  ext x
  simp [Topology.IsOpenEmbedding.functor, IsOpenMap.functor, smallZariskiToOpens,
    smallStructureArrow]

private theorem dataSmallSectionsMap_naturality
    (D : BigZariskiSheafData.{u, v} B S hS)
    (T : BigZariskiOver B S hS)
    {X Y : SmallZariski B T.left.obj T.left.property} (k : X ⟶ Y) :
    (D.sheaf T).obj.map ((smallZariskiToOpens B T.left.obj
        T.left.property).map k).op ≫ dataSmallSectionsMap B S hS D T X =
      dataSmallSectionsMap B S hS D T Y ≫ (dataPresheaf B S hS D).map
        ((smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom).map k).op := by
  let j := smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom
  let E := smallZariskiToOpens B T.left.obj T.left.property
  have hc : j.map k ≫ smallStructureArrow B S hS T Y =
      smallStructureArrow B S hS T X :=
    Over.OverMorphism.ext k.hom.w
  have hX := top_le_preimage_smallStructureArrow B S hS T X
  have hY := top_le_preimage_smallStructureArrow B S hS T Y
  have hXY : ⊤ ≤ (Opens.map (B.inclusion.map
      (smallStructureArrow B S hS T X).left).base).obj (E.obj Y) :=
    fun x hx => (E.map k).le (hX hx)
  show (D.sheaf T).obj.map (E.map k).op ≫
    dataSectionMap B S hS D _ ⊤ (E.obj X) hX =
    dataSectionMap B S hS D _ ⊤ (E.obj Y) hY ≫ dataGlobalSectionsMap B S hS D (j.map k)
  rw [dataSectionMap_restrict B S hS D _ _ _ hXY hX, ← dataSectionMap_top]
  simpa only [hc] using (dataSectionMap_comp B S hS D (smallStructureArrow B S hS T Y)
    (j.map k) ⊤ ⊤ (E.obj Y) hY le_top (by simpa only [hc] using hXY)).symm

private def dataSmallSectionsIso (D : BigZariskiSheafData.{u, v} B S hS)
    (T : BigZariskiOver B S hS) :
    (smallZariskiToOpens B T.left.obj T.left.property).op ⋙ (D.sheaf T).obj ≅
      (smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom).op ⋙
        dataPresheaf B S hS D := by
  have := fun X => dataSmallSectionsMap_isIso B S hS D T X
  exact NatIso.ofComponents (fun X => asIso (dataSmallSectionsMap B S hS D T X.unop))
    (fun k => dataSmallSectionsMap_naturality B S hS D T k.unop)

private theorem dataPresheaf_small_isSheaf (D : BigZariskiSheafData.{u, v} B S hS)
    (T : BigZariskiOver B S hS) :
    Presieve.IsSheaf (SmallZariski.topology B T.left.obj T.left.property)
      ((smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom).op ⋙
        dataPresheaf B S hS D) :=
  Presieve.isSheaf_iso _ (dataSmallSectionsIso B S hS D T) <|
    (isSheaf_iff_isSheaf_of_type _ _).mp ((smallZariskiSheafEquiv B T.left.obj
      T.left.property).inverse.obj (D.sheaf T)).property

private theorem isSheafFor_bigCover
    (P : (BigZariskiOver B S hS)ᵒᵖ ⥤ Type (max u v))
    (H : ∀ T : BigZariskiOver B S hS,
      Presieve.IsSheaf (SmallZariski.topology B T.left.obj T.left.property)
        ((smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom).op ⋙ P))
    (T : BigZariskiOver B S hS) (E : PreZeroHypercover.{u + 1} T)
    (hE : BigZariskiOver.IsCovering B S hS ⟨T, E⟩) :
    Presieve.IsSheafFor P E.presieve₀ := by
  let j := smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom
  have hopen (i : E.I₀) : IsOpenImmersion (B.inclusion.map (E.f i).left) := by
    have hc : (E.map (BigZariskiOver.toScheme B S hS)).presieve₀ ∈
        Scheme.precoverage @IsOpenImmersion T.left.obj := hE.1
    exact ((Scheme.presieve₀_mem_precoverage_iff _).mp hc).2 i
  let Y (i : E.I₀) : SmallZariski B T.left.obj T.left.property :=
    ⟨Over.mk (E.f i).left, hopen i⟩
  let O := SmallZariski.final B T.left.obj T.left.property
  let q (i : E.I₀) : Y i ⟶ O := ObjectProperty.homMk (Over.homMk (E.f i).left)
  let E' : PreZeroHypercover.{u + 1} O := ⟨E.I₀, Y, q⟩
  have hE' : SmallZariski.IsCovering B T.left.obj T.left.property ⟨O, E'⟩ := hE
  have hp := (H T).isSheafFor_of_mem_precoverage
    ((SmallZariski.mem_precoverage_iff _ _ _).mpr ⟨E', rfl, hE'⟩)
  have : CategoryTheory.Limits.PreservesLimitsOfShape CategoryTheory.Limits.WalkingCospan
      (j ⋙ BigZariskiOver.toScheme B S hS) := by
    show CategoryTheory.Limits.PreservesLimitsOfShape CategoryTheory.Limits.WalkingCospan
      (SmallZariski.toScheme B T.left.obj T.left.property)
    infer_instance
  have : CategoryTheory.Limits.PreservesLimitsOfShape CategoryTheory.Limits.WalkingCospan j :=
    CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves j
      (BigZariskiOver.toScheme B S hS)
  have hp' := (Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks j P E'.presieve₀).mp hp
  rw [PreZeroHypercover.presieve₀, Presieve.map_ofArrows] at hp'
  let e : j.obj O ≅ T := Over.isoMk (Iso.refl _) (by simp [O, j,
    SmallZariski.final, smallZariskiToBigZariskiFunctor])
  have hp'' := (isSheafFor_postcomp_iso P (fun i => j.map (q i)) e).mp hp'
  let eY (i : E.I₀) : j.obj (Y i) ≅ E.X i :=
    Over.isoMk (Iso.refl _) (by simp [Y, j])
  have heq (i : E.I₀) : j.map (q i) ≫ e.hom = (eY i).hom ≫ E.f i := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, e, eY, q, Over.isoMk_hom_left, Iso.refl_hom]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  simp only [heq] at hp''
  exact (Presieve.isSheafFor_ofArrows_comp_iff E.f eY).mp hp''

private theorem isSheaf_of_small_restrictions
    (P : (BigZariskiOver B S hS)ᵒᵖ ⥤ Type (max u v))
    (H : ∀ T : BigZariskiOver B S hS,
      Presieve.IsSheaf (SmallZariski.topology B T.left.obj T.left.property)
        ((smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom).op ⋙ P)) :
    Presieve.IsSheaf (BigZariskiOver.topology B S hS) P := by
  rw [Precoverage.isSheaf_toGrothendieck_iff]
  intro X Y f R hR
  obtain ⟨E, rfl, hE⟩ := (BigZariskiOver.mem_precoverage_iff _ _ _).mp hR
  obtain ⟨Q, p, q, hpq, hQ⟩ := B.coverings_isSite.2.2
    ⟨X.left, E.map (Over.forget _)⟩ hE Y.left f.left
  let Z (i : E.I₀) : BigZariskiOver B S hS := Over.mk (q i ≫ Y.hom)
  let a (i : E.I₀) : Z i ⟶ E.X i := Over.homMk (p i) (by
    have hi := (hpq i).w
    change p i ≫ (E.f i).left = q i ≫ f.left at hi
    show p i ≫ (E.X i).hom = q i ≫ Y.hom
    rw [← Over.w (E.f i), ← Over.w f]
    exact (Category.assoc _ _ _).symm.trans ((hi =≫ X.hom).trans (Category.assoc _ _ _)))
  let b (i : E.I₀) : Z i ⟶ Y := Over.homMk (q i)
  have hp (i : E.I₀) : IsPullback (a i) (b i) (E.f i) f :=
    IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext (hpq i).w) (hpq i)
  let E' : PreZeroHypercover.{u + 1} Y := ⟨E.I₀, Z, b⟩
  have hE' : BigZariskiOver.IsCovering B S hS ⟨Y, E'⟩ := hQ
  have hsheaf := isSheafFor_bigCover B S hS P H Y E' hE'
  rw [Presieve.isSheafFor_iff_generate] at hsheaf
  change Presieve.IsSheafFor P (Sieve.ofArrows Z b).arrows at hsheaf
  rwa [Sieve.ofArrows_eq_pullback_of_isPullback E.f (fun i => (hp i).flip)] at hsheaf

private def dataSheaf (D : BigZariskiSheafData.{u, v} B S hS) :
    Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)) :=
  ⟨dataPresheaf B S hS D, (isSheaf_iff_isSheaf_of_type _ _).mpr
    (isSheaf_of_small_restrictions B S hS _ (dataPresheaf_small_isSheaf B S hS D))⟩

/-- A morphism of compatible data commutes with the section comparisons. -/
private theorem dataPushforwardApp_hom_naturality {D E : BigZariskiSheafData.{u, v} B S hS}
    (φ : D ⟶ E) {T T' : BigZariskiOver B S hS} (f : T' ⟶ T) (V : Opens T.left.obj.carrier) :
    (φ.app T).hom.app (op V) ≫ dataPushforwardApp B S hS E f V =
      dataPushforwardApp B S hS D f V ≫
        (φ.app T').hom.app (op ((Opens.map (B.inclusion.map f.left).base).obj V)) :=
  congrArg (fun a => a.hom.app (op V))
    ((TopCat.Sheaf.inverseImagePushforwardAdjunction
      (B.inclusion.map f.left).base).homEquiv_naturality_left_square
        (φ.app T) (E.pullback f) (D.pullback f) (φ.app T') (φ.naturality f))

/-- A morphism of compatible data commutes with the restriction maps on sections. -/
private theorem dataSectionMap_hom_naturality
    {D E : BigZariskiSheafData.{u, v} B S hS} (φ : D ⟶ E)
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    (U : Opens T'.left.obj.carrier) (V : Opens T.left.obj.carrier)
    (h : U ≤ (Opens.map (B.inclusion.map f.left).base).obj V) :
    (φ.app T).hom.app (op V) ≫ dataSectionMap B S hS E f U V h =
      dataSectionMap B S hS D f U V h ≫ (φ.app T').hom.app (op U) := by
  dsimp only [dataSectionMap]
  rw [← Category.assoc, dataPushforwardApp_hom_naturality, Category.assoc,
    ← (φ.app T').hom.naturality (homOfLE h).op, ← Category.assoc]

private def dataPresheafFunctor : BigZariskiSheafData.{u, v} B S hS ⥤
    (BigZariskiOver B S hS)ᵒᵖ ⥤ Type (max u v) where
  obj := dataPresheaf B S hS
  map φ := {
    app T := (φ.app T.unop).hom.app (op ⊤)
    naturality {T T'} f := by
      have h := dataSectionMap_hom_naturality B S hS φ f.unop ⊤ ⊤ le_top
      simp only [dataSectionMap_top] at h
      exact h.symm }
  map_id D := rfl
  map_comp φ ψ := rfl

private theorem dataPresheafFunctor_faithful : (dataPresheafFunctor.{u, v} B S hS).Faithful where
  map_injective {D E} {φ ψ} h := by
    apply BigZariskiSheafData.Hom.ext
    intro T
    apply Sheaf.hom_ext
    apply ((Functor.whiskeringLeft _ _ (Type (max u v))).obj
      (smallZariskiToOpens B T.left.obj T.left.property).op).map_injective
    apply NatTrans.ext
    funext X
    have := dataSmallSectionsMap_isIso B S hS E T X.unop
    apply (cancel_mono (dataSmallSectionsMap B S hS E T X.unop)).mp
    have key (χ : D ⟶ E) := dataSectionMap_hom_naturality B S hS χ
      (smallStructureArrow B S hS T X.unop) ⊤
        ((smallZariskiToOpens B T.left.obj T.left.property).obj X.unop)
        (top_le_preimage_smallStructureArrow B S hS T X.unop)
    have he := congrArg (fun a => a.app
      (op ((smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom).obj X.unop))) h
    exact (key φ).trans
      ((dataSmallSectionsMap B S hS D T X.unop ≫= he).trans (key ψ).symm)

private def restrictionGlobalSectionsIso
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v))) :
    dataPresheaf B S hS ((bigZariskiSheafRestriction B S hS).obj F) ≅ F.obj :=
  NatIso.ofComponents (fun T =>
    Equiv.toIso (bigZariskiSheafRestriction_sectionEquiv B S hS F T.unop)) (by
      intro T T' f
      ext s
      have hss : (bigZariskiSheafRestriction_sectionEquiv B S hS F T.unop).symm
          (bigZariskiSheafRestriction_sectionEquiv B S hS F T.unop s) = s :=
        Equiv.symm_apply_apply _ _
      have h := bigZariskiSheafRestriction_pullback_sections B S hS F f.unop
        (bigZariskiSheafRestriction_sectionEquiv B S hS F T.unop s)
      dsimp only at h
      rw [hss] at h
      exact h)

private def restrictionGlobalSectionsNatIso :
    bigZariskiSheafRestriction.{u, v} B S hS ⋙ dataPresheafFunctor B S hS ≅
      sheafToPresheaf _ _ :=
  NatIso.ofComponents (restrictionGlobalSectionsIso B S hS) (by
    intro F G φ
    apply NatTrans.ext
    funext T
    ext s
    exact bigZariskiSheafRestriction_sectionEquiv_naturality B S hS φ T.unop s)

private theorem bigZariskiSheafRestriction_full :
    (bigZariskiSheafRestriction.{u, v} B S hS).Full := by
  have := dataPresheafFunctor_faithful.{u, v} B S hS
  have := Functor.Full.of_iso (restrictionGlobalSectionsNatIso.{u, v} B S hS).symm
  exact Functor.Full.of_comp_faithful _ (dataPresheafFunctor.{u, v} B S hS)

private def dataRecoveryIso (D : BigZariskiSheafData.{u, v} B S hS)
    (T : BigZariskiOver B S hS) :
    canonicalSmallSheaf B S hS (dataSheaf B S hS D) T ≅ D.sheaf T :=
  (sheafToPresheaf _ _).preimageIso
    (((Functor.whiskeringLeft _ _ (Type (max u v))).obj
      (smallZariskiToOpens B T.left.obj T.left.property).op).preimageIso
        (canonicalSmallSiteIso B S hS (dataSheaf B S hS D) T ≪≫
          (dataSmallSectionsIso B S hS D T).symm))

private theorem dataRecoveryIso_app (D : BigZariskiSheafData.{u, v} B S hS)
    (T : BigZariskiOver B S hS)
    (X : SmallZariski B T.left.obj T.left.property) :
    (dataRecoveryIso B S hS D T).hom.hom.app
        (op ((smallZariskiToOpens B T.left.obj T.left.property).obj X)) ≫
      dataSmallSectionsMap B S hS D T X =
        (canonicalSmallSiteSectionsIso B S hS (dataSheaf B S hS D) T X).hom := by
  let W := (Functor.whiskeringLeft _ _ (Type (max u v))).obj
    (smallZariskiToOpens B T.left.obj T.left.property).op
  let e := canonicalSmallSiteIso B S hS (dataSheaf B S hS D) T ≪≫
    (dataSmallSectionsIso B S hS D T).symm
  have h₀ : (dataRecoveryIso B S hS D T).hom.hom = (W.preimageIso e).hom :=
    (sheafToPresheaf _ _).map_preimage _
  have h := W.map_preimage e.hom
  rw [← show (W.preimageIso e).hom = W.preimage e.hom from rfl, ← h₀] at h
  have h' := congrArg (fun a => a.app (op X)) h
  change (dataRecoveryIso B S hS D T).hom.hom.app
    (op ((smallZariskiToOpens B T.left.obj T.left.property).obj X)) = _ at h'
  have hA : e.hom.app (op X) =
      (canonicalSmallSiteSectionsIso B S hS (dataSheaf B S hS D) T X).hom ≫
        ((dataSmallSectionsIso B S hS D T).app (op X)).inv := rfl
  rw [h', hA]
  exact (Category.assoc _ _ _).trans
    ((_ ≫= ((dataSmallSectionsIso B S hS D T).app (op X)).inv_hom_id).trans (Category.comp_id _))

private def dataRepresentativeSectionsIso (D : BigZariskiSheafData.{u, v} B S hS)
    (T : BigZariskiOver B S hS) (U : Opens T.left.obj.carrier)
    (X : SmallZariski B T.left.obj T.left.property)
    (hX : (smallZariskiToOpens B T.left.obj T.left.property).obj X = U) :
    (D.sheaf T).obj.obj (op U) ≅ (dataPresheaf B S hS D).obj
      (op ((smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom).obj X)) := by
  have := dataSmallSectionsMap_isIso B S hS D T X
  exact (D.sheaf T).obj.mapIso (eqToIso hX).op ≪≫
    asIso (dataSmallSectionsMap B S hS D T X)

private theorem dataRecoveryIso_app_representative
    (D : BigZariskiSheafData.{u, v} B S hS)
    (T : BigZariskiOver B S hS) (U : Opens T.left.obj.carrier)
    (X : SmallZariski B T.left.obj T.left.property)
    (hX : (smallZariskiToOpens B T.left.obj T.left.property).obj X = U) :
    (dataRecoveryIso B S hS D T).hom.hom.app (op U) ≫
      (dataRepresentativeSectionsIso B S hS D T U X hX).hom =
        (canonicalSmallRepresentativeSectionsIso B S hS (dataSheaf B S hS D)
          T U X hX).hom := by
  subst U
  simpa [dataRepresentativeSectionsIso, canonicalSmallRepresentativeSectionsIso] using
    dataRecoveryIso_app B S hS D T X

private theorem dataRepresentativeSectionsIso_pullback
    (D : BigZariskiSheafData.{u, v} B S hS)
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    (U : Opens T'.left.obj.carrier) (V : Opens T.left.obj.carrier)
    (X : SmallZariski B T'.left.obj T'.left.property)
    (Y : SmallZariski B T.left.obj T.left.property)
    (hX : (smallZariskiToOpens B T'.left.obj T'.left.property).obj X = U)
    (hY : (smallZariskiToOpens B T.left.obj T.left.property).obj Y = V)
    (h : U ≤ (Opens.map (B.inclusion.map f.left).base).obj V) :
    dataSectionMap B S hS D f U V h ≫
      (dataRepresentativeSectionsIso B S hS D T' U X hX).hom =
    (dataRepresentativeSectionsIso B S hS D T V Y hY).hom ≫
      (dataPresheaf B S hS D).map
        (smallSiteArrow B S hS f X Y (by
          change _ ≤ (Opens.map (B.inclusion.map f.left).base).obj _
          rw [hX, hY]
          exact h)).op := by
  subst U
  subst V
  let i := smallStructureArrow B S hS T' X
  let j := smallStructureArrow B S hS T Y
  let a := smallSiteArrow B S hS f X Y h
  have ha : a ≫ j = i ≫ f :=
    Over.OverMorphism.ext (B.inclusion.map_injective (smallSiteArrow_fac B S hS f X Y h))
  let U := (smallZariskiToOpens B T'.left.obj T'.left.property).obj X
  let V := (smallZariskiToOpens B T.left.obj T.left.property).obj Y
  have hi := top_le_preimage_smallStructureArrow B S hS T' X
  have hj := top_le_preimage_smallStructureArrow B S hS T Y
  have hf : ⊤ ≤ (Opens.map (B.inclusion.map (i ≫ f).left).base).obj V :=
    fun x hx => h (hi hx)
  have h₁ := dataSectionMap_comp B S hS D f i ⊤ U V h hi hf
  have h₂ := dataSectionMap_comp B S hS D j a ⊤ ⊤ V hj le_top (by simpa only [ha] using hf)
  simp only [dataSectionMap_top, ha] at h₂
  simpa [dataRepresentativeSectionsIso, dataSmallSectionsMap, dataPresheaf] using
    h₁.trans h₂.symm

private theorem dataRecoveryIso_sections_naturality
    (D : BigZariskiSheafData.{u, v} B S hS)
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    (U : Opens T'.left.obj.carrier) (V : Opens T.left.obj.carrier)
    (h : U ≤ (Opens.map (B.inclusion.map f.left).base).obj V) :
    (dataRecoveryIso B S hS D T).hom.hom.app (op V) ≫ dataSectionMap B S hS D f U V h =
      dataSectionMap B S hS ((bigZariskiSheafRestriction B S hS).obj
        (dataSheaf B S hS D)) f U V h ≫ (dataRecoveryIso B S hS D T').hom.hom.app (op U) := by
  let F := dataSheaf B S hS D
  let X := smallOpenObject B S hS T' U
  let Y := smallOpenObject B S hS T V
  have hX := smallOpenObject_toOpens B S hS T' U
  have hY := smallOpenObject_toOpens B S hS T V
  have hXY : (smallZariskiToOpens B T'.left.obj T'.left.property).obj X ≤
      (Opens.map (B.inclusion.map f.left).base).obj
        ((smallZariskiToOpens B T.left.obj T.left.property).obj Y) := by
    dsimp only [X, Y]
    rwa [smallOpenObject_toOpens, smallOpenObject_toOpens]
  have hfam : dataSectionMap B S hS ((bigZariskiSheafRestriction B S hS).obj F) f U V h =
      canonicalSmallPairMap B S hS F f U V X Y hX hY hXY := by
    ext s
    show (TopCat.Sheaf.inverseImageSectionFamily (B.inclusion.map f.left).base _ _
      (TopCat.Sheaf.inverseImageSectionFamilyHom _ _ _
        (canonicalSmallPullbackFamily B S hS F f))).app
        U V h s = _
    exact TopCat.Sheaf.inverseImageSectionFamilyHom_sectionFamily _ _ _
      (canonicalSmallPullbackFamily B S hS F f) U V h s
  apply (cancel_mono (dataRepresentativeSectionsIso B S hS D T' U X hX).hom).mp
  have hd := dataRepresentativeSectionsIso_pullback B S hS D f U V X Y hX hY h
  have haX := dataRecoveryIso_app_representative B S hS D T' U X hX
  have haY := dataRecoveryIso_app_representative B S hS D T V Y hY
  show (_ ≫ _) ≫ (dataRepresentativeSectionsIso B S hS D T' U X hX).hom = _
  simp only [Category.assoc]
  rw [hd, reassoc_of% haY, hfam]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_
    (congrArg (fun k => canonicalSmallPairMap B S hS F f U V X Y hX hY hXY ≫ k) haX).symm
  dsimp only [F, canonicalSmallPairMap]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (fun k =>
    (canonicalSmallRepresentativeSectionsIso B S hS (dataSheaf B S hS D) T V Y hY).hom ≫ k) ?_
  exact ((Category.assoc _ _ _).trans
    ((congrArg (fun k => (dataSheaf B S hS D).obj.map
        (smallSiteArrow B S hS f X Y hXY).op ≫ k)
      (canonicalSmallRepresentativeSectionsIso B S hS
        (dataSheaf B S hS D) T' U X hX).inv_hom_id).trans (Category.comp_id _))).symm

private theorem dataRecoveryIso_naturality
    (D : BigZariskiSheafData.{u, v} B S hS)
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T) :
    (TopCat.Sheaf.inverseImage (B.inclusion.map f.left).base).map (dataRecoveryIso B S hS D T).hom ≫
      D.pullback f =
    ((bigZariskiSheafRestriction B S hS).obj (dataSheaf B S hS D)).pullback f ≫
      (dataRecoveryIso B S hS D T').hom := by
  let adj := TopCat.Sheaf.inverseImagePushforwardAdjunction.{u, v} (B.inclusion.map f.left).base
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  refine Eq.trans ?_ (adj.homEquiv_naturality_right _ _).symm
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  have h := dataRecoveryIso_sections_naturality B S hS D f
    ((Opens.map (B.inclusion.map f.left).base).obj V.unop) V.unop le_rfl
  change (dataRecoveryIso B S hS D T).hom.hom.app V ≫
      ((dataPushforwardMap B S hS D f).hom.app V ≫ (D.sheaf T').obj.map (𝟙 _)) =
    ((dataPushforwardMap B S hS ((bigZariskiSheafRestriction B S hS).obj
        (dataSheaf B S hS D)) f).hom.app V ≫
      (((bigZariskiSheafRestriction B S hS).obj (dataSheaf B S hS D)).sheaf T').obj.map
        (𝟙 _)) ≫ (dataRecoveryIso B S hS D T').hom.hom.app _ at h
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at h
  ext s
  exact congrArg (fun q => q s) h

private def dataIsoMk {D E : BigZariskiSheafData.{u, v} B S hS}
    (e : ∀ T : BigZariskiOver B S hS, D.sheaf T ≅ E.sheaf T)
    (he : ∀ {T T' : BigZariskiOver B S hS} (f : T' ⟶ T),
      (TopCat.Sheaf.inverseImage (B.inclusion.map f.left).base).map (e T).hom ≫ E.pullback f =
        D.pullback f ≫ (e T').hom) : D ≅ E where
  hom := ⟨fun T => (e T).hom, he⟩
  inv := ⟨fun T => (e T).inv, by
    intro T T' f
    apply (cancel_epi ((TopCat.Sheaf.inverseImage (B.inclusion.map f.left).base).map (e T).hom)).mp
    rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp, ← Category.assoc, he, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]⟩
  hom_inv_id := by apply BigZariskiSheafData.Hom.ext; intro T; exact (e T).hom_inv_id
  inv_hom_id := by apply BigZariskiSheafData.Hom.ext; intro T; exact (e T).inv_hom_id

private theorem bigZariskiSheafRestriction_essSurj :
    (bigZariskiSheafRestriction.{u, v} B S hS).EssSurj where
  mem_essImage D := ⟨dataSheaf B S hS D,
    ⟨dataIsoMk B S hS (dataRecoveryIso B S hS D) (dataRecoveryIso_naturality B S hS D)⟩⟩

/-- Restriction is fully faithful and every compatible system comes from a big-site sheaf. -/
public theorem bigZariskiSheafRestriction_isEquivalence :
    (bigZariskiSheafRestriction.{u, v} B S hS).IsEquivalence := by
  have := bigZariskiSheafRestriction_full.{u, v} B S hS
  have := bigZariskiSheafRestriction_faithful.{u, v} B S hS
  have := bigZariskiSheafRestriction_essSurj.{u, v} B S hS
  exact {}

/-- The canonical restriction functor is an equivalence of categories. -/
@[stacks 0213 "equivalence of categories"]
public noncomputable def characterizeSheafBigZariski :
    Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)) ≌
      BigZariskiSheafData.{u, v} B S hS :=
  @Functor.asEquivalence _ _ _ _ (bigZariskiSheafRestriction.{u, v} B S hS)
    (bigZariskiSheafRestriction_isEquivalence.{u, v} B S hS)

/-- The equivalence uses the canonical restriction functor, not an arbitrary
equivalent object assignment. -/
@[stacks 0213 "canonicality of the equivalence"]
public theorem characterizeSheafBigZariski_functor :
    (characterizeSheafBigZariski.{u, v} B S hS).functor =
      bigZariskiSheafRestriction.{u, v} B S hS := rfl

end AlgebraicGeometry
