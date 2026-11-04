module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.Topology.Category.TopCommRingCat

/-!
# Colimits of topological rings (Stacks 0B24)

Following the Stacks Project convention that "ring" means a commutative ring with `1`, the
category of topological rings is Mathlib's `TopCommRingCat` and the category of rings is
`CommRingCat`. The tag says that `TopCommRingCat` has all small colimits and that the
forgetful functor to `CommRingCat` preserves them.

Both follow from the forgetful functor *creating* colimits. Given `K : J ⥤ TopCommRingCat`
and a colimit cocone `c` for the underlying diagram of rings, the apex `c.pt` is topologized
by `TopCommRingCat.colimitRingTopology`, the supremum in the lattice `RingTopology c.pt` of
the ring topologies coinduced by the cocone maps `c.ι.app j`. Since `RingTopology.coinduced g`
is the finest ring topology making `g` continuous, and a ring topology makes every `c.ι.app j`
continuous exactly when it lies above every one of those coinduced topologies, this supremum
is the finest ring topology making all the cocone maps continuous — which is what a colimit
topology must be. (Mathlib orders topologies so that `≤` means "finer", hence `sSup` here and
`le_sSup` / `sSup_le` in the proofs.)

That the descent map out of the colimit is continuous is the one real verification: pulling
the topology of a competing cocone apex back along the descent ring homomorphism gives a ring
topology on `c.pt` making every cocone map continuous, so the colimit topology lies below it.

Preservation, part (2), goes the other way: any cocone in `CommRingCat` can be lifted to
`TopCommRingCat` by giving its apex the indiscrete topology `⊤`, into which every map is
continuous (`continuous_top`). This is exactly the source's observation that the forgetful
functor has a right adjoint given by the chaotic topology, hence preserves colimits.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace TopCommRingCat

section Colimit

variable {J : Type u} [SmallCategory J] (K : J ⥤ TopCommRingCat.{u})
  (c : Cocone (K ⋙ forget₂ TopCommRingCat CommRingCat))

/-- The colimit ring topology on the apex of a cocone of underlying rings: the supremum, in
the lattice of ring topologies, of the ring topologies coinduced by the cocone maps. It is
the finest ring topology making every cocone map continuous. -/
noncomputable def colimitRingTopology : RingTopology (c.pt : Type u) :=
  sSup (Set.range fun j : J =>
    @RingTopology.coinduced (K.obj j).α (c.pt : Type u) (K.obj j).isTopologicalSpace
      inferInstance (c.ι.app j))

/-- The apex of the colimit cocone: the colimit ring carrying `colimitRingTopology`. -/
noncomputable def colimitPt : TopCommRingCat.{u} :=
  @TopCommRingCat.of (c.pt : Type u) inferInstance
    (colimitRingTopology K c).toTopologicalSpace
    (colimitRingTopology K c).toIsTopologicalRing

/-- Each cocone map is continuous for the colimit ring topology: it is continuous for the
ring topology it coinduces, and the colimit topology lies above that one. -/
lemma continuous_ι_colimitRingTopology (j : J) :
    @Continuous (K.obj j).α (c.pt : Type u) (K.obj j).isTopologicalSpace
      (colimitRingTopology K c).toTopologicalSpace (c.ι.app j) := by
  have hle : (@RingTopology.coinduced (K.obj j).α (c.pt : Type u) (K.obj j).isTopologicalSpace
      inferInstance (c.ι.app j)) ≤ colimitRingTopology K c :=
    le_sSup (Set.mem_range_self j)
  exact continuous_le_rng hle (@RingTopology.coinduced_continuous (K.obj j).α _
    (K.obj j).isTopologicalSpace _ (c.ι.app j))

/-- The descent map to the apex of any cocone in `TopCommRingCat` is continuous. Pulling that
apex's topology back along the descent ring homomorphism is a ring topology on `c.pt` for
which every cocone map is continuous, so the colimit topology lies below it. -/
lemma continuous_desc_colimitRingTopology (hc : IsColimit c) (s : Cocone K) :
    @Continuous (c.pt : Type u) (s.pt).α
      (colimitRingTopology K c).toTopologicalSpace (s.pt).isTopologicalSpace
      (hc.desc ((forget₂ TopCommRingCat CommRingCat).mapCocone s)) := by
  let φ := hc.desc ((forget₂ TopCommRingCat CommRingCat).mapCocone s)
  let φ_hom : (c.pt : Type u) →+* (s.pt).α := ConcreteCategory.hom φ
  let τ_ts : TopologicalSpace (c.pt : Type u) := TopologicalSpace.induced φ_hom
      (s.pt).isTopologicalSpace
  have hind : @Topology.IsInducing _ _ τ_ts (s.pt).isTopologicalSpace φ_hom := ⟨rfl⟩
  have hτ_ring : @IsTopologicalRing (c.pt : Type u) τ_ts inferInstance :=
    { toIsTopologicalSemiring :=
        { toContinuousAdd := Topology.IsInducing.continuousAdd φ_hom hind,
          toContinuousMul := Topology.IsInducing.continuousMul φ_hom hind },
      toContinuousNeg := hind.continuousNeg (map_neg φ_hom) }
  let τ : RingTopology (c.pt : Type u) := ⟨τ_ts, hτ_ring⟩
  have hle : colimitRingTopology K c ≤ τ := by
    apply sSup_le
    rintro _ ⟨j, rfl⟩
    -- `sInf_le` wants continuity of the cocone map into `τ`; going through `change` and `rw`
    -- instead is not available: the coinduced-topology goal mentions `(K ⋙ forget₂ …).obj j`
    -- where the map is typed by `K.obj j`, and that is not type-correct at the `implicit`
    -- transparency level, so no rewrite fires on it.
    refine sInf_le (continuous_iff_coinduced_le.mp ?_)
    refine continuous_induced_rng.mpr ((s.ι.app j).2.congr fun x => ?_)
    exact (congrFun (congrArg DFunLike.coe (congrArg ConcreteCategory.hom
      (hc.fac ((forget₂ TopCommRingCat CommRingCat).mapCocone s) j))) x).symm
  exact continuous_le_dom (isOpen_implies_isOpen_iff.mp hle) continuous_induced_dom

/-- The cocone on `K` obtained by topologizing the apex of `c` with `colimitRingTopology`. -/
noncomputable def colimitCocone : Cocone K where
  pt := colimitPt K c
  ι :=
    { app := fun j => ⟨ConcreteCategory.hom (c.ι.app j), continuous_ι_colimitRingTopology K c j⟩
      naturality := by
        intro i j f
        ext x
        simp only [Functor.const_obj_map]
        have h := c.ι.naturality f
        simp only [Functor.const_obj_map] at h
        exact congrFun (congrArg DFunLike.coe (congrArg ConcreteCategory.hom h)) x }

/-- `TopCommRingCat.colimitCocone` is a colimit cocone whenever `c` is: the descent map is the
underlying ring homomorphism `hc.desc`, continuous by `continuous_desc_colimitRingTopology`,
and it is unique because `forget₂` is faithful. -/
noncomputable def colimitCoconeIsColimit (hc : IsColimit c) : IsColimit (colimitCocone K c) :=
  IsColimit.mk
    (fun s => ⟨ConcreteCategory.hom (hc.desc ((forget₂ TopCommRingCat CommRingCat).mapCocone s)),
              continuous_desc_colimitRingTopology K c hc s⟩)
    (by
      intro s j
      ext x
      simp only [colimitCocone]
      have hfac := hc.fac ((forget₂ TopCommRingCat CommRingCat).mapCocone s) j
      exact congrFun (congrArg DFunLike.coe (congrArg ConcreteCategory.hom hfac)) x)
    (by
      intro s m hm
      ext x
      have huniq := hc.uniq ((forget₂ TopCommRingCat CommRingCat).mapCocone s)
        (ConcreteCategory.ofHom m.val) (by
          intro j
          ext y
          exact congrFun (congrArg DFunLike.coe (congrArg Subtype.val (hm j))) y)
      exact congrFun (congrArg DFunLike.coe (congrArg ConcreteCategory.hom huniq)) x)

/-- Lift a cocone of underlying rings to `TopCommRingCat` by giving its apex the indiscrete
topology `⊤`: every map into an indiscrete space is continuous, so the cocone maps become
morphisms of topological rings. -/
noncomputable def indiscreteCocone (K' : J ⥤ TopCommRingCat.{u})
    (t : Cocone (K' ⋙ forget₂ TopCommRingCat CommRingCat)) : Cocone K' := by
  letI : TopologicalSpace (t.pt : Type u) := ⊤
  haveI : IsTopologicalRing (t.pt : Type u) :=
    { toIsTopologicalSemiring :=
        { toContinuousAdd := ⟨continuous_top⟩
          toContinuousMul := ⟨continuous_top⟩ }
      toContinuousNeg := ⟨continuous_top⟩ }
  exact
    { pt := TopCommRingCat.of (t.pt : Type u)
      ι :=
        { app := fun j => ⟨ConcreteCategory.hom (t.ι.app j), continuous_top⟩
          naturality := by
            intro i j f
            ext x
            simp only [Functor.const_obj_map]
            have h := t.ι.naturality f
            simp only [Functor.const_obj_map] at h
            exact congrFun (congrArg DFunLike.coe (congrArg ConcreteCategory.hom h)) x } }

end Colimit

/-- **Stacks 0B24**, part (1). The category of topological rings has all small colimits. -/
@[stacks 0B24 "part (1): existence of colimits"]
noncomputable instance hasColimits : HasColimits TopCommRingCat.{u} :=
  ⟨fun _ _ => ⟨fun K => HasColimit.mk
    ⟨colimitCocone K (colimit.cocone (K ⋙ forget₂ TopCommRingCat CommRingCat)),
      colimitCoconeIsColimit K _ (colimit.isColimit _)⟩⟩⟩

/-- **Stacks 0B24**, part (2). The forgetful functor from topological rings to rings preserves
all small colimits, by the indiscrete-topology lift `TopCommRingCat.indiscreteCocone`. -/
@[stacks 0B24 "part (2): commutes with forgetful to CommRing"]
noncomputable instance preservesColimits_forget₂CommRingCat :
    PreservesColimits (forget₂ TopCommRingCat.{u} CommRingCat.{u}) := by
  refine ⟨fun {J} _ => ⟨fun {K} => ⟨fun {c} hc => ⟨IsColimit.mk ?_ ?_ ?_⟩⟩⟩⟩
  · exact fun t => ConcreteCategory.ofHom (hc.desc (indiscreteCocone K t)).val
  · intro t j
    ext x
    exact congrFun
      (congrArg DFunLike.coe (congrArg Subtype.val (hc.fac (indiscreteCocone K t) j))) x
  · intro t m hm
    ext x
    have huniq := hc.uniq (indiscreteCocone K t) ⟨ConcreteCategory.hom m, continuous_top⟩
      fun j => by
        ext y
        exact congrFun (congrArg DFunLike.coe (congrArg ConcreteCategory.hom (hm j))) y
    exact congrFun (congrArg DFunLike.coe (congrArg Subtype.val huniq)) x

end TopCommRingCat
