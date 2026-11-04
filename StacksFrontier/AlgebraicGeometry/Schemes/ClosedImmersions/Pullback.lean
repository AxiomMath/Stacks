module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedSubspaceExistence
public import StacksFrontier.AlgebraicGeometry.Schemes.ClosedImmersions.FactorizationExistence
public import StacksFrontier.Topology.Sheaves.Modules.Generators.LocallyGeneratedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiOver

/-!
# Pulling back a closed subspace

Let `f : X ⟶ Y` be a morphism of locally ringed spaces and let `i : I ⟶ 𝒪_Y` be a monomorphism of
sheaves of modules exhibiting `I` as a locally generated sheaf of ideals. The inverse-image ideal
of `I` is the image of the canonical map `f^* I ⟶ 𝒪_Y`; it is again locally generated, and the
closed subspace it cuts out is the fibre product of the closed subspace of `I` with `X` over `Y`.

## Main definitions

* `pullbackIdeal f I i` is the inverse-image ideal, with inclusion `pullbackIdealInclusion`.
* `pullbackClosedSubspace f I i hI` is the closed subspace of `X` it cuts out.
* `restrictedMap f I i hI` is the induced morphism of closed subspaces.

## Main results

* `pullbackIdeal_locallyGenerated`: the inverse-image ideal is locally generated.
* `restrictedMap_commutes` and `restrictedMap_unique` specify the induced morphism.
* `restrictedMap_isPullback`: the restriction square is cartesian.

## Implementation notes

Everything rests on the factorization criterion of Tag 01HP, in the form
`Stacks.ClosedImmersion.factorsThrough_closedSubspace_iff`, used in both directions and on both
closed subspaces. The criterion is stated through `pullbackIdealMap`, so transporting it along a
composition `a ≫ f` is the technical content of this file:
`pullbackIdealMap_comp` reads `pullbackIdealMap (a ≫ f) I i` through the comparison isomorphism
`structurePullbackComp`, for which `pullbackUnitMap_comp` is the required compatibility with the
canonical maps to the structure sheaf. That compatibility is proved by transposing both sides
across `a^* ⊣ a_*`, where they become the structure-sheaf map of the composite; the transpose of
the canonical map `f^* 𝒪 ⟶ 𝒪` is Mathlib's
`SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`, so no transparency
option is needed anywhere here.

Both directions of the transport are then recorded.
`pullbackIdealMap_comp_eq_zero` says that a morphism killing the inverse-image ideal composes
with `f` to one killing `I`; it needs only that `f^* I` maps onto the inverse-image ideal.
`pullbackImageIdealMap_eq_zero` is the converse, and there the epimorphism
`f^* I ⟶ pullbackIdeal f I i` is used to cancel: `a^*` is a left adjoint, so it preserves that
epimorphism, and the vanishing may be tested after composing with it.

Local generation of the inverse-image ideal is Tag 01B3 — local generators for `f^* I`, via
`Stacks.SheafOfModules.modulePullback_nonempty_localGeneratorsData` — followed by
`Stacks.SheafOfModules.EpiMono.epi_over`, which says that an epimorphism of sheaves of modules
stays an epimorphism on the site over an object, since epimorphy is local surjectivity and local
surjectivity restricts.

## References

* [Stacks Project, Tag 01HQ](https://stacks.math.columbia.edu/tag/01HQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.ClosedImmersion

section Composition

variable {A B C : LocallyRingedSpace.{u}}

/-- The structure-sheaf map of a composite factors through the pushforward of the
structure-sheaf map of the second morphism. -/
private theorem structureSheafHom_comp (g : A ⟶ B) (f : B ⟶ C) :
    structureSheafHom (g ≫ f).toShHom =
      structureSheafHom f.toShHom ≫
        ((opensMap f.toShHom).sheafPushforwardContinuous RingCat.{u} _ _).map
          (structureSheafHom g.toShHom) := by
  ext U s
  rfl

/-- Pushing modules forward along a composite is pushing forward twice. -/
private noncomputable def structurePushforwardComp (g : A ⟶ B) (f : B ⟶ C) :
    modulePushforward (g ≫ f).toShHom ≅
      modulePushforward g.toShHom ⋙ modulePushforward f.toShHom :=
  SheafOfModules.pushforwardCongr (structureSheafHom_comp g f) ≪≫
    (SheafOfModules.pushforwardComp (structureSheafHom f.toShHom)
      (structureSheafHom g.toShHom)).symm

/-- Pulling modules back along a composite is pulling back twice, by uniqueness of left
adjoints. -/
private noncomputable def structurePullbackComp (g : A ⟶ B) (f : B ⟶ C) :
    modulePullback (g ≫ f).toShHom ≅
      modulePullback f.toShHom ⋙ modulePullback g.toShHom :=
  Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction (g ≫ f).toShHom)
    (((modulePullbackPushforwardAdjunction f.toShHom).comp
      (modulePullbackPushforwardAdjunction g.toShHom)).ofNatIsoRight
        (structurePushforwardComp g f).symm)

/-- The canonical map `f^* 𝒪_C ⟶ 𝒪_B`, the case `J = 𝒪` of `pullbackIdealMap`. -/
private noncomputable abbrev pullbackUnitMap (f : B ⟶ C) :
    (modulePullback f.toShHom).obj (SheafOfModules.unit (structureSheafRing C.toRingedSpace)) ⟶
      SheafOfModules.unit (structureSheafRing B.toRingedSpace) :=
  let : (SheafOfModules.pushforward (structureSheafHom f.toShHom)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f.toShHom
  SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f.toShHom)

/-- The adjoint transpose of `f^* 𝒪_C ⟶ 𝒪_B` is the structure-sheaf map `𝒪_C ⟶ f_* 𝒪_B`. -/
private theorem pullbackUnit_homEquiv (f : B ⟶ C) :
    (modulePullbackPushforwardAdjunction f.toShHom).homEquiv _ _ (pullbackUnitMap f) =
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toShHom) :=
  let : (SheafOfModules.pushforward (structureSheafHom f.toShHom)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f.toShHom
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    (structureSheafHom f.toShHom)

/-- `pullbackIdealMap` unfolded: the pullback of the ideal inclusion followed by the canonical
map `f^* 𝒪 ⟶ 𝒪`. Recorded as a lemma so that the two spellings can be exchanged by `rw`. -/
private theorem pullbackIdealMap_eq (f : B ⟶ C)
    (I : SheafOfModules.{u} (structureSheafRing C.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing C.toRingedSpace)) :
    pullbackIdealMap f I i = (modulePullback f.toShHom).map i ≫ pullbackUnitMap f :=
  rfl

/-- The comparison isomorphism for the pullback of a composite is compatible with the canonical
maps to the structure sheaf. Both sides are maps out of `(g ≫ f)^* 𝒪_C`, and their adjoint
transposes are both the structure-sheaf map of the composite, so they agree. -/
private theorem pullbackUnitMap_comp (g : A ⟶ B) (f : B ⟶ C) :
    (structurePullbackComp g f).hom.app (SheafOfModules.unit (structureSheafRing C.toRingedSpace)) ≫
        (modulePullback g.toShHom).map (pullbackUnitMap f) ≫ pullbackUnitMap g =
      pullbackUnitMap (g ≫ f) := by
  let _ : (SheafOfModules.pushforward (structureSheafHom (g ≫ f).toShHom)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint (g ≫ f).toShHom
  let _ : (SheafOfModules.pushforward (structureSheafHom f.toShHom)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f.toShHom
  let _ : (SheafOfModules.pushforward (structureSheafHom g.toShHom)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint g.toShHom
  -- the three transposes, recorded before abbreviating so that abbreviating rewrites them too
  have hg' := pullbackUnit_homEquiv g
  have hf' := pullbackUnit_homEquiv f
  have hgf' := pullbackUnit_homEquiv (g ≫ f)
  set adjg := modulePullbackPushforwardAdjunction g.toShHom
  set adjf := modulePullbackPushforwardAdjunction f.toShHom
  set adjgf := modulePullbackPushforwardAdjunction (g ≫ f).toShHom
  set e := structurePushforwardComp g f with he
  set adjseq := (adjf.comp adjg).ofNatIsoRight e.symm
  set qg : SheafOfModules.unit (structureSheafRing B.toRingedSpace) ⟶
      (modulePushforward g.toShHom).obj
        (SheafOfModules.unit (structureSheafRing A.toRingedSpace)) :=
    SheafOfModules.unitToPushforwardObjUnit (structureSheafHom g.toShHom)
  set qf : SheafOfModules.unit (structureSheafRing C.toRingedSpace) ⟶
      (modulePushforward f.toShHom).obj
        (SheafOfModules.unit (structureSheafRing B.toRingedSpace)) :=
    SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toShHom)
  set qgf : SheafOfModules.unit (structureSheafRing C.toRingedSpace) ⟶
      (modulePushforward (g ≫ f).toShHom).obj
        (SheafOfModules.unit (structureSheafRing A.toRingedSpace)) :=
    SheafOfModules.unitToPushforwardObjUnit (structureSheafHom (g ≫ f).toShHom)
  set z : ((modulePullback f.toShHom ⋙ modulePullback g.toShHom).obj
        (SheafOfModules.unit (structureSheafRing C.toRingedSpace))) ⟶
      SheafOfModules.unit (structureSheafRing A.toRingedSpace) :=
    (modulePullback g.toShHom).map (pullbackUnitMap f) ≫ pullbackUnitMap g with hz
  have hseq : adjseq.homEquiv _ _ z =
      (qf ≫ (modulePushforward f.toShHom).map qg) ≫
        e.symm.hom.app (SheafOfModules.unit (structureSheafRing A.toRingedSpace)) := by
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    simp only [Equiv.trans_apply, hz]
    rw [adjg.homEquiv_naturality_left, hg',
      Adjunction.homEquiv_naturality_right adjf (pullbackUnitMap f) qg, hf']
  have hq : qgf ≫ e.hom.app (SheafOfModules.unit (structureSheafRing A.toRingedSpace)) =
      qf ≫ (modulePushforward f.toShHom).map qg := by
    rw [he]
    ext U
    rfl
  apply (adjgf.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, structurePullbackComp,
    Adjunction.unit_leftAdjointUniq_hom_app adjgf adjseq, ← Adjunction.homEquiv_unit adjseq,
    ← Adjunction.homEquiv_unit adjgf, hseq, hgf', ← hq, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id]

/-- `pullbackIdealMap` for a composite, read through the comparison isomorphism. -/
private theorem pullbackComp_map_toUnit (g : A ⟶ B) (f : B ⟶ C)
    (I : SheafOfModules.{u} (structureSheafRing C.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing C.toRingedSpace)) :
    (structurePullbackComp g f).hom.app I ≫
        (modulePullback g.toShHom).map ((modulePullback f.toShHom).map i) ≫
        (modulePullback g.toShHom).map (pullbackUnitMap f) ≫ pullbackUnitMap g =
      (modulePullback (g ≫ f).toShHom).map i ≫ pullbackUnitMap (g ≫ f) := by
  rw [← pullbackUnitMap_comp, NatTrans.naturality_assoc, Functor.comp_map]

/-- **The composition law for `pullbackIdealMap`.** Pulling an ideal map back along a composite
is pulling it back in two steps, read through the comparison isomorphism for the pullback of a
composite. -/
private theorem pullbackIdealMap_comp (g : A ⟶ B) (f : B ⟶ C)
    (I : SheafOfModules.{u} (structureSheafRing C.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing C.toRingedSpace)) :
    pullbackIdealMap (g ≫ f) I i =
      (structurePullbackComp g f).hom.app I ≫
        (modulePullback g.toShHom).map ((modulePullback f.toShHom).map i) ≫
        (modulePullback g.toShHom).map (pullbackUnitMap f) ≫ pullbackUnitMap g :=
  (pullbackComp_map_toUnit g f I i).symm

end Composition

section Pullback

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)

/-- **Stacks Project, Tag 01HQ.** The inverse-image ideal of an ideal sheaf under a morphism of
locally ringed spaces: the image of the canonical map `f^* I ⟶ 𝒪_X`. -/
noncomputable abbrev pullbackIdeal (I : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) :
    SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
  Abelian.image (pullbackIdealMap f I i)

/-- The inclusion of the inverse-image ideal into the structure sheaf. -/
noncomputable abbrev pullbackIdealInclusion
    (I : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) :
    pullbackIdeal f I i ⟶ SheafOfModules.unit (structureSheafRing X.toRingedSpace) :=
  Abelian.image.ι (pullbackIdealMap f I i)

/-- **Stacks Project, Tag 01HQ.** The inverse-image ideal of a locally generated ideal sheaf is
locally generated. Tag 01B3 gives local generators for the pullback `f^* I`, and the inverse-image
ideal is a quotient of `f^* I`, so the images of those generators generate it. -/
@[stacks 01HQ "local generation"]
theorem pullbackIdeal_locallyGenerated (I : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing Y.toRingedSpace))
    (hI : Nonempty (SheafOfModules.LocalGeneratorsData.{u} I)) :
    Nonempty (SheafOfModules.LocalGeneratorsData.{u} (pullbackIdeal f I i)) := by
  obtain ⟨q⟩ := Stacks.SheafOfModules.modulePullback_nonempty_localGeneratorsData
    f.toShHom I hI
  refine ⟨{ I := q.I, X := q.X, coversTop := q.coversTop, generators := fun a => ?_ }⟩
  have : Epi ((Abelian.factorThruImage (pullbackIdealMap f I i)).over (q.X a)) :=
    Stacks.SheafOfModules.EpiMono.epi_over _ (q.X a)
  exact (q.generators a).ofEpi ((Abelian.factorThruImage (pullbackIdealMap f I i)).over (q.X a))

/-- The closed subspace of `X` cut out by the inverse-image ideal. A reducible spelling of
`closedSubspace X (pullbackIdeal f I i) (pullbackIdealInclusion f I i) _`. -/
noncomputable abbrev pullbackClosedSubspace
    (I : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing Y.toRingedSpace))
    (hI : Nonempty (SheafOfModules.LocalGeneratorsData.{u} I)) :
    ClosedSubspaceData X (pullbackIdeal f I i) (pullbackIdealInclusion f I i) :=
  closedSubspace X (pullbackIdeal f I i) (pullbackIdealInclusion f I i)
    (pullbackIdeal_locallyGenerated f I i hI)

/-- Pulling back the image projection and composing with the inclusion's canonical map is pulling
back `i` and the canonical map of `f` in two steps. -/
private theorem map_factorThruImage_comp_pullbackIdealMap {T : LocallyRingedSpace.{u}}
    (I : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) (a : T ⟶ X) :
    (modulePullback a.toShHom).map (Abelian.factorThruImage (pullbackIdealMap f I i)) ≫
        pullbackIdealMap a (pullbackIdeal f I i) (pullbackIdealInclusion f I i) =
      (modulePullback a.toShHom).map ((modulePullback f.toShHom).map i) ≫
        (modulePullback a.toShHom).map (pullbackUnitMap f) ≫ pullbackUnitMap a := by
  rw [pullbackIdealMap_eq a, ← Category.assoc, ← Functor.map_comp, Abelian.image.fac,
    pullbackIdealMap_eq f, Functor.map_comp, Category.assoc]

/-- The vanishing criterion transported to the inverse-image ideal: if `a ≫ f` kills `I`, then
`a` kills the inverse-image ideal. The image projection `f^* I ⟶ pullbackIdeal f I i` is an
epimorphism and `a^*` preserves epimorphisms, so the vanishing may be tested after composing
with it, where it is the hypothesis read through the composition law. -/
private theorem pullbackImageIdealMap_eq_zero {T : LocallyRingedSpace.{u}}
    (I : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing Y.toRingedSpace))
    (a : T ⟶ X) (hzero : pullbackIdealMap (a ≫ f) I i = 0) :
    pullbackIdealMap a (pullbackIdeal f I i) (pullbackIdealInclusion f I i) = 0 := by
  have : PreservesColimitsOfShape WalkingSpan (modulePullback a.toShHom) :=
    (Adjunction.leftAdjoint_preservesColimits
      (modulePullbackPushforwardAdjunction a.toShHom)).preservesColimitsOfShape
  have hepi : Epi ((structurePullbackComp a f).hom.app I ≫
      (modulePullback a.toShHom).map (Abelian.factorThruImage (pullbackIdealMap f I i))) :=
    epi_comp _ _
  refine (cancel_epi ((structurePullbackComp a f).hom.app I ≫
    (modulePullback a.toShHom).map
      (Abelian.factorThruImage (pullbackIdealMap f I i)))).1 ?_
  rw [comp_zero, ← hzero, pullbackIdealMap_comp, Category.assoc,
    map_factorThruImage_comp_pullbackIdealMap]

/-- The converse of `pullbackImageIdealMap_eq_zero`: a morphism killing the inverse-image ideal
composes with `f` to a morphism killing `I`. The inverse-image ideal receives `f^* I`, so the
composite factors through it. -/
private theorem pullbackIdealMap_comp_eq_zero {T : LocallyRingedSpace.{u}}
    (I : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) (a : T ⟶ X)
    (ha : pullbackIdealMap a (pullbackIdeal f I i) (pullbackIdealInclusion f I i) = 0) :
    pullbackIdealMap (a ≫ f) I i = 0 := by
  rw [pullbackIdealMap_comp, ← map_factorThruImage_comp_pullbackIdealMap f I i a, ha,
    comp_zero, comp_zero]

/-- A morphism from the inverse-image closed subspace to the original one exists. The inclusion
of the inverse-image closed subspace kills the inverse-image ideal, hence its composite with `f`
kills `I`, and the factorization criterion produces the morphism. -/
theorem exists_restrictedMap (I : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) [Mono i]
    (hI : Nonempty (SheafOfModules.LocalGeneratorsData.{u} I)) :
    ∃ g : (pullbackClosedSubspace f I i hI).space ⟶ (closedSubspace Y I i hI).space,
      g ≫ (closedSubspace Y I i hI).inclusion =
        (pullbackClosedSubspace f I i hI).inclusion ≫ f :=
  (factorsThrough_closedSubspace_iff (closedSubspace Y I i hI)
    ((pullbackClosedSubspace f I i hI).inclusion ≫ f)).2
    (pullbackIdealMap_comp_eq_zero f I i (pullbackClosedSubspace f I i hI).inclusion
      ((factorsThrough_closedSubspace_iff (pullbackClosedSubspace f I i hI)
        (pullbackClosedSubspace f I i hI).inclusion).mp ⟨𝟙 _, Category.id_comp _⟩))

/-- **Stacks Project, Tag 01HQ.** The morphism of closed subspaces induced by `f`. -/
@[stacks 01HQ "restricted map"]
noncomputable def restrictedMap (I : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) [Mono i]
    (hI : Nonempty (SheafOfModules.LocalGeneratorsData.{u} I)) :
    (pullbackClosedSubspace f I i hI).space ⟶ (closedSubspace Y I i hI).space :=
  Classical.choose (exists_restrictedMap f I i hI)

/-- **Stacks Project, Tag 01HQ.** The induced map commutes with the inclusions into the ambient
spaces. -/
@[stacks 01HQ "commutative square"]
theorem restrictedMap_commutes (I : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) [Mono i]
    (hI : Nonempty (SheafOfModules.LocalGeneratorsData.{u} I)) :
    restrictedMap f I i hI ≫ (closedSubspace Y I i hI).inclusion =
      (pullbackClosedSubspace f I i hI).inclusion ≫ f :=
  Classical.choose_spec (exists_restrictedMap f I i hI)

/-- **Stacks Project, Tag 01HQ.** A morphism between the associated closed subspaces over `f` is
the induced one. -/
@[stacks 01HQ "uniqueness"]
theorem restrictedMap_unique (I : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) [Mono i]
    (hI : Nonempty (SheafOfModules.LocalGeneratorsData.{u} I))
    (g : (pullbackClosedSubspace f I i hI).space ⟶ (closedSubspace Y I i hI).space)
    (hg : g ≫ (closedSubspace Y I i hI).inclusion =
      (pullbackClosedSubspace f I i hI).inclusion ≫ f) :
    g = restrictedMap f I i hI :=
  congrArg Subtype.val
    ((subsingleton_factorizations_closedSubspace I i (closedSubspace Y I i hI)
      ((pullbackClosedSubspace f I i hI).inclusion ≫ f)).elim
      ⟨g, hg⟩ ⟨restrictedMap f I i hI, restrictedMap_commutes f I i hI⟩)

/-- **Stacks Project, Tag 01HQ.** The restriction square is a fibre square of locally ringed
spaces. -/
@[stacks 01HQ "fibre square"]
theorem restrictedMap_isPullback (I : SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
    (i : I ⟶ SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) [Mono i]
    (hI : Nonempty (SheafOfModules.LocalGeneratorsData.{u} I)) :
    IsPullback (pullbackClosedSubspace f I i hI).inclusion (restrictedMap f I i hI) f
      (closedSubspace Y I i hI).inclusion := by
  have hexist (s : PullbackCone f (closedSubspace Y I i hI).inclusion) :
      ∃ l : s.pt ⟶ (pullbackClosedSubspace f I i hI).space,
        l ≫ (pullbackClosedSubspace f I i hI).inclusion = s.fst := by
    have hzero : pullbackIdealMap (s.fst ≫ f) I i = 0 := by
      rw [s.condition]
      exact (factorsThrough_closedSubspace_iff (closedSubspace Y I i hI)
        (s.snd ≫ (closedSubspace Y I i hI).inclusion)).mp ⟨s.snd, rfl⟩
    exact (factorsThrough_closedSubspace_iff (pullbackClosedSubspace f I i hI) s.fst).2
      (pullbackImageIdealMap_eq_zero f I i s.fst hzero)
  refine IsPullback.of_isLimit (c := PullbackCone.mk
    (pullbackClosedSubspace f I i hI).inclusion (restrictedMap f I i hI)
    (restrictedMap_commutes f I i hI).symm)
    (PullbackCone.IsLimit.mk (restrictedMap_commutes f I i hI).symm
      (fun s => Classical.choose (hexist s))
      (fun s => Classical.choose_spec (hexist s)) (fun s => ?_) (fun s m hm₁ _ => ?_))
  · refine congrArg Subtype.val
      ((subsingleton_factorizations_closedSubspace I i (closedSubspace Y I i hI)
        (s.fst ≫ f)).elim ⟨Classical.choose (hexist s) ≫ restrictedMap f I i hI, ?_⟩
        ⟨s.snd, s.condition.symm⟩)
    rw [Category.assoc, restrictedMap_commutes, ← Category.assoc,
      Classical.choose_spec (hexist s)]
  · exact congrArg Subtype.val
      ((subsingleton_factorizations_closedSubspace (pullbackIdeal f I i)
        (pullbackIdealInclusion f I i) (pullbackClosedSubspace f I i hI) s.fst).elim
        ⟨m, hm₁⟩ ⟨Classical.choose (hexist s), Classical.choose_spec (hexist s)⟩)

end Pullback


end Stacks.ClosedImmersion

end
