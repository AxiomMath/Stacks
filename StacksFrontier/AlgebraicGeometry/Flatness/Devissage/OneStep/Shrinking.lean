module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.FiniteTilde
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteOverSmoothFactorization
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.FiniteSingletonFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherentFrom
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Restriction

/-!
# Standard shrinkings of a one-step dévissage

A one-step dévissage of `F/X/S` at a point `x` can always be shrunk: replacing the four affine
schemes by principal open neighbourhoods of the four distinguished points again produces a
one-step dévissage at `x`. Three such shrinkings are produced here. The first takes a prescribed
principal open neighbourhood `S'` of `f x` in the base and restricts everything to the inverse
image of `S'`. The second starts from a prescribed principal open neighbourhood `W` of the
distinguished point of the smooth scheme and produces a shrinking whose smooth open is exactly
`W ⊓ g ⁻¹ᵁ S'`. The third places the open on the source inside an arbitrary neighbourhood of `x`.

## Main definitions

* `AlgebraicGeometry.standardShrinkingOfOpens`: the standard shrinking assembled from four
  compatible principal opens of the four schemes of a one-step dévissage.

## Main results

* `AlgebraicGeometry.exists_standardShrinking_base`: restricting to the inverse images of a
  principal open neighbourhood of `f x` is a standard shrinking.
* `AlgebraicGeometry.exists_standardShrinking_smooth`: a standard shrinking can be chosen whose
  smooth open is a prescribed principal open neighbourhood of `y`, cut down to the new base.
* `AlgebraicGeometry.exists_standardShrinking_source`: a standard shrinking can be chosen whose
  source open lies inside a prescribed neighbourhood of `x`.

## Implementation notes

The four opens of a shrinking are produced together by `standardShrinkingOfOpens`, which takes
them as data subject to the compatibilities a shrinking requires and assembles the restricted
dévissage. Two of its fields carry the mathematical content. That the restricted fibre
dimensions are unchanged comes from two separate transport arguments: the support of the fibre
module is cut down along an open embedding, and the fibres of the smooth morphism are cut down
to nonempty opens, which does not change the dimension of an irreducible space. That the
restricted residue-field extension is still purely transcendental comes from transporting pure
transcendence along the pair of residue-field isomorphisms induced by the two open immersions.

The hypotheses of `standardShrinkingOfOpens` are stated as equalities of opens with principal
opens rather than as existence statements, because the resulting shrinking has to record the
defining global sections. Surjectivity of the restricted smooth morphism is a hypothesis rather
than a consequence; in the second and third results it is arranged by shrinking the base to a
principal open inside the image of the prescribed open of the smooth scheme, which is open
because a smooth morphism is open.

A point of an open `U` of a scheme is written as a point of the scheme `U.toScheme` throughout,
rather than as a point of the subset `U`, and is mapped into the ambient scheme by the open
immersion `U.ι` rather than by the subtype coercion. `resLE_apply_eq_iff` is
`AlgebraicGeometry.Scheme.Hom.coe_resLE_apply` in that convention.

## References

* [Stacks Project, Tag 05HA](https://stacks.math.columbia.edu/tag/05HA)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry

/-! ### Topological dimension along an open embedding -/

/-- If a space `B` has its dimension at the image of a point `a` under an open embedding equal to
its total dimension, then an open subspace realised by that embedding has the same dimension. -/
private lemma topologicalKrullDim_eq_of_isOpenEmbedding {A : Type v} {B : Type w}
    [TopologicalSpace A] [TopologicalSpace B] {j : A → B} (hj : Topology.IsOpenEmbedding j)
    (a : A) (hd : topologicalKrullDimAt B (j a) = topologicalKrullDim B) :
    topologicalKrullDim A = topologicalKrullDim B :=
  le_antisymm hj.isEmbedding.isInducing.topologicalKrullDim_le
    ((hd.symm.trans (hj.topologicalKrullDimAt_eq a)).le.trans
      ((topologicalKrullDimAt_isLeast A a).2
        ⟨Set.univ, Set.mem_univ _, isOpen_univ,
          (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ A).isHomeomorph).symm⟩))

/-- In the situation of `topologicalKrullDim_eq_of_isOpenEmbedding` the maximality of the local
dimension is inherited by the open subspace. -/
private lemma topologicalKrullDimAt_eq_of_isOpenEmbedding {A : Type v} {B : Type w}
    [TopologicalSpace A] [TopologicalSpace B] {j : A → B} (hj : Topology.IsOpenEmbedding j)
    (a : A) (hd : topologicalKrullDimAt B (j a) = topologicalKrullDim B) :
    topologicalKrullDimAt A a = topologicalKrullDim A :=
  (hj.topologicalKrullDimAt_eq a).symm.trans
    (hd.trans (topologicalKrullDim_eq_of_isOpenEmbedding hj a hd).symm)

/-! ### Restriction of a morphism and of a module to opens -/

/-- Points of an open subscheme are determined by their images in the ambient scheme. -/
lemma ι_eq_iff {X : Scheme.{u}} {U : X.Opens} {p q : U.toScheme} :
    U.ι p = U.ι q ↔ p = q :=
  ⟨fun h => U.ι.isOpenEmbedding.injective h, fun h => h ▸ rfl⟩

/-- A point of an open subscheme lies over a prescribed point of an open of the target exactly
when it does so after mapping both into the ambient schemes. -/
lemma resLE_apply_eq_iff {X S : Scheme.{u}} (f : X ⟶ S) {V : S.Opens} {U : X.Opens}
    (hUV : U ≤ f ⁻¹ᵁ V) (p : U.toScheme) (s : V.toScheme) :
    f.resLE V U hUV p = s ↔ f (U.ι p) = V.ι s := by
  rw [← show V.ι (f.resLE V U hUV p) = f (U.ι p) from Scheme.Hom.coe_resLE_apply f hUV p]
  exact ι_eq_iff.symm

/-- The support of the restriction of a finite-type module along an open immersion is the inverse
image of its support.

`AlgebraicGeometry.supp_restrict` is the special case of the inclusion of an open; this is the
form with an arbitrary open immersion. -/
lemma supp_restrict' {X Z : Scheme.{u}} (j : Z ⟶ X) [IsOpenImmersion j] (F : X.Modules)
    [F.IsFiniteType] :
    SheafOfModules.supp (F.restrict j) = j ⁻¹' SheafOfModules.supp F := by
  rw [SheafOfModules.supp_eq_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback j).app F), Stacks.Modules.supp_pullback]

/-- The inverse image along an open immersion of a direct image is the direct image along the
induced morphism of opens. This is the object-level form of
`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`, with the restriction
functors replaced by inverse images and the restricted morphism written as a `resLE`. -/
def pullbackPushforwardResLEIso {X Z : Scheme.{u}} (i : Z ⟶ X) (G : Z.Modules)
    (X' : X.Opens) (Z' : Z.Opens) (hZ : Z' = i ⁻¹ᵁ X') :
    (Scheme.Modules.pullback X'.ι).obj ((Scheme.Modules.pushforward i).obj G) ≅
      (Scheme.Modules.pushforward (i.resLE X' Z' hZ.le)).obj (G.restrict Z'.ι) := by
  subst hZ
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact ((Scheme.Modules.restrictFunctorIsoPullback X'.ι).app _).symm ≪≫
    (Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso i X').app G

/-- A morphism of schemes and its restriction to an open of the target and the full inverse image
of that open form a cartesian square with the two open immersions. -/
lemma isPullback_ι_resLE {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (U : X.Opens)
    (hU : U = f ⁻¹ᵁ V) :
    IsPullback U.ι (f.resLE V U hU.le) f V.ι := by
  subst hU
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using (isPullback_morphismRestrict f V).flip

/-! ### Transport of the fibre dimension -/

/-- Restricting the source and the target of `f` to opens containing `x` and its image changes
neither the dimension of the support of the fibre module nor the maximality of its local
dimension at `x`. -/
lemma topologicalKrullDim_supp_resLE {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    [F.IsFiniteType] (V : S.Opens) (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
    [(F.restrict U.ι).IsFiniteType] (x : X) (hx : x ∈ U)
    (hm : f.asFiber x ∈ SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
    (hd : topologicalKrullDimAt
        (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
        ⟨f.asFiber x, hm⟩ =
      topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)))
    (hm' : (f.resLE V U hUV).asFiber ⟨x, hx⟩ ∈ SheafOfModules.supp
      ((Scheme.Modules.pullback
        ((f.resLE V U hUV).fiberι (f.resLE V U hUV ⟨x, hx⟩))).obj (F.restrict U.ι))) :
    topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback
          ((f.resLE V U hUV).fiberι (f.resLE V U hUV ⟨x, hx⟩))).obj (F.restrict U.ι))) =
        topologicalKrullDim
          (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)) ∧
      topologicalKrullDimAt (SheafOfModules.supp ((Scheme.Modules.pullback
          ((f.resLE V U hUV).fiberι (f.resLE V U hUV ⟨x, hx⟩))).obj (F.restrict U.ι)))
          ⟨(f.resLE V U hUV).asFiber ⟨x, hx⟩, hm'⟩ =
        topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback
          ((f.resLE V U hUV).fiberι (f.resLE V U hUV ⟨x, hx⟩))).obj (F.restrict U.ι))) := by
  have hs : V.ι (f.resLE V U hUV ⟨x, hx⟩) = f x := Scheme.Hom.coe_resLE_apply f hUV ⟨x, hx⟩
  let P : Set X := {p | f p = f x ∧ p ∈ SheafOfModules.supp F}
  let e := fiberSupportHomeo f F (f x)
  let e' := (fiberSupportHomeo (f.resLE V U hUV) (F.restrict U.ι)
      (f.resLE V U hUV ⟨x, hx⟩)).trans
    (restrictedSupportHomeo f F V U hUV (f.resLE V U hUV ⟨x, hx⟩))
  let e'' : {p : U.toScheme // f (U.ι p) = V.ι (f.resLE V U hUV ⟨x, hx⟩) ∧
      U.ι p ∈ SheafOfModules.supp F} ≃ₜ (U.ι ⁻¹' P) :=
    Homeomorph.setCongr <| by
      ext p
      show (f (U.ι p) = V.ι (f.resLE V U hUV ⟨x, hx⟩) ∧ U.ι p ∈ SheafOfModules.supp F) ↔
        (f (U.ι p) = f x ∧ U.ι p ∈ SheafOfModules.supp F)
      rw [hs]
  let j := e.symm ∘ P.restrictPreimage U.ι ∘ e'' ∘ e'
  have hj : Topology.IsOpenEmbedding j :=
    e.symm.isOpenEmbedding.comp ((U.ι.isOpenEmbedding.restrictPreimage P).comp
      (e''.isOpenEmbedding.comp e'.isOpenEmbedding))
  have hpoint : j ⟨(f.resLE V U hUV).asFiber ⟨x, hx⟩, hm'⟩ = ⟨f.asFiber x, hm⟩ := by
    apply Subtype.ext
    apply (f.fiberι (f x)).isEmbedding.injective
    have hfi := Scheme.Hom.fiberι_asFiber (f.resLE V U hUV) ⟨x, hx⟩
    show f.fiberι (f x) ((f.fiberHomeo (f x)).symm _) = f.fiberι (f x) (f.asFiber x)
    rw [Scheme.Hom.fiberι_fiberHomeo_symm, Scheme.Hom.fiberι_asFiber]
    show U.ι ((f.resLE V U hUV).fiberι (f.resLE V U hUV ⟨x, hx⟩)
      ((f.resLE V U hUV).asFiber ⟨x, hx⟩)) = x
    rw [hfi]
    rfl
  have hdj : topologicalKrullDimAt
        (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
        (j ⟨(f.resLE V U hUV).asFiber ⟨x, hx⟩, hm'⟩) =
      topologicalKrullDim
        (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)) := by
    rwa [hpoint]
  exact ⟨topologicalKrullDim_eq_of_isOpenEmbedding hj _ hdj,
    topologicalKrullDimAt_eq_of_isOpenEmbedding hj _ hdj⟩

/-! ### Transport of the fibres of the smooth morphism -/

/-- Restricting a morphism with geometrically irreducible fibres to opens does not change the
dimension of a fibre, as long as the restriction is still surjective: the restricted fibre is a
nonempty open subspace of the original one. -/
lemma topologicalKrullDim_fiber_resLE {X S : Scheme.{u}} (g : X ⟶ S)
    [LocallyOfFiniteType g] [GeometricallyIrreducible g] (V : S.Opens) (U : X.Opens)
    (hUV : U ≤ g ⁻¹ᵁ V) [Surjective (g.resLE V U hUV)] (s : V.toScheme) :
    topologicalKrullDim ((g.resLE V U hUV).fiber s) =
      topologicalKrullDim (g.fiber (V.ι s)) := by
  have : LocallyOfFiniteType (g.fiberToSpecResidueField (V.ι s)) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _))
  let e := restrictedFiberHomeo g V U hUV s
  have : Nonempty ((g.resLE V U hUV).fiber s) := by
    rw [((g.resLE V U hUV).fiberHomeo s).nonempty_congr]
    obtain ⟨p, hp⟩ := (g.resLE V U hUV).surjective s
    exact ⟨p, hp⟩
  refine (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).trans
    (topologicalKrullDim_eq_of_isOpen (S.residueField (V.ι s)) (g.fiber (V.ι s))
      (g.fiberToSpecResidueField (V.ι s)) (g.fiberι (V.ι s) ⁻¹' (U : Set X))
      (U.isOpen.preimage (g.fiberι (V.ι s)).continuous) ?_).symm
  exact Set.nonempty_coe_sort.mp (e.nonempty_congr.mp inferInstance)

/-! ### Transport of the residue-field extension and of geometric irreducibility -/

/-- Pure transcendence of the residue field extension at a point survives restriction of the
source and the target to opens. -/
lemma purelyTranscendental_resLE {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (U : X.Opens) (hUV : U ≤ f ⁻¹ᵁ V) (x : U.toScheme) (s : S) (hs : f (U.ι x) = s)
    (s' : V.toScheme) (hs' : f.resLE V U hUV x = s')
    (H : letI := ((S.residueFieldCongr hs).inv ≫ f.residueFieldMap (U.ι x)).hom.toAlgebra
      PurelyTranscendental (S.residueField s) (X.residueField (U.ι x))) :
    letI := ((V.toScheme.residueFieldCongr hs').inv ≫
      (f.resLE V U hUV).residueFieldMap x).hom.toAlgebra
    PurelyTranscendental (V.toScheme.residueField s') (U.toScheme.residueField x) := by
  subst hs
  subst hs'
  let f' := f.resLE V U hUV
  let _ := (f.residueFieldMap (U.ι x)).hom.toAlgebra
  let _ := (f'.residueFieldMap x).hom.toAlgebra
  have hH : PurelyTranscendental (S.residueField (f (U.ι x))) (X.residueField (U.ι x)) := H
  show PurelyTranscendental (V.toScheme.residueField (f' x)) (U.toScheme.residueField x)
  have hfx : V.ι (f' x) = f (U.ι x) := Scheme.Hom.coe_resLE_apply f hUV x
  let e : S.residueField (f (U.ι x)) ≅ V.toScheme.residueField (f' x) :=
    (S.residueFieldCongr hfx).symm ≪≫ asIso (V.ι.residueFieldMap (f' x))
  let E : X.residueField (U.ι x) ≅ U.toScheme.residueField x := asIso (U.ι.residueFieldMap x)
  have h : V.ι.residueFieldMap (f' x) ≫ f'.residueFieldMap x =
      (S.residueFieldCongr hfx).hom ≫
        f.residueFieldMap (U.ι x) ≫ U.ι.residueFieldMap x := by
    have h₀ := Scheme.Hom.residueFieldMap_congr (Scheme.Hom.resLE_comp_ι f hUV) x
    rwa [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp] at h₀
  have he : e.hom = (S.residueFieldCongr hfx).inv ≫
    V.ι.residueFieldMap (f' x) := rfl
  have h' : e.hom ≫ f'.residueFieldMap x = f.residueFieldMap (U.ι x) ≫ E.hom := by
    rw [he, Category.assoc, h, Iso.inv_hom_id_assoc]
    rfl
  refine Stacks.Flatness.purelyTranscendental_of_ringEquiv e.commRingCatIsoToRingEquiv.symm
    E.commRingCatIsoToRingEquiv (fun a => ?_) hH
  have hfun := congrArg (fun φ : S.residueField (f (U.ι x)) ⟶ U.toScheme.residueField x =>
    ConcreteCategory.hom φ (e.inv.hom a)) h'
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply] at hfun
  exact hfun

/-! ### Assembling a standard shrinking from four principal opens -/

/-- A point mapping to a point of an open of the target lies in the inverse image of that open. -/
private theorem mem_preimage_of_apply_eq {X Y : Scheme.{u}} {g : X ⟶ Y} {U : Y.Opens} {p : X}
    {q : Y} (h : g p = q) (hq : q ∈ U) : p ∈ g ⁻¹ᵁ U :=
  (g.mem_preimage).2 (h ▸ hq)

/-- Four principal opens of the four schemes of a one-step dévissage at `x`, containing the four
distinguished points and compatible with the three morphisms, assemble into a standard
shrinking. -/
def standardShrinkingOfOpens {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] (D : OneStepDevissageAt f F x)
    (V : S.Opens) (U : X.Opens) (T : D.toOneStepDevissage.Z.Opens)
    (W : D.toOneStepDevissage.Y.Opens) (a : Γ(S, ⊤)) (b : Γ(X, ⊤))
    (c : Γ(D.toOneStepDevissage.Z, ⊤)) (d : Γ(D.toOneStepDevissage.Y, ⊤))
    (hV : V = S.basicOpen a) (hU : U = X.basicOpen b)
    (hT : T = D.toOneStepDevissage.Z.basicOpen c) (hW : W = D.toOneStepDevissage.Y.basicOpen d)
    (hs : f x ∈ V) (hx : x ∈ U) (hz : D.z ∈ T) (hy : D.y ∈ W) (hUV : U ≤ f ⁻¹ᵁ V)
    (hTU : T = D.toOneStepDevissage.i ⁻¹ᵁ U) (hTW : T = D.toOneStepDevissage.π ⁻¹ᵁ W)
    (hWV : W ≤ D.toOneStepDevissage.g ⁻¹ᵁ V)
    [Surjective (D.toOneStepDevissage.g.resLE V W hWV)] :
    D.StandardShrinking := by
  let A := D.toOneStepDevissage
  have : IsAffine X := A.affine_X
  have : IsAffine S := A.affine_S
  have : IsAffine A.Z := A.affine_Z
  have : IsAffine A.Y := A.affine_Y
  have : IsAffine U.toScheme := hU ▸ inferInstance
  have : IsAffine V.toScheme := hV ▸ inferInstance
  have : IsAffine T.toScheme := hT ▸ inferInstance
  have : IsAffine W.toScheme := hW ▸ inferInstance
  have : IsClosedImmersion A.i := A.closed_immersion
  have : Smooth A.g := A.smooth
  have : GeometricallyIrreducible A.g := A.geometrically_irreducible
  have : A.G.IsQuasicoherent := A.quasi_coherent_G
  have : A.G.IsFiniteType := A.finite_type_G
  let f' := f.resLE V U hUV
  let i' := A.i.resLE U T hTU.le
  let π' := A.π.resLE W T hTW.le
  let g' := A.g.resLE V W hWV
  have : LocallyOfFiniteType f' := locallyOfFiniteType_resLE f V U hUV
  have : (F.restrict U.ι).IsQuasicoherent := inferInstance
  have : (F.restrict U.ι).IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict U.ι F
  have : (A.G.restrict T.ι).IsQuasicoherent := inferInstance
  have : (A.G.restrict T.ι).IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict T.ι A.G
  have hi := isPullback_ι_resLE A.i U T hTU
  have hπ := isPullback_ι_resLE A.π W T hTW
  let x' : U.toScheme := ⟨x, hx⟩
  let z' : T.toScheme := ⟨D.z, hz⟩
  let y' : W.toScheme := ⟨D.y, hy⟩
  have hgy : g' y' = f' x' := by
    rw [resLE_apply_eq_iff,
      show V.ι (f' x') = f (U.ι x') from Scheme.Hom.coe_resLE_apply f hUV x']
    exact D.g_y
  have hm : f'.asFiber x' ∈ SheafOfModules.supp
      ((Scheme.Modules.pullback (f'.fiberι (f' x'))).obj (F.restrict U.ι)) := by
    rw [Stacks.Modules.supp_pullback, supp_restrict']
    simp only [Set.mem_preimage, Scheme.Hom.fiberι_asFiber]
    have h := D.mem_fiber_support
    rw [Stacks.Modules.supp_pullback] at h
    change x ∈ SheafOfModules.supp F
    simpa only [Set.mem_preimage, Scheme.Hom.fiberι_asFiber] using h
  have hdim := topologicalKrullDim_supp_resLE f F V U hUV x hx D.mem_fiber_support D.dimension hm
  let C : OneStepDevissageAt f' (F.restrict U.ι) x' :=
    { toOneStepDevissage :=
        { Z := T.toScheme
          Y := W.toScheme
          i := i'
          π := π'
          g := g'
          G := A.G.restrict T.ι
          quasi_coherent_G := inferInstance
          finite_type_G := inferInstance
          over_base := by
            apply (cancel_mono V.ι).1
            change i' ≫ f' ≫ V.ι = π' ≫ g' ≫ V.ι
            calc
              i' ≫ f' ≫ V.ι = i' ≫ U.ι ≫ f := by
                rw [show f' ≫ V.ι = U.ι ≫ f from Scheme.Hom.resLE_comp_ι f hUV]
              _ = T.ι ≫ A.i ≫ f := by
                simpa only [Category.assoc, i'] using congrArg (fun k => k ≫ f) hi.w.symm
              _ = T.ι ≫ A.π ≫ A.g := by rw [A.over_base]
              _ = π' ≫ W.ι ≫ A.g := by
                simpa only [Category.assoc, π'] using congrArg (fun k => k ≫ A.g) hπ.w
              _ = π' ≫ g' ≫ V.ι := by rw [Scheme.Hom.resLE_comp_ι]
          affine_X := inferInstance
          affine_S := inferInstance
          affine_Z := inferInstance
          affine_Y := inferInstance
          closed_immersion :=
            MorphismProperty.IsStableUnderBaseChange.of_isPullback hi A.closed_immersion
          finite_presentation :=
            ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback hi A.finite_presentation.1,
              MorphismProperty.IsStableUnderBaseChange.of_isPullback hi
                A.finite_presentation.2.1,
              MorphismProperty.IsStableUnderBaseChange.of_isPullback hi
                A.finite_presentation.2.2⟩
          module_iso := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app F ≪≫
            (Scheme.Modules.pullback U.ι).mapIso A.module_iso ≪≫
            pullbackPushforwardResLEIso A.i A.G U T hTU
          finite := MorphismProperty.IsStableUnderBaseChange.of_isPullback hπ A.finite
          smooth := by dsimp only [g', Scheme.Hom.resLE]; infer_instance
          geometrically_irreducible := geometricallyIrreducible_resLE A.g V W hWV
          fiber_dimension := fun t => (topologicalKrullDim_fiber_resLE A.g V W hWV t).trans
            ((A.fiber_dimension (V.ι t)).trans hdim.1.symm) }
      mem_fiber_support := hm
      dimension := hdim.2
      z := z'
      y := y'
      i_z := (resLE_apply_eq_iff A.i hTU.le z' x').2 D.i_z
      π_z := (resLE_apply_eq_iff A.π hTW.le z' y').2 D.π_z
      g_y := hgy
      fiber_eq_singleton := by
        ext p
        change π' p = y' ↔ p = z'
        rw [resLE_apply_eq_iff, ← ι_eq_iff (p := p) (q := z')]
        exact Set.ext_iff.mp D.fiber_eq_singleton (T.ι p)
      residueField_purelyTranscendental :=
        purelyTranscendental_resLE A.g V W hWV y' (f x) D.g_y (f' x') hgy
          D.residueField_purelyTranscendental }
  exact
    { S' := V, X' := U, Z' := T, Y' := W
      base_section := a, source_section := b, closed_section := c, smooth_section := d
      base_standard := hV, source_standard := hU, closed_standard := hT, smooth_standard := hW
      mem_base := hs, mem_source := hx, mem_closed := hz, mem_smooth := hy
      source_over_base := hUV, closed_over_source := hTU.le
      closed_over_smooth := hTW.le, smooth_over_base := hWV
      restricted_morphism := f', restricted_morphism_eq := rfl
      locally_finite_type := inferInstance
      quasi_coherent := inferInstance, finite_type := inferInstance
      restricted_devissage := C
      restricted_closed := HEq.rfl, restricted_smooth := HEq.rfl
      restricted_closed_map := HEq.rfl, restricted_finite_map := HEq.rfl
      restricted_smooth_map := HEq.rfl, restricted_closed_module := HEq.rfl
      restricted_z := HEq.rfl, restricted_y := HEq.rfl }

/-- The common refinement of parts (2) and (3): a standard shrinking whose smooth open is a
prescribed principal open neighbourhood `W` of `y` cut down to the new base, and whose source
open lies inside a prescribed principal open neighbourhood `U₀` of `x`, provided that the inverse
image of `W` in the closed subscheme already lies over `U₀`. -/
private lemma exists_standardShrinking_smooth_inside {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (x : X) [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (D : OneStepDevissageAt f F x) (W : D.toOneStepDevissage.Y.Opens)
    (a : Γ(D.toOneStepDevissage.Y, ⊤)) (hW : W = D.toOneStepDevissage.Y.basicOpen a)
    (hy : D.y ∈ W) (U₀ : X.Opens) (b : Γ(X, ⊤)) (hU₀ : U₀ = X.basicOpen b) (hx : x ∈ U₀)
    (hWU : D.toOneStepDevissage.π ⁻¹ᵁ W ≤ D.toOneStepDevissage.i ⁻¹ᵁ U₀) :
    ∃ E : D.StandardShrinking,
      E.Y' = W ⊓ (D.toOneStepDevissage.g ⁻¹ᵁ E.S') ∧ E.X' ≤ U₀ := by
  let A := D.toOneStepDevissage
  have : IsAffine X := A.affine_X
  have : IsAffine S := A.affine_S
  have : IsClosedImmersion A.i := A.closed_immersion
  have : Smooth A.g := A.smooth
  let O : S.Opens := ⟨A.g '' (W : Set A.Y), A.g.isOpenMap _ W.isOpen⟩
  have hsO : f x ∈ O := ⟨D.y, hy, D.g_y⟩
  obtain ⟨c, hcO, hc⟩ := (isAffineOpen_top S).exists_basicOpen_le (⟨f x, hsO⟩ : O) trivial
  let V := S.basicOpen c
  obtain ⟨h, hh⟩ := A.i.app_surjective ⊤ (isAffineOpen_top X) (A.π.appTop a)
  have hpre : A.i ⁻¹ᵁ X.basicOpen h = A.π ⁻¹ᵁ W := by
    rw [hW, Scheme.preimage_basicOpen_top, Scheme.preimage_basicOpen_top]
    exact congrArg A.Z.basicOpen hh
  let U := X.basicOpen h ⊓ U₀ ⊓ f ⁻¹ᵁ V
  let W' := W ⊓ A.g ⁻¹ᵁ V
  let T := A.π ⁻¹ᵁ W'
  have hy' : D.y ∈ W' := ⟨hy, mem_preimage_of_apply_eq D.g_y hc⟩
  have hz : D.z ∈ T := mem_preimage_of_apply_eq D.π_z hy'
  have hTU : T = A.i ⁻¹ᵁ U := by
    dsimp only [T, W', U]
    rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, hpre,
      ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, A.over_base, inf_eq_left.mpr hWU]
  have hxU : x ∈ U := by
    have hzh : D.z ∈ A.i ⁻¹ᵁ X.basicOpen h := by
      rw [hpre]
      exact mem_preimage_of_apply_eq D.π_z hy
    exact ⟨⟨D.i_z ▸ hzh, hx⟩, hc⟩
  have hUV : U ≤ f ⁻¹ᵁ V := inf_le_right
  have hWV : W' ≤ A.g ⁻¹ᵁ V := inf_le_right
  have : Surjective (A.g.resLE V W' hWV) := ⟨by
    intro t
    obtain ⟨y, hyW, hyt⟩ := hcO t.property
    refine ⟨⟨y, hyW, ?_⟩, ?_⟩
    · show A.g y ∈ V
      rw [hyt]
      exact t.property
    · exact (resLE_apply_eq_iff A.g hWV _ t).2 hyt⟩
  let d := a * A.g.appTop c
  have hd : W' = A.Y.basicOpen d := by
    show W ⊓ A.g ⁻¹ᵁ V = A.Y.basicOpen (a * A.g.appTop c)
    rw [hW, Scheme.basicOpen_mul, ← Scheme.preimage_basicOpen_top]
  let E := standardShrinkingOfOpens f F x D V U T W' c (h * b * f.appTop c) (A.π.appTop d) d rfl
    (by simp only [U, hU₀, Scheme.basicOpen_mul, ← Scheme.preimage_basicOpen_top]; rfl)
    (by rw [show T = A.π ⁻¹ᵁ W' from rfl, hd, Scheme.preimage_basicOpen_top]) hd hc hxU hz hy'
    hUV hTU rfl hWV
  exact ⟨E, rfl, inf_le_left.trans inf_le_right⟩

/-- **Stacks Tag 05HA, part (1).** Restricting a one-step dévissage at `x` to a principal open
neighbourhood `V` of `f x` in the base is a standard shrinking, whose other three opens are the
inverse images of `V`. -/
@[stacks 05HA "part (1)"]
theorem exists_standardShrinking_base {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] (D : OneStepDevissageAt f F x)
    (V : S.Opens) (a : Γ(S, ⊤)) (hV : V = S.basicOpen a) (hs : f x ∈ V) :
    ∃ E : D.StandardShrinking, E.S' = V ∧ E.X' = f ⁻¹ᵁ V ∧
      E.Z' = (D.toOneStepDevissage.i ≫ f) ⁻¹ᵁ V ∧ E.Y' = D.toOneStepDevissage.g ⁻¹ᵁ V := by
  let A := D.toOneStepDevissage
  have : GeometricallyIrreducible A.g := A.geometrically_irreducible
  have : Surjective (A.g.resLE V (A.g ⁻¹ᵁ V) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  have hTU : (A.i ≫ f) ⁻¹ᵁ V = A.i ⁻¹ᵁ (f ⁻¹ᵁ V) := Scheme.Hom.comp_preimage _ _ _
  have hTW : (A.i ≫ f) ⁻¹ᵁ V = A.π ⁻¹ᵁ (A.g ⁻¹ᵁ V) := by
    rw [A.over_base, Scheme.Hom.comp_preimage]
  let E := standardShrinkingOfOpens f F x D V (f ⁻¹ᵁ V) ((A.i ≫ f) ⁻¹ᵁ V) (A.g ⁻¹ᵁ V) a
    (f.appTop a) ((A.i ≫ f).appTop a) (A.g.appTop a) hV
    (by rw [hV, Scheme.preimage_basicOpen_top]) (by rw [hV, Scheme.preimage_basicOpen_top])
    (by rw [hV, Scheme.preimage_basicOpen_top]) hs hs
    (mem_preimage_of_apply_eq (congrArg f D.i_z) hs) (mem_preimage_of_apply_eq D.g_y hs)
    le_rfl hTU hTW le_rfl
  exact ⟨E, rfl, rfl, rfl, rfl⟩

/-- **Stacks Tag 05HA, part (2).** Given a principal open neighbourhood `W` of the distinguished
point `y` of the smooth scheme, there is a standard shrinking whose smooth open is `W` cut down
to the inverse image of the new base. -/
@[stacks 05HA "part (2)"]
theorem exists_standardShrinking_smooth {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] (D : OneStepDevissageAt f F x)
    (W : D.toOneStepDevissage.Y.Opens) (a : Γ(D.toOneStepDevissage.Y, ⊤))
    (hW : W = D.toOneStepDevissage.Y.basicOpen a) (hy : D.y ∈ W) :
    ∃ E : D.StandardShrinking, E.Y' = W ⊓ (D.toOneStepDevissage.g ⁻¹ᵁ E.S') := by
  obtain ⟨E, hE, -⟩ :=
    exists_standardShrinking_smooth_inside f F x D W a hW hy ⊤ 1 (by simp) trivial (by simp)
  exact ⟨E, hE⟩

/-- **Stacks Tag 05HA, part (3).** Given any open neighbourhood `U` of `x`, there is a standard
shrinking whose source open lies inside `U`. -/
@[stacks 05HA "part (3)"]
theorem exists_standardShrinking_source {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] (D : OneStepDevissageAt f F x)
    (U : X.Opens) (hx : x ∈ U) : ∃ E : D.StandardShrinking, E.X' ≤ U := by
  let A := D.toOneStepDevissage
  have : IsAffine X := A.affine_X
  have : IsAffine A.Y := A.affine_Y
  have : IsFinite A.π := A.finite
  obtain ⟨b, hbU, hb⟩ := (isAffineOpen_top X).exists_basicOpen_le (⟨x, hx⟩ : U) trivial
  have hz : D.z ∈ A.i ⁻¹ᵁ X.basicOpen b := mem_preimage_of_apply_eq D.i_z hb
  obtain ⟨W, hy, hW⟩ :=
    exists_open_preimage_le A.π D.z D.y D.π_z D.fiber_eq_singleton (A.i ⁻¹ᵁ X.basicOpen b) hz
  obtain ⟨a, haW, ha⟩ := (isAffineOpen_top A.Y).exists_basicOpen_le (⟨D.y, hy⟩ : W) trivial
  obtain ⟨E, -, hE⟩ := exists_standardShrinking_smooth_inside f F x D (A.Y.basicOpen a) a rfl ha
    (X.basicOpen b) b rfl hb ((A.π.preimage_mono haW).trans hW)
  exact ⟨E, hE.trans hbU⟩

end AlgebraicGeometry

end
