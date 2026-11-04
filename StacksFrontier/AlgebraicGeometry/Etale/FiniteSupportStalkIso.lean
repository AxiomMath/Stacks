module

public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalkGeometric
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalkVanishing

/-!
# The germ decomposition of a finite-support stalk is an isomorphism

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site, let `ȳ` be a geometric
point of `Y` and let `F` be an abelian sheaf on the small étale site of `X`. The canonical map
`(f_{p!}F)_ȳ ⟶ ⊕_{f(x̄) = ȳ} F_x̄` is an isomorphism. Surjectivity is already available; what is
proved here is injectivity, and with it the isomorphism of Stacks 0F6P.

An element of the stalk is a finite sum of germs of sections supported on supports finite over
étale neighbourhoods of `ȳ`; after shrinking the neighbourhood all the supports may be taken over
one neighbourhood `V`. If every germ of the family vanishes, each support is cut, over a further
shrinking of `V`, into the finitely many pieces meeting the geometric fibre in a single point, and
the pieces belonging to distinct points of the geometric fibre have disjoint supports. For a single
support the vanishing of all its germs is handled directly: the zero locus of the section contains
the whole fibre of the support over the image point of `ȳ`, so, the support being finite over `V`,
shrinking `V` once more makes the section itself zero.

## Main definitions

No new definitions are introduced beyond the isomorphism
`AlgebraicGeometry.SmallEtale.finiteSupportStalkIso`.

## Main results

* `AlgebraicGeometry.SmallEtale.injective_finiteSupportStalkToFiberStalks` — the germ
  decomposition map is injective.
* `AlgebraicGeometry.SmallEtale.finiteSupportStalkIso` — the germ decomposition
  `(f_{p!}F)_ȳ ≅ ⊕_{f(x̄) = ȳ} F_x̄`, with `finiteSupportStalkIso_hom` identifying its forward
  direction with the canonical map, so that the germ characterization and the naturality of that
  map describe the isomorphism.

## Implementation notes

The isomorphism is obtained as `CategoryTheory.asIso` of the canonical map of
`StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalk` rather than produced abstractly, so that
every property already proved of that map — its value on a germ, its vanishing off the canonical
support-open, its naturality in the sheaf — is a property of the isomorphism.

The one point where the geometry of `f` is used again, beyond what the surjectivity half needed,
is the lifting of a point of the fibre of a finite morphism to a morphism from the spectrum of the
algebraically closed residue field: it is what turns the hypothesis that all germs of a family
vanish into a statement about the zero locus of the section on the whole fibre.

## References

* [Stacks Project, Tag 0F6P](https://stacks.math.columbia.edu/tag/0F6P)
* [Stacks Project, Tag 0F6M](https://stacks.math.columbia.edu/tag/0F6M)
* [Stacks Project, Tag 04FR](https://stacks.math.columbia.edu/tag/04FR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe u v

namespace AlgebraicGeometry

section SchemeLift

/-- A point of the fibre of a locally quasi-finite morphism over the image of a morphism from the
spectrum of an algebraically closed field lifts to a morphism from that spectrum. -/
private theorem exists_lift_of_locallyQuasiFinite_of_isAlgClosed {X S : Scheme.{u}} (g : X ⟶ S)
    [LocallyQuasiFinite g] {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S)
    (x : X) (hx : g x = t default) :
    ∃ l : Spec (.of Ω) ⟶ X, l ≫ g = t ∧ l default = x := by
  obtain ⟨⟨y, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω S).symm.surjective t
  obtain rfl : g x = y := by simpa [Scheme.SpecToEquivOfField] using hx
  let m := (g.residueFieldMap x).hom
  dsimp at m
  algebraize [m, a.hom]
  have hm : m.QuasiFinite := by
    apply RingHom.QuasiFinite.of_comp (g := (S.residue (g x)).hom)
    rw [← CommRingCat.hom_comp, Scheme.residue_residueFieldMap]
    exact (RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective _
      IsLocalRing.residue_surjective)).comp (g.quasiFiniteAt x)
  have : Algebra.QuasiFinite (S.residueField (g x)) (X.residueField x) := hm
  have : Module.Finite (S.residueField (g x)) (X.residueField x) := .of_quasiFinite
  let b : X.residueField x →ₐ[S.residueField (g x)] Ω := IsAlgClosed.lift
  have hb : g.residueFieldMap x ≫ CommRingCat.ofHom b.toRingHom = a := by
    ext1
    exact b.comp_algebraMap
  refine ⟨Spec.map (CommRingCat.ofHom b.toRingHom) ≫ X.fromSpecResidueField x, ?_, ?_⟩
  · have hrhs : (Scheme.SpecToEquivOfField Ω S).symm ⟨g x, a⟩ =
        Spec.map a ≫ S.fromSpecResidueField (g x) := rfl
    have hmap := Spec.map_comp (g.residueFieldMap x) (CommRingCat.ofHom b.toRingHom)
    rw [hrhs, ← hb, hmap]
    exact ((Category.assoc _ _ _).trans
      (congrArg (fun m => Spec.map (CommRingCat.ofHom b.toRingHom) ≫ m)
        (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g x))).symm
  · exact X.fromSpecResidueField_apply x _

end SchemeLift

namespace SmallEtale

section Generators

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (s : GeometricPoint Y.obj)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max u v})
  (hsmall : ∀ V : SmallEtale B Y.obj Y.property, Small.{max u v} (FiniteSupport B f V))

/-- The germ in the stalk of the finite-support direct image of a section supported on a support
finite over an étale neighbourhood of the geometric point: the composite of the two colimit
inclusions. -/
private def stalkGenerator (U : (geometricPointFiber B Y.obj Y.property s).Elements)
    (E : FiniteSupport B f U.1) :
    (finiteSupportDiagram B f F U.1).obj E ⟶
      etaleStalk B Y.obj Y.property s ((finiteSupportPushforward B f hsmall).1.obj F) :=
  colimit.ι (finiteSupportDiagram B f F U.1) E ≫
    eqToHom ((finiteSupportPushforward B f hsmall).2.obj_eq F U.1).symm ≫
    colimit.ι (etaleStalkDiagram B Y.obj Y.property s
      ((finiteSupportPushforward B f hsmall).1.obj F)) (op U)

/-- The germ decomposition map sends a germ of a supported section to the decomposition of that
section. -/
private theorem stalkGenerator_comp (U : (geometricPointFiber B Y.obj Y.property s).Elements)
    (E : FiniteSupport B f U.1) :
    stalkGenerator B f s F hsmall U E ≫ finiteSupportStalkToFiberStalks B f s F hsmall =
      fiberStalkHom B f s F U.1 U.2 E := by
  unfold stalkGenerator
  simp only [Category.assoc]
  exact finiteSupportStalkToFiberStalks_generator B f s F hsmall U E

/-- The germ decomposition map sends a sum of germs of supported sections to the sum of the
decompositions of those sections. -/
private theorem finiteSupportStalkToFiberStalks_sum_stalkGenerator
    (U : (geometricPointFiber B Y.obj Y.property s).Elements)
    {I : Type*} [Fintype I] (E : I → FiniteSupport B f U.1)
    (a : ∀ i, (finiteSupportDiagram B f F U.1).obj (E i)) :
    finiteSupportStalkToFiberStalks B f s F hsmall
        (∑ i, (stalkGenerator B f s F hsmall U (E i)) (a i)) =
      ∑ i, fiberStalkSum B f s F U.1 U.2 (E i) (a i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ =>
    ConcreteCategory.congr_hom (stalkGenerator_comp B f s F hsmall U (E i)) (a i)

/-- Enlarging the support does not change the germ of a supported section. -/
private theorem stalkGenerator_transition
    (U : (geometricPointFiber B Y.obj Y.property s).Elements)
    (E E' : FiniteSupport B f U.1) (h : E ≤ E') :
    (finiteSupportDiagram B f F U.1).map (homOfLE h) ≫ stalkGenerator B f s F hsmall U E' =
      stalkGenerator B f s F hsmall U E := by
  unfold stalkGenerator
  rw [← Category.assoc, colimit.w]

/-- Shrinking the étale neighbourhood does not change the germ of a supported section. -/
private theorem stalkGenerator_baseChange
    {U V : (geometricPointFiber B Y.obj Y.property s).Elements} (g : V ⟶ U)
    (E : FiniteSupport B f U.1) :
    AddCommGrpCat.ofHom (finiteSupportBaseChange B f F g.1 E).sectionsMap ≫
        stalkGenerator B f s F hsmall V (finiteSupportBaseChange B f F g.1 E).support =
      stalkGenerator B f s F hsmall U E := by
  have hres := (finiteSupportPushforward B f hsmall).2.map_restrict F g.1 E
  have hw := colimit.w (etaleStalkDiagram B Y.obj Y.property s
    ((finiteSupportPushforward B f hsmall).1.obj F)) g.op
  have h := congrArg (fun z =>
      z ≫ eqToHom ((finiteSupportPushforward B f hsmall).2.obj_eq F V.1).symm ≫
        colimit.ι (etaleStalkDiagram B Y.obj Y.property s
          ((finiteSupportPushforward B f hsmall).1.obj F)) (op V)) hres
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at h
  unfold stalkGenerator
  refine h.symm.trans ?_
  exact congrArg (fun z => colimit.ι (finiteSupportDiagram B f F U.1) E ≫
    eqToHom ((finiteSupportPushforward B f hsmall).2.obj_eq F U.1).symm ≫ z) hw

/-- The germ of a supported section whose decomposition vanishes at a point of the geometric
fibre, read on the canonical support-open. -/
private theorem fiberStalkComponent_germ (x : GeometricFiberPoint B f s)
    (U : (geometricPointFiber B Y.obj Y.property s).Elements) (E : FiniteSupport B f U.1)
    (V : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).Elements)
    (t : V.1 ⟶ finiteSupportOpenObject B f U.1 E)
    (hU : V.2.1 ≫ (SmallEtale.toScheme B X.obj X.property).map t ≫
        (finiteSupportOpen B f U.1 E).ι ≫
        B.inclusion.map (pullback.fst U.1.obj.hom f) = U.2.1)
    (hX : V.2.1 ≫ (SmallEtale.toScheme B X.obj X.property).map t ≫
        (finiteSupportOpen B f U.1 E).ι ≫
        B.inclusion.map (pullback.snd U.1.obj.hom f) = x.1)
    (a : (finiteSupportDiagram B f F U.1).obj E) :
    fiberStalkComponent B f s F U.1 U.2 E a x =
      (F.obj.map t.op ≫
        colimit.ι (etaleStalkDiagram B X.obj X.property (x.toGeometricPoint B f s) F.obj)
          (op V)) a.val := by
  have h := finiteSupportStalkToFiberStalks_germ B f s F (fun _ => inferInstance) x U E V t hU hX a
  rw [finiteSupportStalkToFiberStalks_generator] at h
  exact h

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- A point of the fibre of a support over the image point of the geometric point is the image of
the chosen point of the spectrum under a lift of the geometric point through the support, and so is
hit by a point of the geometric fibre. -/
private theorem exists_fiberPoint_of_mem_fibre
    (U : (geometricPointFiber B Y.obj Y.property s).Elements)
    {Z : Scheme.{u}} (i : Z ⟶ (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1))
    [LocallyQuasiFinite (i ≫ B.inclusion.map (pullback.fst U.1.obj.hom f))] (z : Z)
    (hz : (i ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)).base z = U.2.1.base default) :
    ∃ (x : GeometricFiberPoint B f s) (r : s.source ⟶ Z),
      fiberPointLift B f s U.1 U.2 x = r ≫ i ∧ r.base default = z := by
  obtain ⟨r, hr, hrz⟩ := exists_lift_of_locallyQuasiFinite_of_isAlgClosed
    (i ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)) U.2.1 z hz
  have hpb := (IsPullback.of_hasPullback U.1.obj.hom f).map B.inclusion
  have hx1 : (r ≫ i ≫ B.inclusion.map (pullback.snd U.1.obj.hom f)) ≫
      B.inclusion.map f = s.hom := by
    rw [Category.assoc, Category.assoc]
    refine (congrArg (fun m => r ≫ i ≫ m) hpb.w.symm).trans ?_
    have h := (congrArg (· ≫ B.inclusion.map U.1.obj.hom) hr).trans U.2.2
    simp only [Category.assoc] at h
    exact h
  exact ⟨⟨_, hx1⟩, r, hpb.hom_ext
    ((fiberPointLift_comp_fst B f s U.1 U.2 _).trans (hr.symm.trans (Category.assoc _ _ _).symm))
    ((fiberPointLift_comp_snd B f s U.1 U.2 _).trans (Category.assoc _ _ _).symm), hrz⟩

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- **Shrinking the étale neighbourhood moves a fibre-neighbourhood into an open of a finite
scheme.** If the fibre of a finite scheme `Z` over the image point of the geometric point lies in
an open `P` of `Z`, then over a smaller étale neighbourhood every point of `Z` hit by the base
change of the neighbourhood lies in `P`. -/
private theorem exists_shrink_mem_of_fibre_subset
    (U : (geometricPointFiber B Y.obj Y.property s).Elements)
    {Z : Scheme.{u}} (i : Z ⟶ (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1))
    [IsFinite (i ≫ B.inclusion.map (pullback.fst U.1.obj.hom f))] (P : Z.Opens)
    (hP : (i ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)).base ⁻¹' {U.2.1.base default} ⊆ P) :
    ∃ (V : (geometricPointFiber B Y.obj Y.property s).Elements) (g : V ⟶ U),
      ∀ (q : (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V.1)) (w : Z),
        ((SmallEtale.toScheme B X.obj X.property).map
          ((smallEtaleBaseChange B f).map g.1)).base q = i.base w → w ∈ P := by
  obtain ⟨W₀, hW, hWP⟩ := exists_open_preimage_le_of_isClosedMap
    (i ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)).base
    (i ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)).isClosedMap (U.2.1.base default) P hP
  let W : ((SmallEtale.toScheme B Y.obj Y.property).obj U.1).Opens := W₀
  have hWmem : U.2.1.base default ∈ (W : Set ((SmallEtale.toScheme B Y.obj Y.property).obj U.1)) :=
    hW
  have hk : (SmallEtale.toScheme B X.obj X.property).map
        ((smallEtaleBaseChange B f).map (openObjectι B Y.obj Y.property U.1 W)) ≫
        B.inclusion.map (pullback.fst U.1.obj.hom f) =
      B.inclusion.map (pullback.fst (openObject B Y.obj Y.property U.1 W).obj.hom f) ≫ W.ι :=
    (toScheme_baseChange_comp_fst B f U.1 (openObject B Y.obj Y.property U.1 W)
        (openObjectι B Y.obj Y.property U.1 W)).trans
      (congrArg (fun m => B.inclusion.map
          (pullback.fst (openObject B Y.obj Y.property U.1 W).obj.hom f) ≫ m)
        (openObjectι_map B Y.obj Y.property U.1 W))
  refine ⟨⟨openObject B Y.obj Y.property U.1 W,
      openObjectLift B Y.obj Y.property s U.1 U.2 W hWmem⟩,
    ⟨openObjectι B Y.obj Y.property U.1 W,
      openObjectLift_map B Y.obj Y.property s U.1 U.2 W hWmem⟩, fun q w hqw => hWP ?_⟩
  change (i ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)).base w ∈
    (W : Set ((SmallEtale.toScheme B Y.obj Y.property).obj U.1))
  rw [Scheme.Hom.comp_apply, ← hqw, ← Scheme.Hom.comp_apply, hk]
  exact Subtype.property _

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- **Shrinking the étale neighbourhood kills a section all of whose germs vanish.** The germs of
a section supported on a support finite over `V` vanish at every point of the geometric fibre
exactly when the zero locus of the section contains the whole fibre of the support over the image
point of the geometric point; the support being finite over `V`, that fibre has a neighbourhood in
`V` over which the section vanishes outright. -/
private theorem exists_shrink_sectionsMap_eq_zero
    (U : (geometricPointFiber B Y.obj Y.property s).Elements) (E : FiniteSupport B f U.1)
    (a : (finiteSupportDiagram B f F U.1).obj E)
    (ha : ∀ x : GeometricFiberPoint B f s, fiberStalkComponent B f s F U.1 U.2 E a x = 0) :
    ∃ (V : (geometricPointFiber B Y.obj Y.property s).Elements) (g : V ⟶ U),
      (finiteSupportBaseChange B f F g.1 E).sectionsMap a = 0 := by
  classical
  obtain ⟨Z, i, hi, hfin, hiE⟩ := E.property
  have hi' : IsImmersion i := hi
  have hfin' : IsFinite (i ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)) := hfin
  have hpb := (IsPullback.of_hasPullback U.1.obj.hom f).map B.inclusion
  have hiO : Set.range i.base ⊆ Set.range (finiteSupportOpen B f U.1 E).ι.base := by
    rw [Scheme.Opens.range_ι, hiE]
    exact subset_supportOpen B X.obj X.property (baseChange B f U.1) E.1
      (finiteSupport_isLocallyClosed B f U.1 E)
  obtain ⟨j, hj⟩ : ∃ j : Z ⟶ (finiteSupportOpen B f U.1 E).toScheme,
      j ≫ (finiteSupportOpen B f U.1 E).ι = i :=
    ⟨IsOpenImmersion.lift _ i hiO, IsOpenImmersion.lift_fac _ _ _⟩
  have hzero : (i ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)).base ⁻¹'
        {U.2.1.base default} ⊆
      (j ⁻¹ᵁ zeroOpen B X.obj X.property F (finiteSupportOpenObject B f U.1 E) a.val :
        Set Z) := by
    intro z hz
    obtain ⟨x, r, hfl, hrz⟩ := exists_fiberPoint_of_mem_fibre B f s U i z hz
    have hcomp : (fiberPointLift B f s U.1 U.2 x).base default = i.base z :=
      (congrArg (fun m : s.source ⟶ _ => m.base (default : ↥s.source)) hfl).trans
        (congrArg i.base hrz)
    have hptE : (fiberPointLift B f s U.1 U.2 x).base default ∈ E.1 :=
      hcomp ▸ hiE.subset (Set.mem_range_self z)
    have hmem : HasFiberLift B f s U.1 U.2 E x :=
      subset_supportOpen B X.obj X.property (baseChange B f U.1) E.1
        (finiteSupport_isLocallyClosed B f U.1 E) hptE
    have hzerogerm := ha x
    rw [fiberStalkComponent_of_hasFiberLift B f s F U.1 U.2 E a x hmem] at hzerogerm
    have hmem0 := (etaleGerm_eq_zero_iff_mem_zeroOpen B X.obj X.property
      (x.toGeometricPoint B f s) F (finiteSupportOpenObject B f U.1 E)
      (openObjectLift B X.obj X.property (x.toGeometricPoint B f s) (baseChange B f U.1)
        (fiberPointElement B f s U.1 U.2 x) (finiteSupportOpen B f U.1 E) hmem)
      a.val).1 hzerogerm
    have hlift : (openObjectLift B X.obj X.property (x.toGeometricPoint B f s)
        (baseChange B f U.1) (fiberPointElement B f s U.1 U.2 x)
        (finiteSupportOpen B f U.1 E) hmem).1 = r ≫ j := by
      refine (cancel_mono (finiteSupportOpen B f U.1 E).ι).1 ?_
      calc (openObjectLift B X.obj X.property (x.toGeometricPoint B f s) (baseChange B f U.1)
              (fiberPointElement B f s U.1 U.2 x) (finiteSupportOpen B f U.1 E) hmem).1 ≫
            (finiteSupportOpen B f U.1 E).ι
          = fiberPointLift B f s U.1 U.2 x :=
            openObjectLift_comp_ι B X.obj X.property (x.toGeometricPoint B f s)
              (baseChange B f U.1) (fiberPointElement B f s U.1 U.2 x)
              (finiteSupportOpen B f U.1 E) hmem
        _ = r ≫ i := hfl
        _ = r ≫ j ≫ (finiteSupportOpen B f U.1 E).ι := congrArg (fun m => r ≫ m) hj.symm
        _ = (r ≫ j) ≫ (finiteSupportOpen B f U.1 E).ι := (Category.assoc r j _).symm
    have hpt : (openObjectLift B X.obj X.property (x.toGeometricPoint B f s)
        (baseChange B f U.1) (fiberPointElement B f s U.1 U.2 x)
        (finiteSupportOpen B f U.1 E) hmem).1.base default = j.base z :=
      (congrArg (fun m : s.source ⟶ _ => m.base (default : ↥s.source)) hlift).trans
        (congrArg j.base hrz)
    show j.base z ∈
      zeroOpen B X.obj X.property F (finiteSupportOpenObject B f U.1 E) a.val
    exact hpt ▸ hmem0
  obtain ⟨V, g, hg⟩ := exists_shrink_mem_of_fibre_subset B f s U i
    (j ⁻¹ᵁ zeroOpen B X.obj X.property F (finiteSupportOpenObject B f U.1 E) a.val) hzero
  refine ⟨V, g, Subtype.ext ?_⟩
  show F.obj.map (finiteSupportBaseChange B f F g.1 E).openMap.op a.val = 0
  refine (map_eq_zero_iff_range_subset_zeroOpen B X.obj X.property F
    (finiteSupportOpenObject B f U.1 E) a.val _
    (finiteSupportBaseChange B f F g.1 E).openMap).2 ?_
  rintro y ⟨w, rfl⟩
  by_contra hy
  obtain ⟨w₀, hw₀⟩ := hiE.symm.subset (a.property hy)
  have hwj : j.base w₀ = ((SmallEtale.toScheme B X.obj X.property).map
      (finiteSupportBaseChange B f F g.1 E).openMap).base w :=
    (finiteSupportOpen B f U.1 E).ι.isEmbedding.injective
      ((congrArg (fun m : Z ⟶ _ => m.base w₀) hj).trans hw₀)
  refine hy (hwj ▸ hg ((finiteSupportOpen B f V.1
    (finiteSupportBaseChange B f F g.1 E).support).ι.base w) w₀ ?_)
  rw [hw₀]
  exact (congrArg (fun m => m.base w)
    (finiteSupportBaseChange B f F g.1 E).openMap_commutes).symm

/-- A germ of a supported section all of whose components vanish is zero in the stalk. -/
private theorem stalkGenerator_eq_zero
    (U : (geometricPointFiber B Y.obj Y.property s).Elements) (E : FiniteSupport B f U.1)
    (a : (finiteSupportDiagram B f F U.1).obj E)
    (ha : fiberStalkSum B f s F U.1 U.2 E a = 0) :
    (stalkGenerator B f s F hsmall U E) a = 0 := by
  have hcomp : ∀ x : GeometricFiberPoint B f s,
      fiberStalkComponent B f s F U.1 U.2 E a x = 0 := by
    intro x
    have h := congrArg (fun z : fiberStalks B f s F => z x) ha
    simp only [DirectSum.zero_apply] at h
    exact h
  obtain ⟨V, g, hg⟩ := exists_shrink_sectionsMap_eq_zero B f s F U E a hcomp
  have H := ConcreteCategory.congr_hom (stalkGenerator_baseChange B f s F hsmall g E) a
  change (stalkGenerator B f s F hsmall V (finiteSupportBaseChange B f F g.1 E).support)
    ((finiteSupportBaseChange B f F g.1 E).sectionsMap a) = _ at H
  rw [hg] at H
  exact H.symm.trans (map_zero _)

/-- Two supported sections with the same germ decomposition have the same germ in the stalk. -/
private theorem stalkGenerator_eq_of_fiberStalkSum_eq
    (U : (geometricPointFiber B Y.obj Y.property s).Elements) (E : FiniteSupport B f U.1)
    (a b : (finiteSupportDiagram B f F U.1).obj E)
    (h : fiberStalkSum B f s F U.1 U.2 E a = fiberStalkSum B f s F U.1 U.2 E b) :
    (stalkGenerator B f s F hsmall U E) a = (stalkGenerator B f s F hsmall U E) b := by
  have hsub : fiberStalkSum B f s F U.1 U.2 E (a - b) = 0 := by
    have hs : fiberStalkSum B f s F U.1 U.2 E (a - b) =
        fiberStalkSum B f s F U.1 U.2 E a - fiberStalkSum B f s F U.1 U.2 E b :=
      map_sub (fiberStalkHom B f s F U.1 U.2 E).hom a b
    rw [hs, h, sub_self]
  have H := stalkGenerator_eq_zero B f s F hsmall U E (a - b) hsub
  rw [map_sub, sub_eq_zero] at H
  exact H

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- Membership of the lift of a point of the geometric fibre in the inverse image of a subset of
a base change is membership of the lift in the subset itself. -/
private theorem fiberPointLift_mem_preimage
    {U V : (geometricPointFiber B Y.obj Y.property s).Elements} (g : V ⟶ U)
    (E : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1)))
    (x : GeometricFiberPoint B f s) :
    (fiberPointLift B f s V.1 V.2 x).base default ∈
        ((SmallEtale.toScheme B X.obj X.property).map
          ((smallEtaleBaseChange B f).map g.1)).base ⁻¹' E ↔
      (fiberPointLift B f s U.1 U.2 x).base default ∈ E := by
  have hpt : ((SmallEtale.toScheme B X.obj X.property).map
        ((smallEtaleBaseChange B f).map g.1)).base
        ((fiberPointLift B f s V.1 V.2 x).base default) =
      (fiberPointLift B f s U.1 U.2 x).base default :=
    congrArg (fun m : s.source ⟶ _ => m.base (default : ↥s.source))
      (fiberPointLift_comp_baseChange B f s U.1 V.1 g.1 U.2 V.2 g.2 x)
  show ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map g.1)).base
      ((fiberPointLift B f s V.1 V.2 x).base default) ∈ E ↔ _
  rw [hpt]

/-- **An open support concentrated at one point of the geometric fibre.** Every point of the
geometric fibre has an étale neighbourhood of the geometric point of `Y` carrying an open support
finite over it which the geometric fibre meets in that point alone. -/
private theorem exists_isOpen_finiteSupport_unique_mem (x : GeometricFiberPoint B f s) :
    ∃ (U : (geometricPointFiber B Y.obj Y.property s).Elements) (E : FiniteSupport B f U.1),
      IsOpen E.1 ∧ ∀ y : GeometricFiberPoint B f s,
        (fiberPointLift B f s U.1 U.2 y).base default ∈ E.1 ↔ y = x := by
  have hid : Etale (B.inclusion.map (𝟙 X)) := by
    simpa using (inferInstance : Etale (𝟙 X.obj))
  let N : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).Elements :=
    ⟨⟨Over.mk (𝟙 X), hid⟩, ⟨x.1, by simp⟩⟩
  obtain ⟨U, O, r, t, hfin, hrU, hrN, huniq⟩ := exists_finite_open_neighborhood B f s x N
  have hpb := (IsPullback.of_hasPullback U.1.obj.hom f).map B.inclusion
  have ht : (SmallEtale.toScheme B X.obj X.property).map t =
      O.ι ≫ B.inclusion.map (pullback.snd U.1.obj.hom f) := by
    have H := congrArg B.inclusion.map (Over.w t.hom)
    simp only [Functor.map_comp, Over.mk_hom, Functor.map_preimage] at H
    exact H
  have hrX : r ≫ O.ι ≫ B.inclusion.map (pullback.snd U.1.obj.hom f) = x.1 := by
    rwa [← ht]
  have hp : fiberPointLift B f s U.1 U.2 x = r ≫ O.ι :=
    hpb.hom_ext
      ((fiberPointLift_comp_fst B f s U.1 U.2 x).trans (hrU.symm.trans (Category.assoc _ _ _).symm))
      ((fiberPointLift_comp_snd B f s U.1 U.2 x).trans (hrX.symm.trans (Category.assoc _ _ _).symm))
  refine ⟨U, ⟨(O : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1))),
    isFiniteSupport_of_isFinite_opens B f U.1 O hfin⟩, O.isOpen, fun y => ⟨?_, ?_⟩⟩
  · exact fun hy => eq_of_fiberPointLift_mem_of_unique_lift B f s U O r huniq x hp.symm y hy
  · intro hy
    subst hy
    have hpt : (fiberPointLift B f s U.1 U.2 y).base default = O.ι.base (r.base default) :=
      congrArg (fun m : s.source ⟶ _ => m.base (default : ↥s.source)) hp
    rw [hpt]
    exact Subtype.property _

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- Finitely many supports can be pushed into finitely many opens by one shrinking. -/
private theorem exists_shrink_supports_subset_opens
    (U : (geometricPointFiber B Y.obj Y.property s).Elements)
    {I : Type*} [Finite I] (E : I → FiniteSupport B f U.1)
    (O : I → ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1)).Opens)
    (hO : ∀ (k : I) (x : GeometricFiberPoint B f s),
      (fiberPointLift B f s U.1 U.2 x).base default ∈ (E k).1 →
        (fiberPointLift B f s U.1 U.2 x).base default ∈
          (O k : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1)))) :
    ∃ (V : (geometricPointFiber B Y.obj Y.property s).Elements) (g : V ⟶ U), ∀ k : I,
      (finiteSupportBaseChange B f F g.1 (E k)).support.1 ⊆
        ((SmallEtale.toScheme B X.obj X.property).map
            ((smallEtaleBaseChange B f).map g.1)).base ⁻¹'
          (O k : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1))) := by
  classical
  have hshr : ∀ k : I, ∃ (V : (geometricPointFiber B Y.obj Y.property s).Elements) (g : V ⟶ U),
      (finiteSupportBaseChange B f F g.1 (E k)).support.1 ⊆
        ((SmallEtale.toScheme B X.obj X.property).map
            ((smallEtaleBaseChange B f).map g.1)).base ⁻¹'
          (O k : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1))) := by
    intro k
    obtain ⟨Z, i, hi, hfin, hiE⟩ := (E k).property
    have hi' : IsImmersion i := hi
    have hfin' : IsFinite (i ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)) := hfin
    have hcover : (i ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)).base ⁻¹'
        {U.2.1.base default} ⊆ (i ⁻¹ᵁ O k : Set Z) := by
      intro z hz
      obtain ⟨x, r, hfl, hrz⟩ := exists_fiberPoint_of_mem_fibre B f s U i z hz
      have hpt : (fiberPointLift B f s U.1 U.2 x).base default = i.base z :=
        (congrArg (fun m : s.source ⟶ _ => m.base (default : ↥s.source)) hfl).trans
          (congrArg i.base hrz)
      have hmemO := hO k x (hpt ▸ hiE.subset (Set.mem_range_self z))
      rw [hpt] at hmemO
      exact hmemO
    obtain ⟨V, g, hg⟩ := exists_shrink_mem_of_fibre_subset B f s U i (i ⁻¹ᵁ O k) hcover
    refine ⟨V, g, fun z hz => ?_⟩
    rw [((finiteSupportBaseChange B f F g.1 (E k)).support_eq)] at hz
    obtain ⟨w, hw⟩ := hiE.symm.subset hz
    exact Set.mem_preimage.2 (hw ▸ (hg z w hw.symm : i.base w ∈ (O k : Set _)))
  choose V g hg using hshr
  obtain ⟨W, k, l, hl⟩ := IsCofiltered.wideCospan g
  refine ⟨W, k, fun n z hz => ?_⟩
  have hm : (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map k.1) =
      (SmallEtale.toScheme B X.obj X.property).map ((smallEtaleBaseChange B f).map (l n).1) ≫
      (SmallEtale.toScheme B X.obj X.property).map
        ((smallEtaleBaseChange B f).map (g n).1) := by
    have H : k.1 = (l n).1 ≫ (g n).1 := congrArg Subtype.val (hl n).symm
    rw [H, Functor.map_comp, Functor.map_comp]
  have hz' : ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map k.1)).base z ∈ (E n).1 := by
    rwa [(finiteSupportBaseChange B f F k.1 (E n)).support_eq] at hz
  have hzi : ((SmallEtale.toScheme B X.obj X.property).map
        ((smallEtaleBaseChange B f).map (l n).1)).base z ∈
      (finiteSupportBaseChange B f F (g n).1 (E n)).support.1 := by
    rw [(finiteSupportBaseChange B f F (g n).1 (E n)).support_eq]
    rw [hm, Scheme.Hom.comp_apply] at hz'
    exact hz'
  have H := hg n hzi
  have hgoal : ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map k.1)).base z ∈
      (O n : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1))) := by
    rw [hm]
    exact H
  exact hgoal

/-- **A common neighbourhood with one open support for each of finitely many points of the
geometric fibre.** -/
private theorem exists_common_isOpen_finiteSupports
    (U : (geometricPointFiber B Y.obj Y.property s).Elements)
    (t : Finset (GeometricFiberPoint B f s)) :
    ∃ (V : (geometricPointFiber B Y.obj Y.property s).Elements) (_ : V ⟶ U)
      (E : t → FiniteSupport B f V.1),
      ∀ x : t, IsOpen (E x).1 ∧ ∀ y : GeometricFiberPoint B f s,
        (fiberPointLift B f s V.1 V.2 y).base default ∈ (E x).1 ↔ y = x.1 := by
  classical
  choose W E hO hE using fun x : t => exists_isOpen_finiteSupport_unique_mem B f s x.1
  obtain ⟨V, hV⟩ := IsCofiltered.inf_objs_exists (insert U (Finset.univ.image W))
  let g : ∀ x : t, V ⟶ W x := fun x => (hV (by simp)).some
  refine ⟨V, (hV (Finset.mem_insert_self _ _)).some,
    fun x => ⟨((SmallEtale.toScheme B X.obj X.property).map
        ((smallEtaleBaseChange B f).map (g x).1)).base ⁻¹' (E x).1,
      isFiniteSupport_preimage B f (g x).1 (E x)⟩, fun x => ⟨?_, ?_⟩⟩
  · exact (hO x).preimage ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map (g x).1)).continuous
  · intro y
    exact (fiberPointLift_mem_preimage B f s (g x) (E x).1 y).trans (hE x y)

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The intersection of an eligible support with an eligible support contained in its canonical
open is again eligible: the intersection carries the fibre product of the two subschemes, which is
a closed subscheme of the second and so finite over the étale neighbourhood. -/
private theorem isFiniteSupport_inter
    (U : (geometricPointFiber B Y.obj Y.property s).Elements) (E W : FiniteSupport B f U.1)
    (hW : W.1 ⊆ (finiteSupportOpen B f U.1 E :
      Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1)))) :
    IsFiniteSupport B f U.1 (E.1 ∩ W.1) := by
  obtain ⟨Z, i, hi, hfi, hiE⟩ := E.property
  obtain ⟨T, j, hj, hfj, hjW⟩ := W.property
  have hi' : IsImmersion i := hi
  have hj' : IsImmersion j := hj
  have hfj' : IsFinite (j ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)) := hfj
  obtain ⟨k, hk⟩ : ∃ k : T ⟶ (finiteSupportOpen B f U.1 E).toScheme,
      k ≫ (finiteSupportOpen B f U.1 E).ι = j :=
    ⟨IsOpenImmersion.lift _ j (by rw [Scheme.Opens.range_ι, hjW]; exact hW),
      IsOpenImmersion.lift_fac _ _ _⟩
  have hc : IsClosed (j.base ⁻¹' E.1) := by
    rw [← hk]
    exact (isClosed_supportOpen_preimage B X.obj X.property (baseChange B f U.1) E.1
      (finiteSupport_isLocallyClosed B f U.1 E)).preimage k.continuous
  have hcl : IsClosedImmersion (pullback.snd i j) :=
    IsClosedImmersion.of_isPreimmersion _ (by
      rw [Scheme.Pullback.range_snd, hiE]
      exact hc)
  refine ⟨pullback i j, pullback.snd i j ≫ j, inferInstance, ?_, ?_⟩
  · rw [Category.assoc]
    infer_instance
  · rw [Scheme.Pullback.range_snd_comp, hiE, hjW]

open Classical in
/-- **Cutting a supported section down to a piece of its support.** Let `W` be an eligible support
contained in the canonical open of the eligible support `E` and open in `X_U`. A section supported
on `E` restricts to a section supported on `E ∩ W` whose germ decomposition agrees with that of the
original at the points of the geometric fibre lying in `W` and vanishes at the others. -/
private theorem exists_cut_section
    (U : (geometricPointFiber B Y.obj Y.property s).Elements) (E W : FiniteSupport B f U.1)
    (hopen : IsOpen W.1)
    (hW : W.1 ⊆ (finiteSupportOpen B f U.1 E :
      Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1))))
    (a : (finiteSupportDiagram B f F U.1).obj E) :
    ∃ (T : FiniteSupport B f U.1) (b : (finiteSupportDiagram B f F U.1).obj T),
      T.1 = E.1 ∩ W.1 ∧ ∀ x : GeometricFiberPoint B f s,
        fiberStalkComponent B f s F U.1 U.2 T b x =
          if (fiberPointLift B f s U.1 U.2 x).base default ∈ W.1 then
            fiberStalkComponent B f s F U.1 U.2 E a x else 0 := by
  classical
  let O : ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1)).Opens :=
    ⟨W.1, hopen⟩
  let T : FiniteSupport B f U.1 := ⟨E.1 ∩ W.1, isFiniteSupport_inter B f s U E W hW⟩
  have hOP : O ≤ finiteSupportOpen B f U.1 E := hW
  let k := openObjectHomOfLE B X.obj X.property (baseChange B f U.1) hOP
  have hk : (SmallEtale.toScheme B X.obj X.property).map k ≫
      (finiteSupportOpen B f U.1 E).ι = O.ι := by
    rw [openObjectHomOfLE_map, Scheme.homOfLE_ι]
  have hc : IsClosed (O.ι.base ⁻¹' T.1) := by
    have he : O.ι.base ⁻¹' T.1 = O.ι.base ⁻¹' E.1 := by
      ext z
      exact and_iff_left z.property
    rw [he, ← hk]
    exact (isClosed_supportOpen_preimage B X.obj X.property (baseChange B f U.1) E.1
      (finiteSupport_isLocallyClosed B f U.1 E)).preimage
      ((SmallEtale.toScheme B X.obj X.property).map k).continuous
  have hTO : T.1 ⊆ (O : Set ((SmallEtale.toScheme B X.obj X.property).obj
      (baseChange B f U.1))) := fun _ h => h.2
  let aO : supportedSectionsOnOpen B X.obj X.property F (baseChange B f U.1) T.1 O :=
    ⟨F.obj.map k.op a.val, by
      intro z hz
      refine ⟨?_, z.property⟩
      have hz' := a.property
        (supportSection_restrict_subset_preimage B X.obj X.property F _ _ k a.val hz)
      have hkz : ((SmallEtale.toScheme B X.obj X.property).map k ≫
          (finiteSupportOpen B f U.1 E).ι).base z = O.ι.base z :=
        congrArg (fun m : O.toScheme ⟶ _ => m.base z) hk
      exact hkz ▸ hz'⟩
  let e := supportedSectionsOpenEquiv B X.obj X.property F (baseChange B f U.1) T.1
    (finiteSupport_isLocallyClosed B f U.1 T) O hTO hc
  let b := e.symm aO
  have hOQ : O ≤ finiteSupportOpen B f U.1 T := by
    intro z hz
    show z ∈ coborder T.1
    rw [mem_coborder_iff_imp]
    intro hzT
    have he := O.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      O.ι.continuous T.1
    have hmem : (⟨z, hz⟩ : O.toScheme) ∈ closure (O.ι.base ⁻¹' T.1) := by
      rwa [← he]
    rwa [hc.closure_eq] at hmem
  let l := openObjectHomOfLE B X.obj X.property (baseChange B f U.1) hOQ
  have hl : (SmallEtale.toScheme B X.obj X.property).map l ≫
      (finiteSupportOpen B f U.1 T).ι = O.ι := by
    rw [openObjectHomOfLE_map, Scheme.homOfLE_ι]
  have hb : F.obj.map l.op b.val = F.obj.map k.op a.val := by
    have H := locallyClosedSupportEquiv_restrict B X.obj X.property F (baseChange B f U.1) T.1
      (finiteSupportOpen B f U.1 T) O
      (subset_supportOpen B X.obj X.property (baseChange B f U.1) T.1
        (finiteSupport_isLocallyClosed B f U.1 T)) hTO
      (isClosed_supportOpen_preimage B X.obj X.property (baseChange B f U.1) T.1
        (finiteSupport_isLocallyClosed B f U.1 T)) hc hOQ b
    exact H.symm.trans (congrArg Subtype.val (e.apply_symm_apply aO))
  refine ⟨T, b, rfl, fun x => ?_⟩
  by_cases hx : (fiberPointLift B f s U.1 U.2 x).base default ∈ W.1
  · rw [ite_eq_left hx]
    have hxO : (fiberPointLift B f s U.1 U.2 x).base default ∈
        (O : Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1))) := hx
    let N : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).Elements :=
      ⟨openObject B X.obj X.property (baseChange B f U.1) O,
        openObjectLift B X.obj X.property (x.toGeometricPoint B f s) (baseChange B f U.1)
          (fiberPointElement B f s U.1 U.2 x) O hxO⟩
    have hNι : N.2.1 ≫ O.ι = fiberPointLift B f s U.1 U.2 x :=
      openObjectLift_comp_ι B X.obj X.property (x.toGeometricPoint B f s) (baseChange B f U.1)
        (fiberPointElement B f s U.1 U.2 x) O hxO
    have hUT : N.2.1 ≫ (SmallEtale.toScheme B X.obj X.property).map l ≫
        (finiteSupportOpen B f U.1 T).ι ≫
          B.inclusion.map (pullback.fst U.1.obj.hom f) = U.2.1 :=
      calc N.2.1 ≫ (SmallEtale.toScheme B X.obj X.property).map l ≫
            (finiteSupportOpen B f U.1 T).ι ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)
          = (N.2.1 ≫ (SmallEtale.toScheme B X.obj X.property).map l ≫
              (finiteSupportOpen B f U.1 T).ι) ≫
              B.inclusion.map (pullback.fst U.1.obj.hom f) := by simp only [Category.assoc]
        _ = (N.2.1 ≫ O.ι) ≫ B.inclusion.map (pullback.fst U.1.obj.hom f) :=
              congrArg (fun z => (N.2.1 ≫ z) ≫
                B.inclusion.map (pullback.fst U.1.obj.hom f)) hl
        _ = fiberPointLift B f s U.1 U.2 x ≫ B.inclusion.map (pullback.fst U.1.obj.hom f) :=
              congrArg (fun z => z ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)) hNι
        _ = U.2.1 := fiberPointLift_comp_fst B f s U.1 U.2 x
    have hXT : N.2.1 ≫ (SmallEtale.toScheme B X.obj X.property).map l ≫
        (finiteSupportOpen B f U.1 T).ι ≫
          B.inclusion.map (pullback.snd U.1.obj.hom f) = x.1 :=
      calc N.2.1 ≫ (SmallEtale.toScheme B X.obj X.property).map l ≫
            (finiteSupportOpen B f U.1 T).ι ≫ B.inclusion.map (pullback.snd U.1.obj.hom f)
          = (N.2.1 ≫ (SmallEtale.toScheme B X.obj X.property).map l ≫
              (finiteSupportOpen B f U.1 T).ι) ≫
              B.inclusion.map (pullback.snd U.1.obj.hom f) := by simp only [Category.assoc]
        _ = (N.2.1 ≫ O.ι) ≫ B.inclusion.map (pullback.snd U.1.obj.hom f) :=
              congrArg (fun z => (N.2.1 ≫ z) ≫
                B.inclusion.map (pullback.snd U.1.obj.hom f)) hl
        _ = fiberPointLift B f s U.1 U.2 x ≫ B.inclusion.map (pullback.snd U.1.obj.hom f) :=
              congrArg (fun z => z ≫ B.inclusion.map (pullback.snd U.1.obj.hom f)) hNι
        _ = x.1 := fiberPointLift_comp_snd B f s U.1 U.2 x
    have hUE : N.2.1 ≫ (SmallEtale.toScheme B X.obj X.property).map k ≫
        (finiteSupportOpen B f U.1 E).ι ≫
          B.inclusion.map (pullback.fst U.1.obj.hom f) = U.2.1 :=
      calc N.2.1 ≫ (SmallEtale.toScheme B X.obj X.property).map k ≫
            (finiteSupportOpen B f U.1 E).ι ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)
          = (N.2.1 ≫ (SmallEtale.toScheme B X.obj X.property).map k ≫
              (finiteSupportOpen B f U.1 E).ι) ≫
              B.inclusion.map (pullback.fst U.1.obj.hom f) := by simp only [Category.assoc]
        _ = (N.2.1 ≫ O.ι) ≫ B.inclusion.map (pullback.fst U.1.obj.hom f) :=
              congrArg (fun z => (N.2.1 ≫ z) ≫
                B.inclusion.map (pullback.fst U.1.obj.hom f)) hk
        _ = fiberPointLift B f s U.1 U.2 x ≫ B.inclusion.map (pullback.fst U.1.obj.hom f) :=
              congrArg (fun z => z ≫ B.inclusion.map (pullback.fst U.1.obj.hom f)) hNι
        _ = U.2.1 := fiberPointLift_comp_fst B f s U.1 U.2 x
    have hXE : N.2.1 ≫ (SmallEtale.toScheme B X.obj X.property).map k ≫
        (finiteSupportOpen B f U.1 E).ι ≫
          B.inclusion.map (pullback.snd U.1.obj.hom f) = x.1 :=
      calc N.2.1 ≫ (SmallEtale.toScheme B X.obj X.property).map k ≫
            (finiteSupportOpen B f U.1 E).ι ≫ B.inclusion.map (pullback.snd U.1.obj.hom f)
          = (N.2.1 ≫ (SmallEtale.toScheme B X.obj X.property).map k ≫
              (finiteSupportOpen B f U.1 E).ι) ≫
              B.inclusion.map (pullback.snd U.1.obj.hom f) := by simp only [Category.assoc]
        _ = (N.2.1 ≫ O.ι) ≫ B.inclusion.map (pullback.snd U.1.obj.hom f) :=
              congrArg (fun z => (N.2.1 ≫ z) ≫
                B.inclusion.map (pullback.snd U.1.obj.hom f)) hk
        _ = fiberPointLift B f s U.1 U.2 x ≫ B.inclusion.map (pullback.snd U.1.obj.hom f) :=
              congrArg (fun z => z ≫ B.inclusion.map (pullback.snd U.1.obj.hom f)) hNι
        _ = x.1 := fiberPointLift_comp_snd B f s U.1 U.2 x
    rw [fiberStalkComponent_germ B f s F x U T N l hUT hXT b,
      fiberStalkComponent_germ B f s F x U E N k hUE hXE a]
    exact congrArg (colimit.ι (etaleStalkDiagram B X.obj X.property
      (x.toGeometricPoint B f s) F.obj) (op N)) hb
  · rw [ite_eq_right hx]
    exact fiberStalkComponent_eq_zero_of_notMem B f s F U.1 U.2 T b x fun h => hx h.2

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The inverse image of the canonical open of a support lies in the canonical open of the inverse
image support. -/
private theorem preimage_finiteSupportOpen_subset
    {U V : (geometricPointFiber B Y.obj Y.property s).Elements} (g : V ⟶ U)
    (E : FiniteSupport B f U.1) :
    ((SmallEtale.toScheme B X.obj X.property).map
        ((smallEtaleBaseChange B f).map g.1)).base ⁻¹'
      (finiteSupportOpen B f U.1 E :
        Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1))) ⊆
      (finiteSupportOpen B f V.1 (finiteSupportBaseChange B f F g.1 E).support :
        Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f V.1))) := by
  show _ ⊆ coborder _
  rw [(finiteSupportBaseChange B f F g.1 E).support_eq]
  exact ((SmallEtale.toScheme B X.obj X.property).map
    ((smallEtaleBaseChange B f).map g.1)).continuous.preimage_coborder_subset E.1

/-- A finite family of supported sections whose germ decompositions sum to zero, and whose
supports are met by pairwise distinct parts of the geometric fibre, has all its germs zero. -/
private theorem stalkGenerator_sum_eq_zero_of_disjoint
    (U : (geometricPointFiber B Y.obj Y.property s).Elements)
    {I : Type*} (t : Finset I) (E : I → FiniteSupport B f U.1)
    (a : ∀ i, (finiteSupportDiagram B f F U.1).obj (E i))
    (hdisj : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → ∀ y : GeometricFiberPoint B f s,
      (fiberPointLift B f s U.1 U.2 y).base default ∈ (E i).1 →
        (fiberPointLift B f s U.1 U.2 y).base default ∉ (E j).1)
    (ha : ∑ i ∈ t, fiberStalkSum B f s F U.1 U.2 (E i) (a i) = 0) :
    ∑ i ∈ t, (stalkGenerator B f s F hsmall U (E i)) (a i) = 0 := by
  classical
  refine Finset.sum_eq_zero fun i hi => ?_
  refine stalkGenerator_eq_zero B f s F hsmall U (E i) (a i) (DFinsupp.ext fun y => ?_)
  by_cases hy : (fiberPointLift B f s U.1 U.2 y).base default ∈ (E i).1
  · have H := congrArg (fun z : fiberStalks B f s F => z y) ha
    simp only [DirectSum.zero_apply] at H
    have hsum : (∑ j ∈ t, fiberStalkSum B f s F U.1 U.2 (E j) (a j)) y =
        (fiberStalkSum B f s F U.1 U.2 (E i) (a i)) y := by
      rw [DFinsupp.finsetSum_apply]
      refine Finset.sum_eq_single i (fun j hj hji => ?_) (fun h => (h hi).elim)
      exact fiberStalkComponent_eq_zero_of_notMem B f s F U.1 U.2 (E j) (a j) y
        (hdisj i hi j hj (Ne.symm hji) y hy)
    exact hsum.symm.trans H
  · exact fiberStalkComponent_eq_zero_of_notMem B f s F U.1 U.2 (E i) (a i) y hy

/-- **The injectivity argument for a family of supports cut by open supports.** A finite family of
supported sections over one étale neighbourhood whose germ decompositions sum to zero has germs
summing to zero in the stalk, provided the geometric fibre meets the supports only in the points
singled out by a finite family of open supports. -/
private theorem stalkGenerator_sum_eq_zero_of_isOpen_supports
    (U : (geometricPointFiber B Y.obj Y.property s).Elements)
    {I J : Type*} [Fintype I] [Finite J]
    (E : I → FiniteSupport B f U.1)
    (a : ∀ i, (finiteSupportDiagram B f F U.1).obj (E i))
    (W : J → FiniteSupport B f U.1)
    (x : J → GeometricFiberPoint B f s) (hx : Function.Injective x)
    (hW : ∀ j, IsOpen (W j).1 ∧ ∀ y : GeometricFiberPoint B f s,
      (fiberPointLift B f s U.1 U.2 y).base default ∈ (W j).1 ↔ y = x j)
    (hcover : ∀ (i : I) (y : GeometricFiberPoint B f s),
      (fiberPointLift B f s U.1 U.2 y).base default ∈ (E i).1 → ∃ j, y = x j)
    (hsub : ∀ (i : I) (j : J),
      (fiberPointLift B f s U.1 U.2 (x j)).base default ∈ (E i).1 →
        (W j).1 ⊆ (finiteSupportOpen B f U.1 (E i) :
          Set ((SmallEtale.toScheme B X.obj X.property).obj (baseChange B f U.1))))
    (ha : ∑ i, fiberStalkSum B f s F U.1 U.2 (E i) (a i) = 0) :
    ∑ i, (stalkGenerator B f s F hsmall U (E i)) (a i) = 0 := by
  classical
  let _ := Fintype.ofFinite J
  choose T b hT hb using fun (i : I)
    (j : {j : J // (fiberPointLift B f s U.1 U.2 (x j)).base default ∈ (E i).1}) =>
    exists_cut_section B f s F U (E i) (W j.1) (hW j.1).1 (hsub i j.1 j.2) (a i)
  have hTE : ∀ (i : I) (j : {j : J //
      (fiberPointLift B f s U.1 U.2 (x j)).base default ∈ (E i).1}), T i j ≤ E i := by
    intro i j
    show (T i j).1 ⊆ (E i).1
    rw [hT]
    exact Set.inter_subset_left
  have hTW : ∀ (i : I) (j : {j : J //
      (fiberPointLift B f s U.1 U.2 (x j)).base default ∈ (E i).1}), T i j ≤ W j.1 := by
    intro i j
    show (T i j).1 ⊆ (W j.1).1
    rw [hT]
    exact Set.inter_subset_right
  let d : ∀ (i : I) (j : J), (finiteSupportDiagram B f F U.1).obj (E i) := fun i j =>
    if h : (fiberPointLift B f s U.1 U.2 (x j)).base default ∈ (E i).1 then
      ((finiteSupportDiagram B f F U.1).map (homOfLE (hTE i ⟨j, h⟩))) (b i ⟨j, h⟩) else 0
  let c : ∀ (i : I) (j : J), (finiteSupportDiagram B f F U.1).obj (W j) := fun i j =>
    if h : (fiberPointLift B f s U.1 U.2 (x j)).base default ∈ (E i).1 then
      ((finiteSupportDiagram B f F U.1).map (homOfLE (hTW i ⟨j, h⟩))) (b i ⟨j, h⟩) else 0
  have hd_pos : ∀ (i : I) (j : J)
      (h : (fiberPointLift B f s U.1 U.2 (x j)).base default ∈ (E i).1),
      d i j = ((finiteSupportDiagram B f F U.1).map (homOfLE (hTE i ⟨j, h⟩))) (b i ⟨j, h⟩) :=
    fun i j h => dite_eq_left h
  have hd_neg : ∀ (i : I) (j : J),
      ¬ (fiberPointLift B f s U.1 U.2 (x j)).base default ∈ (E i).1 → d i j = 0 :=
    fun i j h => dite_eq_right h
  have hc_pos : ∀ (i : I) (j : J)
      (h : (fiberPointLift B f s U.1 U.2 (x j)).base default ∈ (E i).1),
      c i j = ((finiteSupportDiagram B f F U.1).map (homOfLE (hTW i ⟨j, h⟩))) (b i ⟨j, h⟩) :=
    fun i j h => dite_eq_left h
  have hc_neg : ∀ (i : I) (j : J),
      ¬ (fiberPointLift B f s U.1 U.2 (x j)).base default ∈ (E i).1 → c i j = 0 :=
    fun i j h => dite_eq_right h
  have hdc : ∀ (i : I) (j : J), (stalkGenerator B f s F hsmall U (E i)) (d i j) =
      (stalkGenerator B f s F hsmall U (W j)) (c i j) := by
    intro i j
    by_cases h : (fiberPointLift B f s U.1 U.2 (x j)).base default ∈ (E i).1
    · rw [hd_pos i j h, hc_pos i j h]
      exact (ConcreteCategory.congr_hom (stalkGenerator_transition B f s F hsmall U
            (T i ⟨j, h⟩) (E i) (hTE i ⟨j, h⟩)) (b i ⟨j, h⟩)).trans
        (ConcreteCategory.congr_hom (stalkGenerator_transition B f s F hsmall U
            (T i ⟨j, h⟩) (W j) (hTW i ⟨j, h⟩)) (b i ⟨j, h⟩)).symm
    · rw [hd_neg i j h, hc_neg i j h, map_zero, map_zero]
  have hd : ∀ (i : I) (j : J) (y : GeometricFiberPoint B f s),
      (fiberStalkSum B f s F U.1 U.2 (E i) (d i j)) y =
        if y = x j then (fiberStalkSum B f s F U.1 U.2 (E i) (a i)) y else 0 := by
    intro i j y
    by_cases h : (fiberPointLift B f s U.1 U.2 (x j)).base default ∈ (E i).1
    · rw [hd_pos i j h]
      refine ((fiberStalkComponent_supportedSectionsMap B f s F U.1 U.2 (T i ⟨j, h⟩) (E i)
        (hTE i ⟨j, h⟩) (b i ⟨j, h⟩) y).trans (hb i ⟨j, h⟩ y)).trans ?_
      exact if_congr ((hW j).2 y) rfl rfl
    · rw [hd_neg i j h]
      refine (fiberStalkComponent_zero B f s F U.1 U.2 (E i) y).trans ?_
      split_ifs with hy
      · subst hy
        exact (fiberStalkComponent_eq_zero_of_notMem B f s F U.1 U.2 (E i) (a i) (x j) h).symm
      · rfl
  have hdi : ∀ i : I, fiberStalkSum B f s F U.1 U.2 (E i) (∑ j, d i j) =
      fiberStalkSum B f s F U.1 U.2 (E i) (a i) := by
    intro i
    have hmap : fiberStalkSum B f s F U.1 U.2 (E i) (∑ j, d i j) =
        ∑ j, fiberStalkSum B f s F U.1 U.2 (E i) (d i j) :=
      map_sum (fiberStalkHom B f s F U.1 U.2 (E i)).hom _ _
    refine DFinsupp.ext fun y => ?_
    rw [hmap, DFinsupp.finsetSum_apply, Finset.sum_congr rfl fun j _ => hd i j y]
    by_cases hy : (fiberPointLift B f s U.1 U.2 y).base default ∈ (E i).1
    · obtain ⟨j₀, rfl⟩ := hcover i y hy
      refine (Finset.sum_eq_single j₀
        (fun j _ hj => ite_eq_right fun h => hj (hx h.symm)) ?_).trans ?_
      · exact fun h => (h (Finset.mem_univ j₀)).elim
      · exact ite_eq_left rfl
    · have hz : (fiberStalkSum B f s F U.1 U.2 (E i) (a i)) y = 0 :=
        fiberStalkComponent_eq_zero_of_notMem B f s F U.1 U.2 (E i) (a i) y hy
      rw [hz]
      refine Finset.sum_eq_zero fun j _ => ?_
      split_ifs with hyj
      · rfl
      · rfl
  have hi : ∀ i : I, (stalkGenerator B f s F hsmall U (E i)) (a i) =
      ∑ j, (stalkGenerator B f s F hsmall U (W j)) (c i j) := by
    intro i
    have hms : (stalkGenerator B f s F hsmall U (E i)) (∑ j, d i j) =
        ∑ j, (stalkGenerator B f s F hsmall U (E i)) (d i j) :=
      map_sum (stalkGenerator B f s F hsmall U (E i)).hom _ _
    rw [← stalkGenerator_eq_of_fiberStalkSum_eq B f s F hsmall U (E i) (∑ j, d i j) (a i)
      (hdi i), hms]
    exact Finset.sum_congr rfl fun j _ => hdc i j
  have heq : ∑ i, (stalkGenerator B f s F hsmall U (E i)) (a i) =
      ∑ j, (stalkGenerator B f s F hsmall U (W j)) (∑ i, c i j) := by
    have h2 : ∀ j : J, (stalkGenerator B f s F hsmall U (W j)) (∑ i, c i j) =
        ∑ i, (stalkGenerator B f s F hsmall U (W j)) (c i j) :=
      fun j => map_sum (stalkGenerator B f s F hsmall U (W j)).hom _ _
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => h2 j,
      Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hi i]
    exact Finset.sum_comm
  rw [heq]
  refine stalkGenerator_sum_eq_zero_of_disjoint B f s F hsmall U Finset.univ W
    (fun j => ∑ i, c i j) (fun j _ j' _ hjj' y hy hy' => ?_) ?_
  · exact hjj' (hx ((((hW j).2 y).1 hy).symm.trans (((hW j').2 y).1 hy')))
  · refine (finiteSupportStalkToFiberStalks_sum_stalkGenerator B f s F hsmall U W
      (fun j => ∑ i, c i j)).symm.trans ?_
    rw [← heq]
    exact (finiteSupportStalkToFiberStalks_sum_stalkGenerator B f s F hsmall U E a).trans ha

/-- **The injectivity argument.** A finite family of supported sections over one étale
neighbourhood whose germ decompositions sum to zero has germs summing to zero in the stalk: the
geometric fibre meets the supports in finitely many points, and over a smaller neighbourhood each
of those points is isolated by an open support. -/
private theorem stalkGenerator_sum_eq_zero
    (U : (geometricPointFiber B Y.obj Y.property s).Elements)
    {I : Type*} [Fintype I] (E : I → FiniteSupport B f U.1)
    (a : ∀ i, (finiteSupportDiagram B f F U.1).obj (E i))
    (ha : ∑ i, fiberStalkSum B f s F U.1 U.2 (E i) (a i) = 0) :
    ∑ i, (stalkGenerator B f s F hsmall U (E i)) (a i) = 0 := by
  classical
  have hfin : ∀ i : I, Set.Finite {y : GeometricFiberPoint B f s |
      (fiberPointLift B f s U.1 U.2 y).base default ∈ (E i).1} :=
    fun i => finite_mem_of_isFiniteSupport B f s U.1 U.2 (E i)
  let t : Finset (GeometricFiberPoint B f s) := Finset.univ.biUnion fun i => (hfin i).toFinset
  have ht : ∀ (i : I) (y : GeometricFiberPoint B f s),
      (fiberPointLift B f s U.1 U.2 y).base default ∈ (E i).1 → y ∈ t :=
    fun i _ hy => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, (hfin i).mem_toFinset.mpr hy⟩
  obtain ⟨V, g, W, hW⟩ := exists_common_isOpen_finiteSupports B f s U t
  let E' : I → FiniteSupport B f V.1 :=
    fun i => (finiteSupportBaseChange B f F g.1 (E i)).support
  let a' : ∀ i, (finiteSupportDiagram B f F V.1).obj (E' i) :=
    fun i => (finiteSupportBaseChange B f F g.1 (E i)).sectionsMap (a i)
  obtain ⟨N, k, hk⟩ := exists_shrink_supports_subset_opens B f s F V
    (fun p : {p : I × t // (fiberPointLift B f s V.1 V.2 p.2.1).base default ∈ (E' p.1).1} =>
      W p.1.2)
    (fun p => finiteSupportOpen B f V.1 (E' p.1.1)) (by
      intro p y hy
      obtain rfl := ((hW p.1.2).2 y).mp hy
      exact subset_supportOpen B X.obj X.property (baseChange B f V.1) (E' p.1.1).1
        (finiteSupport_isLocallyClosed B f V.1 (E' p.1.1)) p.2)
  let e : ∀ i : I, FiniteSupportBaseChange B f F k.1 (E' i) :=
    fun i => finiteSupportBaseChange B f F k.1 (E' i)
  let w : ∀ j : t, FiniteSupportBaseChange B f F k.1 (W j) :=
    fun j => finiteSupportBaseChange B f F k.1 (W j)
  have hsum : ∑ i, (stalkGenerator B f s F hsmall U (E i)) (a i) =
      ∑ i, (stalkGenerator B f s F hsmall N (e i).support) ((e i).sectionsMap (a' i)) :=
    Finset.sum_congr rfl fun i _ => (ConcreteCategory.congr_hom
        (stalkGenerator_baseChange B f s F hsmall g (E i)) (a i)).symm.trans
      (ConcreteCategory.congr_hom
        (stalkGenerator_baseChange B f s F hsmall k (E' i)) (a' i)).symm
  rw [hsum]
  refine stalkGenerator_sum_eq_zero_of_isOpen_supports B f s F hsmall N
    (fun i => (e i).support) (fun i => (e i).sectionsMap (a' i))
    (fun j => (w j).support) (fun j : t => j.1) Subtype.val_injective
    (fun j => ⟨?_, ?_⟩) ?_ ?_ ?_
  · rw [(w j).support_eq]
    exact (hW j).1.preimage ((SmallEtale.toScheme B X.obj X.property).map
      ((smallEtaleBaseChange B f).map k.1)).continuous
  · intro y
    rw [(w j).support_eq]
    exact (fiberPointLift_mem_preimage B f s k (W j).1 y).trans ((hW j).2 y)
  · intro i y hy
    rw [(e i).support_eq] at hy
    have hy' := (fiberPointLift_mem_preimage B f s k (E' i).1 y).mp hy
    rw [(finiteSupportBaseChange B f F g.1 (E i)).support_eq] at hy'
    exact ⟨⟨y, ht i y ((fiberPointLift_mem_preimage B f s g (E i).1 y).mp hy')⟩, rfl⟩
  · intro i j hj
    rw [(e i).support_eq] at hj
    have hj' := (fiberPointLift_mem_preimage B f s k (E' i).1 j.1).mp hj
    exact (hk ⟨⟨i, j⟩, hj'⟩).trans (preimage_finiteSupportOpen_subset B f s F k (E' i))
  · have he : ∀ i : I, fiberStalkSum B f s F N.1 N.2 (e i).support
        ((e i).sectionsMap (a' i)) = fiberStalkSum B f s F U.1 U.2 (E i) (a i) := by
      intro i
      refine DFinsupp.ext fun y => ?_
      exact (fiberStalkComponent_baseChange B f s F V.1 N.1 k.1 V.2 N.2 k.2 (E' i)
          (e i) (a' i) y).trans
        (fiberStalkComponent_baseChange B f s F U.1 V.1 g.1 U.2 V.2 g.2 (E i)
          (finiteSupportBaseChange B f F g.1 (E i)) (a i) y)
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => he i]
    exact ha

end Generators

section Iso

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (s : GeometricPoint Y.obj)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max u v})
  (hsmall : ∀ V : SmallEtale B Y.obj Y.property, Small.{max u v} (FiniteSupport B f V))

/-- **The injectivity half of Stacks 0F6P.** The germ decomposition map
`(f_{p!}F)_ȳ ⟶ ⊕_{f(x̄) = ȳ} F_x̄` is injective.

An element of the stalk is a finite sum of germs of supported sections over one étale
neighbourhood of `ȳ`, and such a sum of germs vanishes as soon as the family of germ
decompositions does. -/
@[stacks 0F6P "injectivity of the germ decomposition"]
public theorem injective_finiteSupportStalkToFiberStalks :
    Function.Injective (finiteSupportStalkToFiberStalks B f s F hsmall) := by
  classical
  have hinj : Function.Injective (finiteSupportStalkToFiberStalks B f s F hsmall).hom := by
    refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    obtain ⟨U, l, hl⟩ := exists_listSum_generators_eq_etaleStalk B f s F hsmall z
    have hr : z = ∑ i : Fin l.length, (stalkGenerator B f s F hsmall U l[i].1) l[i].2 := by
      rw [← hl, ← List.ofFn_getElem_eq_map, List.sum_ofFn]
      rfl
    rw [hr] at hz ⊢
    refine stalkGenerator_sum_eq_zero B f s F hsmall U (fun i : Fin l.length => l[i].1)
      (fun i => l[i].2) ?_
    refine (finiteSupportStalkToFiberStalks_sum_stalkGenerator B f s F hsmall U _ _).symm.trans ?_
    exact hz
  exact hinj

/-- The germ decomposition map of the stalk of the finite-support direct image is an
isomorphism. -/
public instance isIso_finiteSupportStalkToFiberStalks :
    IsIso (finiteSupportStalkToFiberStalks B f s F hsmall) := by
  have hmono : Mono (finiteSupportStalkToFiberStalks B f s F hsmall) :=
    (AddCommGrpCat.mono_iff_injective _).2
      (injective_finiteSupportStalkToFiberStalks B f s F hsmall)
  have hepi : Epi (finiteSupportStalkToFiberStalks B f s F hsmall) :=
    (AddCommGrpCat.epi_iff_surjective _).2
      (surjective_finiteSupportStalkToFiberStalks B f s F hsmall)
  exact isIso_of_mono_of_epi _

/-- **Stacks 0F6P.** For a locally quasi-finite morphism `f : X ⟶ Y`, the stalk of the
finite-support direct image `f_{p!}F` at a geometric point `ȳ` of `Y` is the direct sum of the
stalks of `F` over the geometric points of `X` lying over `ȳ`:
`(f_{p!}F)_ȳ ≅ ⊕_{f(x̄) = ȳ} F_x̄`. -/
@[stacks 0F6P "the germ decomposition is an isomorphism"]
public def finiteSupportStalkIso :
    etaleStalk B Y.obj Y.property s ((finiteSupportPushforward B f hsmall).1.obj F) ≅
      AddCommGrpCat.of (fiberStalks B f s F) :=
  asIso (finiteSupportStalkToFiberStalks B f s F hsmall)

/-- The forward direction of the germ decomposition isomorphism is the canonical map of
`StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalk`, so its germ characterization and its
naturality in the sheaf describe the isomorphism. -/
@[simp]
public lemma finiteSupportStalkIso_hom :
    (finiteSupportStalkIso B f s F hsmall).hom =
      finiteSupportStalkToFiberStalks B f s F hsmall := rfl

end Iso

end SmallEtale

end AlgebraicGeometry

end
