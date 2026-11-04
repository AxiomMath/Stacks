module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalk
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.ConstantSheafSections
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcSmallEtaleSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall

/-!
# The constant abelian sheaf on the small étale site of a chosen big étale site

Let `B` be a big étale site containing a scheme `S` and let `A` be an abstract abelian group.
The constant sheaf of abelian groups with value `A` on the small étale site `SmallEtale B S hS`
has as its sections over an object `V` of that site the group of Zariski locally constant
`A`-valued maps on `V`, and its stalk at a geometric point of `S` is `A` itself.

## Main definitions

* `AlgebraicGeometry.locallyConstantMapsAbSmallEtale` — the presheaf of abelian groups on the
  small étale site sending an object to the group of locally constant `A`-valued maps on its
  underlying scheme, and `AlgebraicGeometry.locallyConstantSheafAb` the corresponding sheaf.
* `AlgebraicGeometry.constantToLocallyConstantMapsAb` — the comparison from the constant
  presheaf, sending `a : A` to the constant map with value `a`.
* `AlgebraicGeometry.constantSheafIsoLocallyConstantMapsAb_smallEtale` — the identification of
  the constant abelian sheaf with the locally constant maps, in the category of sheaves, with
  `AlgebraicGeometry.constantSheafIsoLocallyConstantMapsAb_smallEtale_presheaf` its corollary
  for the underlying presheaves.
* `AlgebraicGeometry.etaleStalkLocallyConstantMapsAbCocone` and
  `AlgebraicGeometry.etaleStalkLocallyConstantMapsAbHom` — evaluation of a locally constant map
  at the image of a chosen lift of a geometric point, as a cocone on the stalk diagram and as
  the induced map out of the stalk, with
  `AlgebraicGeometry.etaleStalkLocallyConstantMapsAbInv` the inverse map.
* `AlgebraicGeometry.etaleStalkLocallyConstantMapsAbIso` — the resulting identification of the
  stalk with `A`.

## Main results

* `AlgebraicGeometry.locallyConstantMapsAb_isSheaf_smallEtale` is the sheaf condition, obtained
  from the fpqc sheaf condition on schemes along the continuous functor to the schemes over `S`.
* `AlgebraicGeometry.constantToLocallyConstantMapsAb_isLocallyInjective` and
  `AlgebraicGeometry.constantToLocallyConstantMapsAb_isLocallySurjective` make the comparison
  from the constant presheaf locally bijective, hence an isomorphism after sheafification.
* `AlgebraicGeometry.constantSheafIsoLocallyConstantMapsAb_smallEtale_unit` fixes the
  identification by its action on constant sections, so that it is the comparison map of the
  constant presheaf and not merely some isomorphism.
* `AlgebraicGeometry.smallEtaleTopology_bot_mem` covers an object with empty underlying scheme
  by the empty family, and
  `AlgebraicGeometry.smallEtaleTopology_wEqualsLocallyBijective_addCommGrpCat` supplies the
  local-bijectivity criterion at the coefficient universe used here.
* `AlgebraicGeometry.geometricPointFiber_final_eq` identifies the unique lift of a geometric
  point to the final object of the site.
* `AlgebraicGeometry.etaleGerm_const_eq` identifies the germ of a locally constant map with the
  germ over the final object of the constant map carrying its value at the geometric point.
* `AlgebraicGeometry.etaleStalkLocallyConstantMapsAbIso_etaleGerm` and
  `AlgebraicGeometry.etaleStalkLocallyConstantMapsAbIso_inv_const` compute the identification
  of the stalk on germs and on constants.

## Implementation notes

The sheaf condition travels from schemes to the small étale site along the two continuous
functors `SmallEtale B S hS ⥤ Over S ⥤ Scheme`, the small étale topology being coarser than
the fpqc topology restricted to the schemes over `S`; this is the same route as the
`Type`-valued statement `AlgebraicGeometry.locallyConstantMaps_isSheaf_smallEtale`, taken with
abelian coefficients rather than after applying a forgetful functor, so that no multiplicative
group structure has to be invented on `A`. In the other direction an arbitrary open cover of an
object of the site is refined by a covering family of the site, which is
`AlgebraicGeometry.smallEtale_openCoverData`.

The stalk is computed directly rather than through the identification with the constant sheaf:
the cocone evaluating a locally constant map at the image of the chosen lift of the geometric
point is defined on the nose, and its inverse sends `a : A` to the germ over the final object
`S / S` of the constant map with value `a`. That these are mutually inverse rests on
`AlgebraicGeometry.etaleGerm_const_eq`, whose proof is the only geometric step: a locally
constant map agrees with the constant map carrying its value at the geometric point on a
Zariski open containing the image of the lift, and restricting to that open does not change a
germ.

The coefficient group lives in the universe `max (u + 1) v` in which this library computes
étale cohomology, so that the identifications apply to the coefficients of the finite-support
direct image and of the étale cohomology of a constant sheaf.

## References

* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Locally constant maps as an abelian sheaf -/

/-- The presheaf of abelian groups on the small étale site of `S` inside `B` sending an object
`V` to the group of locally constant `A`-valued maps on the scheme underlying `V`. -/
public abbrev locallyConstantMapsAbSmallEtale (A : Type (max (u + 1) v)) [AddCommGroup A] :
    (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v} :=
  (SmallEtale.toScheme B S hS).op ⋙ locallyConstantMapsAb.{u, max (u + 1) v} A

/-- Locally constant `A`-valued maps form a sheaf of abelian groups on the small étale site of
`S` inside `B`: they are an fpqc sheaf on schemes, and the canonical functor to the schemes
over `S` is continuous for the fpqc topology. -/
public theorem locallyConstantMapsAb_isSheaf_smallEtale (A : Type (max (u + 1) v))
    [AddCommGroup A] :
    Presheaf.IsSheaf (SmallEtale.topology B S hS)
      (locallyConstantMapsAbSmallEtale.{u, v} B S hS A) :=
  (SmallEtale.toOver B S hS).op_comp_isSheaf_of_isSheaf (SmallEtale.topology B S hS)
    (Scheme.fpqcTopology.{u}.over S) _
    ((Over.forget S).op_comp_isSheaf_of_isSheaf (Scheme.fpqcTopology.{u}.over S)
      Scheme.fpqcTopology.{u} _ (locallyConstantMapsAb_isSheaf_fpqc.{u, v} A))

/-- The sheaf of abelian groups of locally constant `A`-valued maps on the small étale site of
`S` inside `B`. -/
public def locallyConstantSheafAb (A : Type (max (u + 1) v)) [AddCommGroup A] :
    Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v} :=
  ⟨locallyConstantMapsAbSmallEtale.{u, v} B S hS A,
    locallyConstantMapsAb_isSheaf_smallEtale.{u, v} B S hS A⟩

/-- An object of the small étale site with empty underlying scheme is covered by the empty
family. -/
public theorem smallEtaleTopology_bot_mem {T : SmallEtale B S hS}
    (hT : IsEmpty ((SmallEtale.toScheme B S hS).obj T)) :
    (⊥ : Sieve T) ∈ SmallEtale.topology B S hS T :=
  openCoverData_bottom (SmallEtale.toScheme B S hS) (SmallEtale.topology B S hS)
    (smallEtale_openCoverData B S hS) hT

/-! ### The comparison from the constant presheaf -/

/-- The map of presheaves of abelian groups on the small étale site of `S` inside `B` sending
`a : A` to the constant map with value `a`. -/
public def constantToLocallyConstantMapsAb (A : Type (max (u + 1) v)) [AddCommGroup A] :
    (Functor.const (SmallEtale B S hS)ᵒᵖ).obj (AddCommGrpCat.of A) ⟶
      locallyConstantMapsAbSmallEtale.{u, v} B S hS A where
  app T := AddCommGrpCat.ofHom (LocallyConstant.constAddMonoidHom
    (X := (SmallEtale.toScheme B S hS).obj T.unop))
  naturality T₁ T₂ f := by
    ext a
    rfl

/-- Two sections of the constant presheaf with the same constant map agree locally on the small
étale site: they agree outright as soon as the underlying scheme has a point, and otherwise the
empty family is a cover. -/
public theorem constantToLocallyConstantMapsAb_isLocallyInjective (A : Type (max (u + 1) v))
    [AddCommGroup A] :
    Presheaf.IsLocallyInjective (SmallEtale.topology B S hS)
      (constantToLocallyConstantMapsAb.{u, v} B S hS A) := by
  classical
  refine ⟨fun {T} a b hab => ?_⟩
  change LocallyConstant.const ((SmallEtale.toScheme B S hS).obj T.unop) a =
    LocallyConstant.const ((SmallEtale.toScheme B S hS).obj T.unop) b at hab
  by_cases hab' : a = b
  · subst b
    simp
  · have hEmpty : IsEmpty ((SmallEtale.toScheme B S hS).obj T.unop) :=
      ⟨fun x => hab' (by
        simpa using congrArg
          (fun f : LocallyConstant ((SmallEtale.toScheme B S hS).obj T.unop) A => f x) hab)⟩
    have heq : Presheaf.equalizerSieve
        (F := (Functor.const (SmallEtale B S hS)ᵒᵖ).obj (AddCommGrpCat.of A)) (X := T) a b
          = ⊥ := by
      ext V f
      simp only [Presheaf.equalizerSieve_apply, Sieve.bot_apply]
      exact ⟨fun hf => hab' (by simpa using hf), False.elim⟩
    rw [heq]
    exact smallEtaleTopology_bot_mem B S hS hEmpty

/-- Every locally constant `A`-valued map on an object of the small étale site is locally in
the image of the constant presheaf: the sets on which it is constant form an open cover, and an
open cover is refined by a covering family of the site. -/
public theorem constantToLocallyConstantMapsAb_isLocallySurjective (A : Type (max (u + 1) v))
    [AddCommGroup A] :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS)
      (constantToLocallyConstantMapsAb.{u, v} B S hS A) := by
  classical
  refine ⟨fun {T} s => ?_⟩
  let s₀ : LocallyConstant ((SmallEtale.toScheme B S hS).obj T) A := s
  choose O hO hx hconst using fun x => s₀.isLocallyConstant.exists_open x
  let U : (SmallEtale.toScheme B S hS).obj T → ((SmallEtale.toScheme B S hS).obj T).Opens :=
    fun x => ⟨O x, hO x⟩
  have hU : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover]
    refine le_antisymm le_top fun x _ => ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨x, hx x⟩
  obtain ⟨I, W, a, r, hcover, hmaps⟩ := smallEtale_openCoverData B S hS U hU
  refine SmallEtale.topology B S hS |>.superset_covering ?_ hcover
  intro V f hf
  obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff W a f).mp hf
  refine (Presheaf.imageSieve
    (constantToLocallyConstantMapsAb.{u, v} B S hS A) s).downward_closed ?_ g
  refine ⟨s₀ (r i), ?_⟩
  show LocallyConstant.const ((SmallEtale.toScheme B S hS).obj (W i)) (s₀ (r i)) =
    LocallyConstant.comapAddMonoidHom
      ((SmallEtale.toScheme B S hS).map (a i)).base.hom s₀
  refine LocallyConstant.ext fun y => ?_
  show s₀ (r i) = s₀ ((SmallEtale.toScheme B S hS).map (a i) y)
  exact (hconst (r i) _ (hmaps i y)).symm


/-! ### Sheafification with coefficients in the étale-cohomology universe -/

/-- The local-bijectivity criterion for abelian sheaves on the small étale site of `S` inside
`B` with coefficients in the universe `max (u + 1) v`: the site has objects in `Type (u + 1)`
and morphisms in `Type u`, hence is essentially small in the coefficient universe, and the
criterion transports from a small model taken there. -/
public instance (priority := low) smallEtaleTopology_wEqualsLocallyBijective_addCommGrpCat :
    (SmallEtale.topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) v} :=
  have : ∀ T : (SmallEtale B S hS)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow T (equivSmallModel.{max (u + 1) v} (SmallEtale B S hS)).inverse.op)
      AddCommGrpCat.{max (u + 1) v} :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{max (u + 1) v} _ _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u,
    max (u + 1) v, u + 1, max (u + 1) v + 1, max (u + 1) v} (SmallEtale.topology B S hS)

/-! ### The constant abelian sheaf -/

/-- **Stacks 03P5 for the small étale site of a chosen big étale site, with abelian
coefficients.** The constant sheaf of abelian groups with value `A` on the small étale site of
`S` inside `B` is the sheaf of locally constant `A`-valued maps. -/
public def constantSheafIsoLocallyConstantMapsAb_smallEtale (A : Type (max (u + 1) v))
    [AddCommGroup A] :
    (constantSheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v}).obj
        (AddCommGrpCat.of A) ≅
      locallyConstantSheafAb.{u, v} B S hS A := by
  haveI := constantToLocallyConstantMapsAb_isLocallyInjective.{u, v} B S hS A
  haveI := constantToLocallyConstantMapsAb_isLocallySurjective.{u, v} B S hS A
  have hfac : toSheafify (SmallEtale.topology B S hS)
        ((Functor.const (SmallEtale B S hS)ᵒᵖ).obj (AddCommGrpCat.of A)) ≫
      sheafifyLift (SmallEtale.topology B S hS)
        (constantToLocallyConstantMapsAb.{u, v} B S hS A)
        (locallyConstantSheafAb.{u, v} B S hS A).property =
      constantToLocallyConstantMapsAb.{u, v} B S hS A :=
    toSheafify_sheafifyLift _ _ _
  have hinj : Presheaf.IsLocallyInjective (SmallEtale.topology B S hS)
      (sheafifyLift (SmallEtale.topology B S hS)
        (constantToLocallyConstantMapsAb.{u, v} B S hS A)
        (locallyConstantSheafAb.{u, v} B S hS A).property) := by
    rw [← Presheaf.comp_isLocallyInjective_iff (SmallEtale.topology B S hS)
      (toSheafify (SmallEtale.topology B S hS)
        ((Functor.const (SmallEtale B S hS)ᵒᵖ).obj (AddCommGrpCat.of A))), hfac]
    infer_instance
  have hsurj : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS)
      (sheafifyLift (SmallEtale.topology B S hS)
        (constantToLocallyConstantMapsAb.{u, v} B S hS A)
        (locallyConstantSheafAb.{u, v} B S hS A).property) := by
    rw [← Presheaf.comp_isLocallySurjective_iff (SmallEtale.topology B S hS)
      (toSheafify (SmallEtale.topology B S hS)
        ((Functor.const (SmallEtale B S hS)ᵒᵖ).obj (AddCommGrpCat.of A))), hfac]
    infer_instance
  haveI : IsIso (ObjectProperty.homMk (sheafifyLift (SmallEtale.topology B S hS)
      (constantToLocallyConstantMapsAb.{u, v} B S hS A)
      (locallyConstantSheafAb.{u, v} B S hS A).property) :
      (presheafToSheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v}).obj
          ((Functor.const (SmallEtale B S hS)ᵒᵖ).obj (AddCommGrpCat.of A)) ⟶
        locallyConstantSheafAb.{u, v} B S hS A) :=
    (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨hinj, hsurj⟩
  have e : (presheafToSheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v}).obj
        ((Functor.const (SmallEtale B S hS)ᵒᵖ).obj (AddCommGrpCat.of A)) ≅
      locallyConstantSheafAb.{u, v} B S hS A :=
    asIso (ObjectProperty.homMk (sheafifyLift (SmallEtale.topology B S hS)
      (constantToLocallyConstantMapsAb.{u, v} B S hS A)
      (locallyConstantSheafAb.{u, v} B S hS A).property))
  exact e

/-- The underlying presheaves of the constant abelian sheaf and of the locally constant maps
agree: the presheaf-level corollary of
`AlgebraicGeometry.constantSheafIsoLocallyConstantMapsAb_smallEtale`. -/
public def constantSheafIsoLocallyConstantMapsAb_smallEtale_presheaf (A : Type (max (u + 1) v))
    [AddCommGroup A] :
    ((constantSheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v}).obj
        (AddCommGrpCat.of A)).obj ≅
      locallyConstantMapsAbSmallEtale.{u, v} B S hS A :=
  (sheafToPresheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v}).mapIso
    (constantSheafIsoLocallyConstantMapsAb_smallEtale.{u, v} B S hS A)

/-- The identification of the constant abelian sheaf with the locally constant maps sends the
sheafification-unit image of `a : A` to the constant map with value `a`. -/
public theorem constantSheafIsoLocallyConstantMapsAb_smallEtale_unit
    (A : Type (max (u + 1) v)) [AddCommGroup A] (T : (SmallEtale B S hS)ᵒᵖ) (a : A) :
    ((constantSheafIsoLocallyConstantMapsAb_smallEtale.{u, v} B S hS A).hom.hom.app T)
        ((toSheafify (SmallEtale.topology B S hS)
          ((Functor.const (SmallEtale B S hS)ᵒᵖ).obj (AddCommGrpCat.of A))).app T a) =
      LocallyConstant.const ((SmallEtale.toScheme B S hS).obj T.unop) a := by
  have h := congrArg (fun f => f.app T a)
    (toSheafify_sheafifyLift (SmallEtale.topology B S hS)
      (constantToLocallyConstantMapsAb.{u, v} B S hS A)
      (locallyConstantSheafAb.{u, v} B S hS A).property)
  show (sheafifyLift (SmallEtale.topology B S hS)
      (constantToLocallyConstantMapsAb.{u, v} B S hS A)
      (locallyConstantSheafAb.{u, v} B S hS A).property).app T
    (((toSheafify (SmallEtale.topology B S hS)
      ((Functor.const (SmallEtale B S hS)ᵒᵖ).obj (AddCommGrpCat.of A))).app T) a) = _
  exact h


/-! ### The stalk at a geometric point -/

section Stalk

variable (t : GeometricPoint S) (A : Type (max (u + 1) v)) [AddCommGroup A]

/-- A lift of a geometric point to the final object `S / S` of the small étale site is the
geometric point itself, the structure morphism of the final object being the identity. -/
public theorem geometricPointFiber_final_eq
    (q : (geometricPointFiber B S hS t).obj (SmallEtale.final B S hS)) :
    q = SmallEtale.finalLift B S hS t := by
  refine Subtype.ext ?_
  have hid : B.inclusion.map (SmallEtale.final B S hS).obj.hom =
      𝟙 ((SmallEtale.toScheme B S hS).obj (SmallEtale.final B S hS)) := by
    show B.inclusion.map (𝟙 (B.obj S hS)) = 𝟙 _
    exact B.inclusion.map_id _
  exact (Category.comp_id q.1).symm.trans ((congrArg (q.1 ≫ ·) hid.symm).trans q.2)

/-- The germ of a locally constant map at a geometric point is the germ over the final object
`S / S` of the constant map carrying its value at the geometric point: the two agree after
restriction to a Zariski open on which the map is constant. -/
public theorem etaleGerm_const_eq (W : SmallEtale B S hS)
    (q : (geometricPointFiber B S hS t).obj W)
    (s : LocallyConstant ((SmallEtale.toScheme B S hS).obj W) A) :
    SmallEtale.etaleGerm B S hS t (locallyConstantMapsAbSmallEtale.{u, v} B S hS A)
        (SmallEtale.final B S hS) (SmallEtale.finalLift B S hS t)
        (LocallyConstant.const ((SmallEtale.toScheme B S hS).obj (SmallEtale.final B S hS))
          (s (q.1.base (default : ↥t.source)))) =
      SmallEtale.etaleGerm B S hS t (locallyConstantMapsAbSmallEtale.{u, v} B S hS A) W q s := by
  classical
  obtain ⟨O, hOopen, hxO, hconst⟩ :=
    s.isLocallyConstant.exists_open (q.1.base (default : ↥t.source))
  let W₀ : ((SmallEtale.toScheme B S hS).obj W).Opens := ⟨O, hOopen⟩
  have hmem : q.1.base (default : ↥t.source) ∈
      (W₀ : Set ((SmallEtale.toScheme B S hS).obj W)) := hxO
  let j : SmallEtale.openObject B S hS W W₀ ⟶ SmallEtale.final B S hS :=
    (SmallEtale.finalIsTerminal B S hS).from (SmallEtale.openObject B S hS W W₀)
  let p := SmallEtale.openObjectLift B S hS t W q W₀ hmem
  have hrestr : ((locallyConstantMapsAbSmallEtale.{u, v} B S hS A).map
        (SmallEtale.openObjectι B S hS W W₀).op s :
      LocallyConstant ((SmallEtale.toScheme B S hS).obj
        (SmallEtale.openObject B S hS W W₀)) A) =
      (locallyConstantMapsAbSmallEtale.{u, v} B S hS A).map j.op
        (LocallyConstant.const ((SmallEtale.toScheme B S hS).obj (SmallEtale.final B S hS))
          (s (q.1.base (default : ↥t.source)))) := by
    refine LocallyConstant.ext fun y => ?_
    show s (((SmallEtale.toScheme B S hS).map (SmallEtale.openObjectι B S hS W W₀)).base y) =
      s (q.1.base (default : ↥t.source))
    rw [SmallEtale.openObjectι_map]
    exact hconst _ y.2
  have h1 := SmallEtale.etaleGerm_openObjectLift B S hS t
    (locallyConstantMapsAbSmallEtale.{u, v} B S hS A) W q W₀ hmem s
  have h2 := SmallEtale.etaleGerm_map B S hS t
    (locallyConstantMapsAbSmallEtale.{u, v} B S hS A) j (SmallEtale.finalLift B S hS t) p
    (geometricPointFiber_final_eq B S hS t _)
    (LocallyConstant.const ((SmallEtale.toScheme B S hS).obj (SmallEtale.final B S hS))
      (s (q.1.base (default : ↥t.source))))
  exact h2.symm.trans ((congrArg (SmallEtale.etaleGerm B S hS t
    (locallyConstantMapsAbSmallEtale.{u, v} B S hS A)
    (SmallEtale.openObject B S hS W W₀) p) hrestr.symm).trans h1)

/-- The cocone on the stalk diagram of the locally constant maps whose leg over an étale
neighbourhood of the geometric point evaluates a locally constant map at the image of the
chosen lift. -/
public def etaleStalkLocallyConstantMapsAbCocone :
    Cocone (SmallEtale.etaleStalkDiagram B S hS t
      (locallyConstantMapsAbSmallEtale.{u, v} B S hS A)) where
  pt := AddCommGrpCat.of A
  ι :=
    { app := fun U => AddCommGrpCat.ofHom
        (⟨⟨fun s => s (U.unop.2.1.base (default : ↥t.source)), rfl⟩, fun _ _ => rfl⟩ :
          LocallyConstant ((SmallEtale.toScheme B S hS).obj U.unop.1) A →+ A)
      naturality := by
        intro U U' m
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro s
        let s₀ : LocallyConstant ((SmallEtale.toScheme B S hS).obj U.unop.1) A := s
        have hcomp : U'.unop.2.1 ≫ (SmallEtale.toScheme B S hS).map m.unop.1 = U.unop.2.1 :=
          congrArg Subtype.val m.unop.2
        have hb : ((SmallEtale.toScheme B S hS).map m.unop.1).base
            (U'.unop.2.1.base (default : ↥t.source)) =
            U.unop.2.1.base (default : ↥t.source) := by
          simpa only [Scheme.Hom.comp_apply] using
            congrArg (fun k : t.source ⟶ (SmallEtale.toScheme B S hS).obj U.unop.1 =>
              k.base (default : ↥t.source)) hcomp
        change s₀ (((SmallEtale.toScheme B S hS).map m.unop.1).base
            (U'.unop.2.1.base (default : ↥t.source))) =
          s₀ (U.unop.2.1.base (default : ↥t.source))
        exact congrArg (⇑s₀) hb }

/-- The map from the stalk of the locally constant maps at a geometric point to the coefficient
group: evaluate a representing locally constant map at the image of the chosen lift. -/
public def etaleStalkLocallyConstantMapsAbHom :
    etaleStalk B S hS t (locallyConstantMapsAbSmallEtale.{u, v} B S hS A) ⟶
      AddCommGrpCat.of A :=
  colimit.desc (SmallEtale.etaleStalkDiagram B S hS t
      (locallyConstantMapsAbSmallEtale.{u, v} B S hS A))
    (etaleStalkLocallyConstantMapsAbCocone.{u, v} B S hS t A)

/-- The evaluation map out of the stalk sends the germ of a locally constant map to its value
at the image of the chosen lift. -/
public theorem etaleStalkLocallyConstantMapsAbHom_etaleGerm (W : SmallEtale B S hS)
    (q : (geometricPointFiber B S hS t).obj W)
    (a : LocallyConstant ((SmallEtale.toScheme B S hS).obj W) A) :
    etaleStalkLocallyConstantMapsAbHom.{u, v} B S hS t A
        (SmallEtale.etaleGerm B S hS t
          (locallyConstantMapsAbSmallEtale.{u, v} B S hS A) W q a) =
      a (q.1.base (default : ↥t.source)) :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (etaleStalkLocallyConstantMapsAbCocone.{u, v} B S hS t A)
      (op (⟨W, q⟩ : (geometricPointFiber B S hS t).Elements))) a

/-- The map from the coefficient group to the stalk of the locally constant maps: send `a : A`
to the germ over the final object `S / S` of the constant map with value `a`. -/
public def etaleStalkLocallyConstantMapsAbInv :
    AddCommGrpCat.of A ⟶
      etaleStalk B S hS t (locallyConstantMapsAbSmallEtale.{u, v} B S hS A) :=
  AddCommGrpCat.ofHom
    { toFun := fun a => SmallEtale.etaleGerm B S hS t
        (locallyConstantMapsAbSmallEtale.{u, v} B S hS A) (SmallEtale.final B S hS)
        (SmallEtale.finalLift B S hS t)
        (LocallyConstant.const ((SmallEtale.toScheme B S hS).obj (SmallEtale.final B S hS)) a)
      map_zero' := SmallEtale.etaleGerm_zero B S hS t
        (locallyConstantMapsAbSmallEtale.{u, v} B S hS A) (SmallEtale.final B S hS)
        (SmallEtale.finalLift B S hS t)
      map_add' := fun a b => SmallEtale.etaleGerm_add B S hS t
        (locallyConstantMapsAbSmallEtale.{u, v} B S hS A) (SmallEtale.final B S hS)
        (SmallEtale.finalLift B S hS t)
        (LocallyConstant.const ((SmallEtale.toScheme B S hS).obj (SmallEtale.final B S hS)) a)
        (LocallyConstant.const ((SmallEtale.toScheme B S hS).obj (SmallEtale.final B S hS)) b) }

/-- **The stalk of the constant abelian sheaf.** The stalk at a geometric point of `S` of the
sheaf of locally constant `A`-valued maps on the small étale site is `A`. -/
public def etaleStalkLocallyConstantMapsAbIso :
    etaleStalk B S hS t (locallyConstantMapsAbSmallEtale.{u, v} B S hS A) ≅
      AddCommGrpCat.of A where
  hom := etaleStalkLocallyConstantMapsAbHom.{u, v} B S hS t A
  inv := etaleStalkLocallyConstantMapsAbInv.{u, v} B S hS t A
  hom_inv_id := by
    refine colimit.hom_ext fun U => ?_
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    let s₀ : LocallyConstant ((SmallEtale.toScheme B S hS).obj U.unop.1) A := s
    change etaleStalkLocallyConstantMapsAbInv.{u, v} B S hS t A
        (etaleStalkLocallyConstantMapsAbHom.{u, v} B S hS t A
          (SmallEtale.etaleGerm B S hS t
            (locallyConstantMapsAbSmallEtale.{u, v} B S hS A) U.unop.1 U.unop.2 s₀)) =
      SmallEtale.etaleGerm B S hS t
        (locallyConstantMapsAbSmallEtale.{u, v} B S hS A) U.unop.1 U.unop.2 s₀
    rw [etaleStalkLocallyConstantMapsAbHom_etaleGerm.{u, v} B S hS t A U.unop.1 U.unop.2 s₀]
    exact etaleGerm_const_eq.{u, v} B S hS t A U.unop.1 U.unop.2 s₀
  inv_hom_id := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    change etaleStalkLocallyConstantMapsAbHom.{u, v} B S hS t A
        (SmallEtale.etaleGerm B S hS t
          (locallyConstantMapsAbSmallEtale.{u, v} B S hS A) (SmallEtale.final B S hS)
          (SmallEtale.finalLift B S hS t)
          (LocallyConstant.const
            ((SmallEtale.toScheme B S hS).obj (SmallEtale.final B S hS)) a)) = a
    exact etaleStalkLocallyConstantMapsAbHom_etaleGerm.{u, v} B S hS t A
      (SmallEtale.final B S hS) (SmallEtale.finalLift B S hS t)
      (LocallyConstant.const ((SmallEtale.toScheme B S hS).obj (SmallEtale.final B S hS)) a)

/-- The identification of the stalk with the coefficient group sends the germ of a locally
constant map to its value at the image of the chosen lift. -/
public theorem etaleStalkLocallyConstantMapsAbIso_etaleGerm (W : SmallEtale B S hS)
    (q : (geometricPointFiber B S hS t).obj W)
    (a : LocallyConstant ((SmallEtale.toScheme B S hS).obj W) A) :
    (etaleStalkLocallyConstantMapsAbIso.{u, v} B S hS t A).hom
        (SmallEtale.etaleGerm B S hS t
          (locallyConstantMapsAbSmallEtale.{u, v} B S hS A) W q a) =
      a (q.1.base (default : ↥t.source)) :=
  etaleStalkLocallyConstantMapsAbHom_etaleGerm.{u, v} B S hS t A W q a

/-- The inverse of the identification of the stalk with the coefficient group sends `a : A` to
the germ over the final object of the constant map with value `a`. -/
public theorem etaleStalkLocallyConstantMapsAbIso_inv_const (a : A) :
    (etaleStalkLocallyConstantMapsAbIso.{u, v} B S hS t A).inv a =
      SmallEtale.etaleGerm B S hS t (locallyConstantMapsAbSmallEtale.{u, v} B S hS A)
        (SmallEtale.final B S hS) (SmallEtale.finalLift B S hS t)
        (LocallyConstant.const
          ((SmallEtale.toScheme B S hS).obj (SmallEtale.final B S hS)) a) :=
  rfl

end Stalk

end AlgebraicGeometry

end
