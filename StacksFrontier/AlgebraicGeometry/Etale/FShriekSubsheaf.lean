module

public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.CategoryTheory.Subobject.MonoOver
public import StacksFrontier.AlgebraicGeometry.Descent.ProperClosedSubsetFpqc
public import StacksFrontier.AlgebraicGeometry.Etale.SupportedSections
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SiteAxioms
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Coverings
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The proper-support direct image of an abelian étale sheaf

Let `f : X ⟶ Y` be a morphism of a big étale site which is locally of finite type as a morphism
of schemes, and let `F` be an abelian sheaf on the small étale site of `X`. A section of the
direct image `f_* F` over an étale test scheme `V ⟶ Y` is a section of `F` over `X ×_Y V`, and
it is said to have *proper support over `V`* when its support — the closed complement of its
maximal zero open — is proper over `V`. These sections form an abelian subsheaf `f_! F` of
`f_* F`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.properSupportSections`: the proper-support condition on a
  section of the small-étale direct image.
* `AlgebraicGeometry.SmallEtale.properSupportSubgroup`: those sections over a fixed test object,
  as an additive subgroup.
* `AlgebraicGeometry.SmallEtale.properSupportPresheaf` and
  `AlgebraicGeometry.SmallEtale.properSupportInclusion`: the resulting subpresheaf of the direct
  image, and its inclusion.
* `AlgebraicGeometry.SmallEtale.fShriekSubsheaf`: the canonical abelian subsheaf of `f_* F` cut
  out by the proper-support condition, bundled with the sectionwise characterization of its
  image.

## Main results

* `AlgebraicGeometry.SmallEtale.coe_zeroOpen_map` and
  `AlgebraicGeometry.SmallEtale.supportSection_map`: the maximal zero open and the support of a
  restricted section are the inverse images of those of the original section.
* `AlgebraicGeometry.SmallEtale.properSupportSections_restrict` and
  `AlgebraicGeometry.SmallEtale.properSupportSections_descend`: the proper-support condition is
  stable under restriction and is local for the fpqc topology on the test object, hence for the
  étale topology.
* `AlgebraicGeometry.SmallEtale.mem_range_fShriekSubsheaf_arrow_iff`: the sections of
  `fShriekSubsheaf` are exactly the sections with proper support, while
  `AlgebraicGeometry.SmallEtale.fShriekSubsheaf_obj_left` and
  `AlgebraicGeometry.SmallEtale.fShriekSubsheaf_arrow` identify the chosen subobject and its
  monomorphism with `properSupportSheaf` and `properSupportSheafInclusion`.
* `AlgebraicGeometry.SmallEtale.properSupportSections_zero`: the zero section has proper
  support.

## Implementation notes

The support of a section is the complement of the maximal Zariski zero open of Tag 04FS, and
the structural morphism of the test object `V` is the first projection of the fibre product
`X ×_Y V`, so the condition is properness over `V` of a closed subset of `X ×_Y V` in the sense
of Tag 0CYM.

That the condition is closed under addition, negation and contains zero uses the behaviour of
supports under those operations (Tag 04FT) together with the union and monotonicity statements
for proper closed subsets (Tags 0CYR, 0CYN). Stability under restriction is base change of a
proper closed subset (Tag 0CYP) applied to the square obtained by base changing an arrow of the
small étale site of `Y`. Locality is fpqc descent of properness of a closed subset (Tag 0F4J),
which applies because an étale covering family is an fpqc covering family (Tag 022C).

The sheaf condition is checked on the underlying subfunctor of sets: that subfunctor equals its
own sheafification, which is proved by induction over the saturation generating the small étale
topology, and a subfunctor equal to its sheafification inside a sheaf is a sheaf. Reducing the
problem to the underlying sets is legitimate because the forgetful functor from abelian groups
both preserves and reflects the sheaf condition.

The subsheaf is returned bundled with its monomorphism into the direct image as a `MonoOver`,
together with the proof that its image is exactly the set of proper-support sections, so later
constructions can use the inclusion and its characterization without choosing another model.
The coefficient universe `v` is independent of the scheme universe `u`.

## References

* [Stacks Project, Tag 0F4X](https://stacks.math.columbia.edu/tag/0F4X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v w

namespace AlgebraicGeometry.SmallEtale

section Support

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})

/-- A section and its negative have the same maximal zero open. -/
public theorem zeroOpen_neg (U : SmallEtale B S hS) (s : F.obj.obj (op U)) :
    zeroOpen B S hS F U (-s) = zeroOpen B S hS F U s := by
  refine congrArg sSup ?_
  ext W
  show IsZeroOpen B S hS F U (-s) W ↔ IsZeroOpen B S hS F U s W
  constructor <;> rintro ⟨V, g, hg, hW, hz⟩ <;>
    exact ⟨V, g, hg, hW, by simpa only [map_neg, neg_eq_zero] using hz⟩

/-- The zero section vanishes everywhere. -/
public theorem zeroOpen_zero (U : SmallEtale B S hS) :
    zeroOpen B S hS F U (0 : F.obj.obj (op U)) = ⊤ := by
  refine top_unique (le_sSup ?_)
  show IsZeroOpen B S hS F U 0 ⊤
  refine ⟨U, 𝟙 U, ?_, by simp, by simp⟩
  simpa using (inferInstance : IsOpenImmersion (𝟙 ((SmallEtale.toScheme B S hS).obj U)))

/-- The maximal zero open of a restricted section is the inverse image of the maximal zero
open. -/
public theorem coe_zeroOpen_map (U V : SmallEtale B S hS) (a : V ⟶ U) (s : F.obj.obj (op U)) :
    (zeroOpen B S hS F V (F.obj.map a.op s) :
        Set ((SmallEtale.toScheme B S hS).obj V)) =
      ((SmallEtale.toScheme B S hS).map a).base ⁻¹'
        (zeroOpen B S hS F U s : Set ((SmallEtale.toScheme B S hS).obj U)) := by
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨W, hWmem, hxW⟩ := TopologicalSpace.Opens.mem_sSup.mp hx
    obtain ⟨T, b, -, hWr, hz⟩ := hWmem
    have hz' : F.obj.map (b ≫ a).op s = 0 := by simpa [Functor.map_comp] using hz
    have hrange := (map_eq_zero_iff_range_subset_zeroOpen B S hS F U s T (b ≫ a)).mp hz'
    have hxW' : x ∈ (W : Set ((SmallEtale.toScheme B S hS).obj V)) := hxW
    rw [hWr] at hxW'
    obtain ⟨y, rfl⟩ := hxW'
    exact hrange ⟨y, by simp⟩
  · by_contra hnot
    exact supportSection_restrict_subset_preimage B S hS F U V a s hnot hx

/-- The support of a restricted section is the inverse image of the support. -/
public theorem supportSection_map (U V : SmallEtale B S hS) (a : V ⟶ U)
    (s : F.obj.obj (op U)) :
    supportSection B S hS F V (F.obj.map a.op s) =
      ((SmallEtale.toScheme B S hS).map a).base ⁻¹'
        supportSection B S hS F U s := by
  unfold supportSection
  rw [coe_zeroOpen_map, Set.preimage_compl]

end Support

section ProperSupport

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})

/-- **Stacks 0F4X.** The condition that a section of the small-étale direct image of `F` over an
étale test object `V ⟶ Y` has proper support over `V`: its support in `X ×_Y V` is proper over
`V`. -/
@[stacks 0F4X "the proper support condition"]
public def properSupportSections (V : SmallEtale B Y.obj Y.property)
    (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj V))) : Prop := by
  let _ := hasPullbacks_bigEtaleSite B
  let Z : Closeds ((SmallEtale.toScheme B X.obj X.property).obj
      ((smallEtaleBaseChange B f).obj V)) :=
    (zeroOpen B X.obj X.property F ((smallEtaleBaseChange B f).obj V) s).compl
  exact IsProper ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫
    B.inclusion.map (pullback.fst V.obj.hom f))

/-- The projection `X ×_Y V ⟶ V` of a base change of a morphism locally of finite type is
locally of finite type. -/
public theorem locallyOfFiniteType_baseChangeProjection
    [LocallyOfFiniteType (B.inclusion.map f)] (V : SmallEtale B Y.obj Y.property) :
    haveI := hasPullbacks_bigEtaleSite B
    LocallyOfFiniteType (B.inclusion.map (pullback.fst V.obj.hom f)) := by
  have := hasPullbacks_bigEtaleSite B
  exact MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback V.obj.hom f).flip.map B.inclusion) inferInstance

/-- Base changing an arrow of a slice category along a morphism gives a cartesian square of the
two first projections. -/
public theorem isPullback_overPullback_map_left {C : Type*} [Category C] [HasPullbacks C]
    {S T : C} (g : T ⟶ S) {U V : Over S} (a : V ⟶ U) :
    IsPullback ((Over.pullback g).map a).left (pullback.fst V.hom g)
      (pullback.fst U.hom g) a.left := by
  have h₁ : ((Over.pullback g).map a).left ≫ pullback.snd U.hom g = pullback.snd V.hom g :=
    Over.w ((Over.pullback g).map a)
  refine IsPullback.of_right (h₁₂ := pullback.snd U.hom g) (h₂₂ := U.hom) ?_
    (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback U.hom g).flip
  rw [h₁, Over.w a]
  exact (IsPullback.of_hasPullback V.hom g).flip

/-- The square comparing the two projections of the base changes of an arrow of the small étale
site of `Y`. -/
public theorem isPullback_baseChange_projection {U V : SmallEtale B Y.obj Y.property}
    (a : V ⟶ U) :
    haveI := hasPullbacks_bigEtaleSite B
    IsPullback (B.inclusion.map ((Over.pullback f).map a.hom).left)
      (B.inclusion.map (pullback.fst V.obj.hom f))
      (B.inclusion.map (pullback.fst U.obj.hom f))
      (B.inclusion.map a.hom.left) := by
  have := hasPullbacks_bigEtaleSite B
  exact (isPullback_overPullback_map_left f a.hom).map B.inclusion

/-- The preimage of the support of a section under the base change of an arrow is the support of
the restricted section. -/
private theorem preimage_compl_zeroOpen_baseChange {U V : SmallEtale B Y.obj Y.property}
    (a : V ⟶ U) (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj U))) :
    (zeroOpen B X.obj X.property F ((smallEtaleBaseChange B f).obj U) s).compl.preimage
        (B.inclusion.map ((Over.pullback f).map a.hom).left).continuous =
      (zeroOpen B X.obj X.property F ((smallEtaleBaseChange B f).obj V)
        (F.obj.map ((smallEtaleBaseChange B f).map a).op s)).compl :=
  Closeds.ext (supportSection_map B X.obj X.property F
    ((smallEtaleBaseChange B f).obj U) ((smallEtaleBaseChange B f).obj V)
    ((smallEtaleBaseChange B f).map a) s).symm

/-- **Stacks 0F4X.** The proper-support condition is stable under restriction along an arrow of
the small étale site of `Y`. -/
@[stacks 0F4X "stability under restriction"]
public theorem properSupportSections_restrict [LocallyOfFiniteType (B.inclusion.map f)]
    (U V : SmallEtale B Y.obj Y.property) (a : V ⟶ U)
    (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj U)))
    (hs : properSupportSections B f F U s) :
    properSupportSections B f F V (F.obj.map ((smallEtaleBaseChange B f).map a).op s) := by
  have := hasPullbacks_bigEtaleSite B
  have := preservesPullbacks_bigEtaleSiteInclusion B
  have hfu : LocallyOfFiniteType (B.inclusion.map (pullback.fst U.obj.hom f)) :=
    locallyOfFiniteType_baseChangeProjection B f U
  have hfv : LocallyOfFiniteType (B.inclusion.map (pullback.fst V.obj.hom f)) :=
    locallyOfFiniteType_baseChangeProjection B f V
  have hZ' := isProperOver_preimage_baseChange
    (B.inclusion.map ((Over.pullback f).map a.hom).left)
    (B.inclusion.map (pullback.fst V.obj.hom f))
    (B.inclusion.map (pullback.fst U.obj.hom f))
    (B.inclusion.map a.hom.left) (isPullback_baseChange_projection B f a)
    (zeroOpen B X.obj X.property F ((smallEtaleBaseChange B f).obj U) s).compl hs
  exact isProperOver_of_le (B.inclusion.map (pullback.fst V.obj.hom f))
    (preimage_compl_zeroOpen_baseChange B f F a s).symm.le hZ'

/-- An étale covering family of an object of the small étale site is an fpqc covering family of
its underlying scheme. -/
public theorem mem_fpqcPrecoverage_of_isCovering (U : SmallEtale B Y.obj Y.property)
    (E : PreZeroHypercover.{u + 1} U) (hE : SmallEtale.IsCovering B Y.obj Y.property ⟨U, E⟩) :
    Presieve.ofArrows (fun i => (SmallEtale.toScheme B Y.obj Y.property).obj (E.X i))
        (fun i => (SmallEtale.toScheme B Y.obj Y.property).map (E.f i)) ∈
      Scheme.fpqcPrecoverage ((SmallEtale.toScheme B Y.obj Y.property).obj U) := by
  have hEtale := BigEtaleSite.IsCovering.etale
    (𝒰 := ⟨(SmallEtale.inclusion B Y.obj Y.property ⋙
      BigEtaleOver.forget B Y.obj Y.property).obj U,
      E.map (SmallEtale.inclusion B Y.obj Y.property ⋙
        BigEtaleOver.forget B Y.obj Y.property)⟩) hE
  refine Scheme.etalePrecoverage_le_fpqcPrecoverage _ ?_
  show (E.map (SmallEtale.toScheme B Y.obj Y.property)).presieve₀ ∈
    Scheme.etalePrecoverage ((SmallEtale.toScheme B Y.obj Y.property).obj U)
  exact hEtale

/-- **Stacks 0F4X.** The proper-support condition is local for the fpqc topology on the test
object. -/
@[stacks 0F4X "locality of the proper support condition"]
public theorem properSupportSections_descend [LocallyOfFiniteType (B.inclusion.map f)]
    (V : SmallEtale B Y.obj Y.property)
    (s : F.obj.obj (op ((smallEtaleBaseChange B f).obj V)))
    {ι : Type w} (W : ι → SmallEtale B Y.obj Y.property) (a : ∀ i, W i ⟶ V)
    (hcover : Presieve.ofArrows
      (fun i => (SmallEtale.toScheme B Y.obj Y.property).obj (W i))
      (fun i => (SmallEtale.toScheme B Y.obj Y.property).map (a i)) ∈
        Scheme.fpqcPrecoverage ((SmallEtale.toScheme B Y.obj Y.property).obj V))
    (hloc : ∀ i, properSupportSections B f F (W i)
      (F.obj.map ((smallEtaleBaseChange B f).map (a i)).op s)) :
    properSupportSections B f F V s := by
  have := hasPullbacks_bigEtaleSite B
  have := preservesPullbacks_bigEtaleSiteInclusion B
  set fu := B.inclusion.map (pullback.fst V.obj.hom f)
  set Z : Closeds (B.inclusion.obj ((Over.pullback f).obj V.obj).left) :=
    (zeroOpen B X.obj X.property F ((smallEtaleBaseChange B f).obj V) s).compl
  have hfu : LocallyOfFiniteType fu := locallyOfFiniteType_baseChangeProjection B f V
  refine isProperOver_of_fpqc fu Z ⟨ι,
    fun i => (SmallEtale.toScheme B Y.obj Y.property).obj (W i),
    fun i => (SmallEtale.toScheme B Y.obj Y.property).map (a i), hcover, fun i => ?_⟩
  set gi := (SmallEtale.toScheme B Y.obj Y.property).map (a i)
  set fv := B.inclusion.map (pullback.fst (W i).obj.hom f)
  set q := B.inclusion.map ((Over.pullback f).map (a i).hom).left
  have hfv : LocallyOfFiniteType fv := locallyOfFiniteType_baseChangeProjection B f (W i)
  have hsq : IsPullback q fv fu gi := isPullback_baseChange_projection B f (a i)
  have hloc_q : IsProperOver fv (Z.preimage q.continuous) :=
    (preimage_compl_zeroOpen_baseChange B f F (a i) s) ▸ hloc i
  set e := hsq.isoIsPullback _ _ (IsPullback.of_hasPullback fu gi)
  have hfst : e.inv ≫ q = pullback.fst fu gi := by
    rw [← hsq.isoIsPullback_hom_fst _ _ (IsPullback.of_hasPullback fu gi), Iso.inv_hom_id_assoc]
  have hsnd : e.inv ≫ fv = pullback.snd fu gi := by
    rw [← hsq.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback fu gi), Iso.inv_hom_id_assoc]
  have hZeq : (Z.preimage q.continuous).preimage e.inv.continuous =
      Z.preimage (pullback.fst fu gi).continuous :=
    Closeds.ext (by rw [← hfst]; simp [Set.preimage_comp])
  have hres := isProperOver_preimage_of_iso e.symm fv (pullback.snd fu gi) hsnd
    (Z.preimage q.continuous) hloc_q
  exact isProperOver_of_le (pullback.snd fu gi) hZeq.symm.le hres

/-- The sections of `f_* F` over a test object whose support is proper over it, as an additive
subgroup. -/
public def properSupportSubgroup [LocallyOfFiniteType (B.inclusion.map f)]
    (V : SmallEtale B Y.obj Y.property) :
    AddSubgroup (F.obj.obj (op ((smallEtaleBaseChange B f).obj V))) := by
  have := hasPullbacks_bigEtaleSite B
  have hq : LocallyOfFiniteType (B.inclusion.map (pullback.fst V.obj.hom f)) :=
    locallyOfFiniteType_baseChangeProjection B f V
  refine
    { carrier := {s | properSupportSections B f F V s}
      zero_mem' := ?_
      add_mem' := ?_
      neg_mem' := ?_ }
  · intro s t hs ht
    refine isProperOver_of_le (B.inclusion.map (pullback.fst V.obj.hom f)) ?_
      (isProperOver_sup (B.inclusion.map (pullback.fst V.obj.hom f))
        (zeroOpen B X.obj X.property F ((smallEtaleBaseChange B f).obj V) s).compl
        (zeroOpen B X.obj X.property F ((smallEtaleBaseChange B f).obj V) t).compl hs ht)
    change supportSection B X.obj X.property F ((smallEtaleBaseChange B f).obj V) (s + t) ⊆
      supportSection B X.obj X.property F ((smallEtaleBaseChange B f).obj V) s ∪
        supportSection B X.obj X.property F ((smallEtaleBaseChange B f).obj V) t
    exact supportSection_add_subset B X.obj X.property F
      ((smallEtaleBaseChange B f).obj V) s t
  · change IsProperOver (B.inclusion.map (pullback.fst V.obj.hom f))
      (zeroOpen B X.obj X.property F ((smallEtaleBaseChange B f).obj V) 0).compl
    rw [zeroOpen_zero, show (⊤ : ((SmallEtale.toScheme B X.obj X.property).obj
      ((smallEtaleBaseChange B f).obj V)).Opens).compl = ⊥ from
      Closeds.ext Set.compl_univ]
    exact isProperOver_bot (B.inclusion.map (pullback.fst V.obj.hom f))
  · intro s hs
    change IsProperOver (B.inclusion.map (pullback.fst V.obj.hom f))
      (zeroOpen B X.obj X.property F ((smallEtaleBaseChange B f).obj V) (-s)).compl
    rwa [zeroOpen_neg]

/-- The direct image of an abelian sheaf on the small étale site of `X` along `f`. -/
public abbrev directImageSheaf :
    Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{v} :=
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{v}
    (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B X.obj X.property)).obj F

/-- The proper-support condition as a subfunctor of the underlying sets of the direct image. -/
public def properSupportSubfunctor [LocallyOfFiniteType (B.inclusion.map f)] :
    Subfunctor ((directImageSheaf B f F).obj ⋙ forget AddCommGrpCat.{v}) where
  obj U := {s | properSupportSections B f F U.unop s}
  map {U V} g s hs := properSupportSections_restrict B f F U.unop V.unop g.unop s hs

/-- A section whose proper-support condition holds locally on a saturated family has proper
support. -/
public theorem properSupport_of_saturate [LocallyOfFiniteType (B.inclusion.map f)]
    (U : SmallEtale B Y.obj Y.property) (S : Sieve U)
    (hS : (SmallEtale.precoverage B Y.obj Y.property).Saturate U S)
    {V : SmallEtale B Y.obj Y.property} (g : V ⟶ U)
    (s : (directImageSheaf B f F).obj.obj (op V))
    (hloc : ∀ ⦃T : SmallEtale B Y.obj Y.property⦄ (k : T ⟶ V), S (k ≫ g) →
      properSupportSections B f F T ((directImageSheaf B f F).obj.map k.op s)) :
    properSupportSections B f F V s := by
  induction hS generalizing V s with
  | of U R hR =>
      obtain ⟨E, hRE, hE⟩ := (SmallEtale.mem_precoverage_iff B Y.obj Y.property).mp hR
      obtain ⟨P, p₁, p₂, hpb, hcov⟩ :=
        (SmallEtale.isSite B Y.obj Y.property).2.2 ⟨U, E⟩ hE V g
      refine properSupportSections_descend B f F V s (⟨E.I₀, P, p₂⟩ : PreZeroHypercover.{u + 1} V).X
        (⟨E.I₀, P, p₂⟩ : PreZeroHypercover.{u + 1} V).f
        (mem_fpqcPrecoverage_of_isCovering B V ⟨E.I₀, P, p₂⟩ hcov) fun i => ?_
      refine hloc (p₂ i) ?_
      rw [← (hpb i).w]
      exact (Sieve.generate R).downward_closed
        ((Sieve.le_generate R) (E.X i) (E.f i) (hRE ▸ E.presieve₀_f i)) (p₁ i)
  | top U =>
      have he : (directImageSheaf B f F).obj.map (𝟙 V).op s = s :=
        congrArg (fun m => m s) ((directImageSheaf B f F).obj.map_id (op V))
      exact he ▸ hloc (𝟙 V) (by simp)
  | pullback U S hS V₀ g₀ ih =>
      refine ih (g ≫ g₀) s fun T k hk => ?_
      simpa [Functor.map_comp, Category.assoc] using hloc k hk
  | transitive U S R hS hR ihS ihR =>
      refine ihS g s fun T k hk => ?_
      refine ihR hk (𝟙 T) ((directImageSheaf B f F).obj.map k.op s) fun Z l hl => ?_
      have he : (directImageSheaf B f F).obj.map (l ≫ k).op s =
          (directImageSheaf B f F).obj.map l.op
            ((directImageSheaf B f F).obj.map k.op s) :=
        congrArg (fun m => m s) ((directImageSheaf B f F).obj.map_comp k.op l.op)
      exact he ▸ hloc (l ≫ k) hl

/-- The proper-support subfunctor is its own sheafification. -/
public theorem properSupportSubfunctor_eq_sheafify
    [LocallyOfFiniteType (B.inclusion.map f)] :
    properSupportSubfunctor B f F =
      (properSupportSubfunctor B f F).sheafify (SmallEtale.topology B Y.obj Y.property) := by
  refine le_antisymm (Subfunctor.le_sheafify _ _) fun U s hs => ?_
  change (SmallEtale.precoverage B Y.obj Y.property).Saturate (unop U)
    ((properSupportSubfunctor B f F).sieveOfSection s) at hs
  refine properSupport_of_saturate B f F (unop U) _ hs (𝟙 (unop U)) s fun V g hg => ?_
  change properSupportSections B f F V ((directImageSheaf B f F).obj.map g.op s) at hg
  simpa using hg

/-- The underlying sets of the direct image form a sheaf of types. -/
public theorem directImageType_isSheaf [LocallyOfFiniteType (B.inclusion.map f)] :
    Presieve.IsSheaf (SmallEtale.topology B Y.obj Y.property)
      ((directImageSheaf B f F).obj ⋙ forget AddCommGrpCat.{v}) :=
  (isSheaf_iff_isSheaf_of_type (SmallEtale.topology B Y.obj Y.property)
      ((directImageSheaf B f F).obj ⋙ forget AddCommGrpCat.{v})).mp
    (Presheaf.isSheaf_comp_of_isSheaf (SmallEtale.topology B Y.obj Y.property)
      (directImageSheaf B f F).obj (forget AddCommGrpCat.{v})
      (directImageSheaf B f F).property)

/-- The proper-support subfunctor is a sheaf of types. -/
public theorem properSupportSubfunctor_isSheaf
    [LocallyOfFiniteType (B.inclusion.map f)] :
    Presieve.IsSheaf (SmallEtale.topology B Y.obj Y.property)
      (properSupportSubfunctor B f F).toFunctor := by
  rw [properSupportSubfunctor_eq_sheafify B f F]
  exact (properSupportSubfunctor B f F).sheafify_isSheaf (directImageType_isSheaf B f F)

/-- The presheaf of proper-support sections of the direct image. -/
public def properSupportPresheaf [LocallyOfFiniteType (B.inclusion.map f)] :
    (SmallEtale B Y.obj Y.property)ᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj U := AddCommGrpCat.of (properSupportSubgroup B f F U.unop)
  map {U V} g := AddCommGrpCat.ofHom
    { toFun := fun s => ⟨(directImageSheaf B f F).obj.map g s.1,
        properSupportSections_restrict B f F U.unop V.unop g.unop s.1 s.2⟩
      map_zero' := by ext; exact map_zero _
      map_add' := fun s t => by ext; exact map_add _ _ _ }
  map_id U := by
    ext s
    change ((directImageSheaf B f F).obj.map (𝟙 U)) s.1 = s.1
    exact congrArg (fun k => k s.1) ((directImageSheaf B f F).obj.map_id U)
  map_comp {U V T} g h := by
    ext s
    change ((directImageSheaf B f F).obj.map (g ≫ h)) s.1 =
      ((directImageSheaf B f F).obj.map h) (((directImageSheaf B f F).obj.map g) s.1)
    exact congrArg (fun k => k s.1) ((directImageSheaf B f F).obj.map_comp g h)

/-- The inclusion of the proper-support presheaf into the direct image. -/
public def properSupportInclusion [LocallyOfFiniteType (B.inclusion.map f)] :
    properSupportPresheaf B f F ⟶ (directImageSheaf B f F).obj where
  app U := AddCommGrpCat.ofHom (properSupportSubgroup B f F U.unop).subtype
  naturality {U V} g := by ext s; rfl

/-- The inclusion of the proper-support presheaf is a monomorphism. -/
public theorem properSupportInclusion_mono [LocallyOfFiniteType (B.inclusion.map f)] :
    Mono (properSupportInclusion B f F) := by
  rw [NatTrans.mono_iff_mono_app]
  exact fun U => (AddCommGrpCat.mono_iff_injective _).mpr fun _ _ h => Subtype.ext h

/-- The underlying sets of the proper-support presheaf are the proper-support subfunctor. -/
public def properSupportUnderlyingIso [LocallyOfFiniteType (B.inclusion.map f)] :
    properSupportPresheaf B f F ⋙ forget AddCommGrpCat.{v} ≅
      (properSupportSubfunctor B f F).toFunctor :=
  NatIso.ofComponents
    (fun _ => Equiv.toIso
      { toFun := fun s => ⟨s.1, s.2⟩
        invFun := fun s => ⟨s.1, s.2⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl })
    fun _ => by ext s; rfl

/-- The proper-support sections form an abelian sheaf. -/
public def properSupportSheaf [LocallyOfFiniteType (B.inclusion.map f)] :
    Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{v} :=
  ⟨properSupportPresheaf B f F,
    Presheaf.isSheaf_of_isSheaf_comp (SmallEtale.topology B Y.obj Y.property)
      (properSupportPresheaf B f F) (forget AddCommGrpCat.{v})
      ((Presheaf.isSheaf_of_iso_iff (properSupportUnderlyingIso B f F)).2
        ((isSheaf_iff_isSheaf_of_type (SmallEtale.topology B Y.obj Y.property)
          (properSupportSubfunctor B f F).toFunctor).mpr
          (properSupportSubfunctor_isSheaf B f F)))⟩

/-- The inclusion of the proper-support sheaf into the direct image. -/
public def properSupportSheafInclusion [LocallyOfFiniteType (B.inclusion.map f)] :
    properSupportSheaf B f F ⟶ directImageSheaf B f F :=
  ⟨properSupportInclusion B f F⟩

/-- The inclusion of the proper-support sheaf into the direct image is a monomorphism. -/
public instance properSupportSheafInclusion_mono [LocallyOfFiniteType (B.inclusion.map f)] :
    Mono (properSupportSheafInclusion B f F) :=
  have : Mono (properSupportSheafInclusion B f F).hom := properSupportInclusion_mono B f F
  Sheaf.Hom.mono_of_presheaf_mono (SmallEtale.topology B Y.obj Y.property)
    AddCommGrpCat.{v} (properSupportSheafInclusion B f F)

/-- **Stacks 0F4X.** The abelian subsheaf `f_! F` of the small-étale direct image `f_* F`
consisting exactly of the sections whose support is proper over the étale base, bundled with the
sectionwise description of its image. -/
@[stacks 0F4X,
  stacks 0F4Z "the subsheaf f_! F of f_* F, the direct image with compact support",
  sga "4 XVII 6.3.16" "f_! as subsheaf of f_*", sga "4 XVII 6.1.2" "abelian sheaves"]
public def fShriekSubsheaf [LocallyOfFiniteType (B.inclusion.map f)] :
    {G : MonoOver ((smallEtaleBaseChange B f).sheafPushforwardContinuous
        AddCommGrpCat.{v} (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B X.obj X.property) |>.obj F) //
      ∀ (V : SmallEtale B Y.obj Y.property)
        (s : ((smallEtaleBaseChange B f).sheafPushforwardContinuous
          AddCommGrpCat.{v} (SmallEtale.topology B Y.obj Y.property)
            (SmallEtale.topology B X.obj X.property)).obj F |>.obj.obj (op V)),
          s ∈ Set.range (G.arrow.hom.app (op V)) ↔
            properSupportSections B f F V s} :=
  ⟨MonoOver.mk (properSupportSheafInclusion B f F), fun _ s =>
    ⟨fun ⟨x, hx⟩ => hx ▸ x.2, fun hs => ⟨⟨s, hs⟩, rfl⟩⟩⟩

/-- The subsheaf chosen by `fShriekSubsheaf` is the sheaf of proper-support sections. -/
@[simp]
public theorem fShriekSubsheaf_obj_left [LocallyOfFiniteType (B.inclusion.map f)] :
    (fShriekSubsheaf B f F).val.obj.left = properSupportSheaf B f F :=
  rfl

/-- The monomorphism chosen by `fShriekSubsheaf` is the inclusion of the proper-support sheaf. -/
@[simp]
public theorem fShriekSubsheaf_arrow [LocallyOfFiniteType (B.inclusion.map f)] :
    (fShriekSubsheaf B f F).val.arrow = properSupportSheafInclusion B f F :=
  rfl

/-- The zero section has proper support. -/
public theorem properSupportSections_zero [LocallyOfFiniteType (B.inclusion.map f)]
    (V : SmallEtale B Y.obj Y.property) :
    properSupportSections B f F V 0 :=
  (properSupportSubgroup B f F V).zero_mem

/-- **Stacks 0F4X.** The sections of `f_! F` over an étale test object are exactly the sections
of `f_* F` whose support is proper over that object. -/
@[stacks 0F4X "the sectionwise characterization"]
public theorem mem_range_fShriekSubsheaf_arrow_iff [LocallyOfFiniteType (B.inclusion.map f)]
    (V : SmallEtale B Y.obj Y.property)
    (s : (directImageSheaf B f F).obj.obj (op V)) :
    s ∈ Set.range ((fShriekSubsheaf B f F).val.arrow.hom.app (op V)) ↔
      properSupportSections B f F V s :=
  (fShriekSubsheaf B f F).2 V s

end ProperSupport

end AlgebraicGeometry.SmallEtale

end

