module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.InvariantAffineOpenDimensionOne
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# A finite surjective affine chart of an open neighbourhood of a codimension-one point

This file carries out the [Stacks, Tag 0ABI] step of the proof of [Stacks, Tag 0ADD]. Let `X`
be a separated, locally Noetherian algebraic space over `S`, let `g : U ⟶ X` be a finite
surjective morphism from (the functor of points of) a scheme `U`, and let `x` be a point of
`X` whose local ring has dimension at most one. Then there is an open subspace `H ⊆ X`
containing `x` and a finite surjective morphism `W ⟶ H` from an affine scheme `W`.

The argument is the one of the source once the cover `g` has been chosen. The kernel pair
`R = U ×_X U` is an equivalence relation on `U` ([Stacks, Tag 0262]), hence a groupoid scheme
`(U, R, s, t, c)` ([Stacks, Tag 0233]) whose source and target maps are finite, being base
changes of `g`. The scheme `U` is separated, because `g` is finite, hence separated, and `X` is
separated; and `U` is locally Noetherian, because `g` is locally of finite type
([Stacks, Tag 04ZK]). The points of `U` over `x` have local rings of dimension at most one
([Stacks, Tag 0ABW]), so [Stacks, Tag 0ABI] provides an `R`-invariant affine open `W ⊆ U`
containing a point over `x`. The map `|U| → |X|` is closed and surjective, hence submersive,
so the image of the saturated open `W` is open and cuts out an open subspace `H ⊆ X`; the
morphism `W ⟶ H` is the base change of `g` along `H ⊆ X`, hence finite, and it is surjective.

What remains of 0ADD after this step is [Stacks, Tag 07VP], which makes `H` an affine scheme,
and [Stacks, Tag 09YC], which produces the cover `g`. No tag is registered here.

## Main results

* `exists_isOpenSubspace_isFinite_isSurjective_affine_of_localRingDimension_le_one`, in the
  namespace `AlgebraicGeometry.Space`: the statement above.

## Implementation notes

The groupoid scheme of [Stacks, Tag 0233] is only characterised up to the equalities of
`AlgebraicGeometry.ExtendsRelation`; the private lemma
`exists_isAffineOpen_mem_forall_mem_of_isEquivalenceRelation` destructures such a groupoid
against those equalities, so that [Stacks, Tag 0ABI] is read directly on the relation
`(s, t)` and no transport along `eqToHom` is needed afterwards.

## References

* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 0ABI](https://stacks.math.columbia.edu/tag/0ABI)
* [Stacks Project, Tag 0ABW](https://stacks.math.columbia.edu/tag/0ABW)
* [Stacks Project, Tag 0233](https://stacks.math.columbia.edu/tag/0233)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- [Stacks, Tag 0ABI] read on an equivalence relation rather than on a groupoid scheme. Let
`a, b : R ⟶ U` be an equivalence relation on a separated, locally Noetherian scheme `U` over
`T` with `a` and `b` finite, and let `u` be a point of `U` such that every point of the orbit
`a(b⁻¹(u))` has a local ring of dimension at most one. Then some affine open of `U` containing
`u` is invariant: it contains `a(r)` whenever it contains `b(r)`. -/
private theorem exists_isAffineOpen_mem_forall_mem_of_isEquivalenceRelation
    {T : Scheme.{u}} {R U : Over T} (a b : R ⟶ U) [IsEquivalenceRelation a b]
    [_root_.AlgebraicGeometry.IsFinite a.left] [_root_.AlgebraicGeometry.IsFinite b.left]
    [U.left.IsSeparated] [IsLocallyNoetherian U.left]
    (u : U.left)
    (hdim : ∀ r : R.left, b.left r = u → Ring.KrullDimLE 1 (U.left.presheaf.stalk (a.left r))) :
    ∃ W : U.left.Opens, IsAffineOpen W ∧ u ∈ W ∧ ∀ r : R.left, b.left r ∈ W → a.left r ∈ W := by
  let j : PreRelation R U := prod.lift a b
  have hjt : j.target = a := prod.lift_fst a b
  have hjs : j.source = b := prod.lift_snd a b
  have : IsEquivalenceRelation j.target j.source := by
    rw [hjt, hjs]
    infer_instance
  obtain ⟨G, hG⟩ : ∃ G : GroupoidScheme T, ExtendsRelation j G :=
    ⟨_, groupoidSchemeOfIsEquivalenceRelation_extendsRelation j⟩
  rcases G with ⟨objects, arrows, source, target, comp, identity, inverse, source_identity,
    target_identity, source_inverse, target_inverse, source_comp, target_comp, left_identity,
    right_identity, left_inverse, right_inverse, assoc⟩
  obtain ⟨ho, ha, hs, ht⟩ := hG
  dsimp only at ho ha
  replace ho := ho.symm
  replace ha := ha.symm
  subst ho ha
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hs ht
  replace hs := (hs.trans hjs).symm
  replace ht := (ht.trans hjt).symm
  subst hs ht
  obtain ⟨W, hWinv, hWaff, huW⟩ :=
    GroupoidScheme.exists_isInvariantOpen_isAffineOpen_mem_of_krullDimLE_one
      ⟨U, R, b, a, comp, identity, inverse, source_identity, target_identity, source_inverse,
        target_inverse, source_comp, target_comp, left_identity, right_identity, left_inverse,
        right_inverse, assoc⟩ u (by
        rintro u' ⟨r, hr, rfl⟩
        exact hdim r hr)
  exact ⟨W, hWaff, huW, hWinv⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The scheme underlying an object of the big fppf site of `S` is separated as soon as the
presheaf it represents is a separated algebraic space. -/
private theorem isSeparated_toScheme_obj_of_isAbsolutelySeparated
    (hZ : B.Contains (⊤_ Scheme.{u})) (U : BigFppfOver B S hS)
    (h : IsAbsolutelySeparated B S hS hZ (yoneda.obj U)) :
    ((BigFppfOver.toScheme B S hS).obj U).IsSeparated := by
  let γ : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let V : BigFppfOver B (⊤_ Scheme.{u}) hZ := (Over.map γ).obj U
  have hterm : IsTerminal (Over.mk (𝟙 (B.obj hZ)) : BigFppfOver B (⊤_ Scheme.{u}) hZ) :=
    Over.mkIdTerminal
  let e := (OverShriek.relocalizeYonedaIso γ).app U
  have h1 : IsSeparated B (⊤_ Scheme.{u}) hZ (e.hom ≫ yoneda.map (hterm.from V)) :=
    (isSeparatedOver_iff_isSeparated_of_isTerminal B (⊤_ Scheme.{u}) hZ
      (hterm.isTerminalObj yoneda _) _).1 h
  have h2 : IsSeparated B (⊤_ Scheme.{u}) hZ (yoneda.map (hterm.from V)) := by
    have h := isSeparated_comp B (⊤_ Scheme.{u}) hZ e.inv _
      (isSeparated_of_isIso B (⊤_ Scheme.{u}) hZ e.inv) h1
    rwa [Iso.inv_hom_id_assoc] at h
  have h3 := (isSeparated_yoneda_map_iff B (⊤_ Scheme.{u}) hZ (hterm.from V)).1 h2
  let m : (BigFppfOver.toScheme B S hS).obj U ⟶ ⊤_ Scheme.{u} :=
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (hterm.from V)
  have hm : m = terminal.from _ := terminal.hom_ext _ _
  exact ⟨hm ▸ h3⟩

/-- A scheme point `x` of `V` whose image under `ν : V ⟶ T` is the scheme point of a point `w` of
`T` comes from a point of `V` mapping to `w`. -/
private theorem pointsMap_yoneda_map_pointsEquivScheme_symm_eq {V T : BigFppfOver B S hS}
    (ν : V ⟶ T) (x : (BigFppfOver.toScheme B S hS).obj V) (w : points B S hS (yoneda.obj T))
    (h : (BigFppfOver.toScheme B S hS).map ν x = pointsToScheme B S hS T w) :
    pointsMap B S hS (yoneda.obj V) (yoneda.map ν) ((pointsEquivScheme B S hS V).symm x) = w :=
  injective_pointsToScheme B S hS T <| by
    rw [pointsToScheme_pointsMap_yoneda, pointsToScheme_pointsEquivScheme_symm, h]

/-- An invariant affine open over a point of a finite cover. Let `g : U ⟶ X` be finite, with
kernel pair `s, t : R ⟶ U` whose underlying morphisms are finite, `U` separated and locally
Noetherian, and let `y₀` be a point of `U` over a point `x` of `X` whose local ring has
dimension at most one. Then some affine open of `U` containing `y₀` contains `s(r)` whenever it
contains `t(r)`. -/
private theorem exists_isAffineOpen_mem_forall_mem_of_isPullback
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {R U : BigFppfOver B S hS} (g : yoneda.obj U ⟶ X) (hgfin : IsFinite B S hS g)
    (s t : R ⟶ U) (hK : IsPullback (yoneda.map s) (yoneda.map t) g g)
    [_root_.AlgebraicGeometry.IsFinite ((Over.post B.inclusion).map s).left]
    [_root_.AlgebraicGeometry.IsFinite ((Over.post B.inclusion).map t).left]
    [((Over.post (X := B.obj hS) B.inclusion).obj U).left.IsSeparated]
    [IsLocallyNoetherian ((Over.post (X := B.obj hS) B.inclusion).obj U).left]
    (x : points B S hS X) (hdim : localRingDimension B S hS x ≤ 1)
    (y₀ : points B S hS (yoneda.obj U)) (hy₀ : pointsMap B S hS (yoneda.obj U) g y₀ = x) :
    ∃ W : ((BigFppfOver.toScheme B S hS).obj U).Opens,
      IsAffineOpen W ∧ pointsToScheme B S hS U y₀ ∈ W ∧
        ∀ r : (BigFppfOver.toScheme B S hS).obj R,
          (BigFppfOver.toScheme B S hS).map t r ∈ W →
            (BigFppfOver.toScheme B S hS).map s r ∈ W := by
  have := isEquivalenceRelation_of_isPullback B S hS g s t hK
  refine exists_isAffineOpen_mem_forall_mem_of_isEquivalenceRelation
    ((Over.post B.inclusion).map s) ((Over.post B.inclusion).map t)
    (pointsToScheme B S hS U y₀) fun r hr => ?_
  let ρ := (pointsEquivScheme B S hS R).symm r
  have hρ : pointsToScheme B S hS R ρ = r := pointsToScheme_pointsEquivScheme_symm B S hS R r
  have htρ : pointsMap B S hS (yoneda.obj R) (yoneda.map t) ρ = y₀ :=
    pointsMap_yoneda_map_pointsEquivScheme_symm_eq B S hS t r y₀ hr
  have hy : pointsMap B S hS (yoneda.obj U) g
      (pointsMap B S hS (yoneda.obj R) (yoneda.map s) ρ) = x := by
    rw [← pointsMap_comp_apply, hK.w, pointsMap_comp_apply, htρ, hy₀]
  have h := krullDimLE_one_stalk_of_localRingDimension_le_one B S hS hX U g hgfin x hdim _ hy
  rwa [pointsToScheme_pointsMap_yoneda, hρ] at h

/-- The points of an open `W` of the scheme underlying `U`, seen through the open subobject
`W ⟶ U`, are the points of `U` lying in `W`. -/
private theorem range_pointsMap_yoneda_openSubobjectHom (U : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    Set.range (pointsMap B S hS (yoneda.obj (openSubobject B S hS U W.ι inferInstance))
      (yoneda.map (openSubobjectHom B S hS U W.ι inferInstance))) =
      pointsToScheme B S hS U ⁻¹' W := by
  have hTjW := toScheme_map_openSubobjectHom B S hS U W.ι inferInstance
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    have hmem : W.ι (pointsToScheme B S hS _ w) ∈ Set.range W.ι := ⟨_, rfl⟩
    rw [Scheme.Opens.range_ι] at hmem
    rwa [Set.mem_preimage, pointsToScheme_pointsMap_yoneda, hTjW]
  · intro hz
    obtain ⟨q, hq⟩ : pointsToScheme B S hS U z ∈ Set.range W.ι := by
      rwa [Scheme.Opens.range_ι]
    exact ⟨_, pointsMap_yoneda_map_pointsEquivScheme_symm_eq B S hS
      (openSubobjectHom B S hS U W.ι inferInstance) q z (by rwa [hTjW])⟩

/-- A set of points of `U` that is invariant under the kernel pair `s, t` of `g : U ⟶ X` is
saturated for `g`. -/
private theorem preimage_image_pointsMap_eq_of_forall_mem {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {R U : BigFppfOver B S hS} (g : yoneda.obj U ⟶ X) (s t : R ⟶ U)
    (hK : IsPullback (yoneda.map s) (yoneda.map t) g g)
    (W : Set ((BigFppfOver.toScheme B S hS).obj U))
    (hW : ∀ r : (BigFppfOver.toScheme B S hS).obj R,
      (BigFppfOver.toScheme B S hS).map t r ∈ W → (BigFppfOver.toScheme B S hS).map s r ∈ W) :
    pointsMap B S hS (yoneda.obj U) g ⁻¹'
        (pointsMap B S hS (yoneda.obj U) g '' (pointsToScheme B S hS U ⁻¹' W)) =
      pointsToScheme B S hS U ⁻¹' W := by
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
  rintro z ⟨w, hw, hwz⟩
  obtain ⟨ρ, hρs, hρt⟩ := exists_point_of_isPullback_presheaf B S hS hK z w hwz.symm
  rw [Set.mem_preimage, ← hρs, pointsToScheme_pointsMap_yoneda]
  exact hW _ (by rwa [← pointsToScheme_pointsMap_yoneda, hρt])

/-- A morphism `τ` into a subfunctor `H` of `X` is surjective on points when its composite `φ`
with `H ⟶ X` has the same image on points as `H`. -/
private theorem isSurjective_of_comp_ι_eq {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (H : Subfunctor X) (τ : Y ⟶ H.toFunctor) (φ : Y ⟶ X) (hτ : τ ≫ H.ι = φ)
    (hrange : Set.range (pointsMap B S hS H.toFunctor H.ι) = Set.range (pointsMap B S hS Y φ)) :
    IsSurjective B S hS τ := fun z => by
  obtain ⟨w, hw⟩ : pointsMap B S hS H.toFunctor H.ι z ∈ Set.range (pointsMap B S hS Y φ) :=
    hrange ▸ ⟨z, rfl⟩
  exact ⟨w, pointsMap_injective_of_mono B S hS H.ι (by rwa [← pointsMap_comp_apply, hτ])⟩

/-- The [Stacks, Tag 0ABI] step of the proof of [Stacks, Tag 0ADD]. Let `X` be a separated,
locally Noetherian algebraic space over `S`, let `g : U ⟶ X` be a finite surjective morphism
from the functor of points of a scheme `U`, and let `x` be a point of `X` whose local ring has
dimension at most one. Then there are an open subspace `H` of `X` containing `x`, an object
`W` of the big fppf site of `S` with affine underlying scheme, and a finite surjective
morphism `W ⟶ H`.

The kernel pair of `g` is a groupoid scheme on `U` with finite source and target, `U` is
separated and locally Noetherian, and the points of `U` over `x` have local rings of dimension
at most one; [Stacks, Tag 0ABI] gives an invariant affine open of `U` over `x`, whose image in
`X` is open because `|U| → |X|` is closed and surjective, and the restriction of `g` over that
image is a base change of `g`. No tag is registered: this is one step of the source's proof. -/
theorem exists_isOpenSubspace_isFinite_isSurjective_affine_of_localRingDimension_le_one
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hsep : IsAbsolutelySeparated B S hS B.contains_terminal X)
    (hnoeth : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ X)
    (hgfin : IsFinite B S hS g) (hgsurj : IsSurjective B S hS g)
    (x : points B S hS X) (hdim : localRingDimension B S hS x ≤ 1) :
    ∃ (H : Subfunctor X) (W : BigFppfOver B S hS) (t : yoneda.obj W ⟶ H.toFunctor),
      IsOpenSubspace B S hS H ∧ x ∈ Set.range (pointsMap B S hS H.toFunctor H.ι) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) ∧ IsFinite B S hS t ∧
        IsSurjective B S hS t := by
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  obtain ⟨hrep, hgrep⟩ := (isFinite_iff_representable B S hS g hU hX).1 hgfin
  -- The kernel pair `R = U ×_X U`, with its two projections `s` and `t`.
  let R : BigFppfOver B S hS := hrep.pullback g
  let s : R ⟶ U := hrep.fst' g
  let t : R ⟶ U := hrep.snd g
  have hK : IsPullback (yoneda.map s) (yoneda.map t) g g := hrep.isPullback' g
  have : _root_.AlgebraicGeometry.IsFinite ((Over.post B.inclusion).map s).left :=
    hgrep.property g (yoneda.map t) s hK.flip
  have : _root_.AlgebraicGeometry.IsFinite ((Over.post B.inclusion).map t).left :=
    hgrep.property g (yoneda.map s) t hK
  -- `U` is separated and locally Noetherian.
  have : ((Over.post (X := B.obj hS) B.inclusion).obj U).left.IsSeparated :=
    isSeparated_toScheme_obj_of_isAbsolutelySeparated B S hS B.contains_terminal U
      (isAbsolutelySeparated_of_isSeparated B S hS B.contains_terminal hsep
        (isSeparated_of_isFinite B S hS g hU hX hgfin))
  have : IsLocallyNoetherian ((Over.post (X := B.obj hS) B.inclusion).obj U).left :=
    (exists_atlas_iff_of_representable B S hS (yoneda.obj U)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) U (Iso.refl _)).1
      (isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hU hX g
        (isLocallyOfFiniteType_of_isFinite B S hS hU hX hgfin) hnoeth)
  -- A point of `U` over `x`, and an invariant affine open `W` of `U` containing it.
  obtain ⟨y₀, hy₀⟩ := hgsurj x
  obtain ⟨W, hWaff, hy₀W, hWinv⟩ :=
    exists_isAffineOpen_mem_forall_mem_of_isPullback B S hS hX g hgfin s t hK x hdim y₀ hy₀
  -- `W` as an object of the site, and its open immersion into `U`.
  let Wo : BigFppfOver B S hS := openSubobject B S hS U W.ι inferInstance
  let jW : Wo ⟶ U := openSubobjectHom B S hS U W.ι inferInstance
  have hWo : IsAlgebraicSpace B S hS (yoneda.obj Wo) := isAlgebraicSpace_yoneda B S hS Wo
  -- The points of `W`, as a subset of the points of `U`: open and saturated for `g`.
  let A := Set.range (pointsMap B S hS (yoneda.obj Wo) (yoneda.map jW))
  have hA : A = pointsToScheme B S hS U ⁻¹' W := range_pointsMap_yoneda_openSubobjectHom B S hS U W
  have hAopen : IsOpen A := hA ▸ W.isOpen.preimage (schemePointsHomeomorph B S hS U).continuous
  have hAsat : pointsMap B S hS (yoneda.obj U) g ⁻¹' (pointsMap B S hS (yoneda.obj U) g '' A) =
      A := hA ▸ preimage_image_pointsMap_eq_of_forall_mem B S hS g s t hK W hWinv
  -- The open subspace `H` cut out by the image of `W`.
  have hOpen := isOpen_image_pointsMap_of_isFinite_of_isSurjective B S hS hX hU g hgfin hgsurj
    A hAopen hAsat
  let H' := (openSubspacesOrderIso B S hS X hX).symm ⟨_, hOpen⟩
  have hHrange : Set.range (pointsMap B S hS H'.1.toFunctor H'.1.ι) =
      pointsMap B S hS (yoneda.obj U) g '' A :=
    congrArg TopologicalSpace.Opens.carrier ((openSubspacesOrderIso B S hS X hX).apply_symm_apply _)
  have hrange : Set.range (pointsMap B S hS H'.1.toFunctor H'.1.ι) =
      Set.range (pointsMap B S hS (yoneda.obj Wo) (yoneda.map jW ≫ g)) := by
    rw [hHrange, pointsMap_comp, Set.range_comp]
  -- The restriction `W ⟶ H` of `g`: a base change of `g`.
  obtain ⟨τ, hτ⟩ := (factorsThrough_openSubspace_iff_points B S hS hX hWo H'.1 H'.2
    (yoneda.map jW ≫ g)).2 hrange.symm.subset
  have hpb : IsPullback (yoneda.map jW) τ g H'.1.ι :=
    isPullback_of_isOpenImmersion_of_preimage_range B S hS hWo hU hX (yoneda.map jW)
      (isOpenImmersion_yoneda_map_openSubobjectHom B S hS U W.ι inferInstance) g
      H'.1 H'.2 τ hτ.symm (by rw [hHrange, hAsat])
  exact ⟨H'.1, Wo, τ, H'.2, hHrange ▸ ⟨y₀, by rwa [hA], hy₀⟩, hWaff,
    isFinite_of_isPullback B S hS hpb hgfin, isSurjective_of_comp_ι_eq B S hS H'.1 τ _ hτ hrange⟩

end AlgebraicGeometry.Space

end
