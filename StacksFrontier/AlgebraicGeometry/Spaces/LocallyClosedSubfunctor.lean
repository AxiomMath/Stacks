module

public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValuedColimit
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.ImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.FiniteGroupoidThickening
public import StacksFrontier.AlgebraicGeometry.Morphisms.IdealCutOut
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionAffine

/-!
# Subfunctors of an algebraic space cut out by ideals on affine étale charts

Let `X` be an algebraic space over `S` and `Z ⊆ X` a subfunctor which is local on the source for
the étale topology, and which on affine étale charts `V ⟶ X` through every point of `X` is cut
out by two ideals `I, J ⊆ Γ(V, 𝒪_V)`: a morphism `t : T ⟶ V` from an affine scheme lands in `Z`
exactly when `I` maps to zero and `J` generates the unit ideal of `Γ(T, 𝒪_T)`. Then `Z` is an
algebraic space and `Z ⟶ X` is an immersion; it is a closed immersion when every `J` is the unit
ideal, and of finite presentation when every `I` and `J` is finitely generated.

## Main definitions

* `AlgebraicGeometry.Space.IsEtaleLocalOnSource Z`: membership in `Z` is étale local on the
  source.
* `AlgebraicGeometry.Space.IsCutOutBy Z w I J`: on the scheme chart `w`, `Z` is cut out by
  `I, J` on affine test objects.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_and_isImmersion_of_isCutOutBy`
* `AlgebraicGeometry.Space.isClosedImmersion_ι_of_isCutOutBy`
* `AlgebraicGeometry.Space.isFinitePresentation_ι_of_isCutOutBy`

## Implementation notes

On an affine chart the subfunctor is the functor of points of the locally closed subscheme
`AlgebraicGeometry.Scheme.cutOut I J` (`V(I) ∩ D(J)`): on affine test objects this is the
cut-out condition, and both sides are Zariski local. The subfunctor is then an fppf sheaf,
because on each chart it is a representable one. The affine charts are refined to a family of
affine schemes étale over an atlas of `X`, indexed by the affine opens of the atlas and finite
over each, so that their disjoint union lies in the site; over that disjoint union the
subfunctor is the functor of points of the disjoint union of the cut-out subschemes, which is an
immersion by Zariski locality at the target. Stacks 03I2 for immersions
(`AlgebraicGeometry.Space.isAlgebraicSpace_and_isImmersion_of_surjectiveEtaleChart`) concludes,
and the remaining properties are tested on the same chart by Stacks 02WZ.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Membership in a subfunctor `Z` of `X` is *local on the source for the étale topology*: a
section `x ∈ X(T)` lies in `Z` as soon as every point of `T` lies in the image of an étale chart
of `T` on which `x` restricts into `Z`. -/
def IsEtaleLocalOnSource (Z : Subfunctor X) : Prop :=
  ∀ (T : BigFppfOver B S hS) (x : X.obj (op T)),
    (∀ y : points B S hS (yoneda.obj T), ∃ W : SmallEtale B S hS (yoneda.obj T),
      y ∈ Set.range (pointsMap B S hS (yoneda.obj W.1.left) W.1.hom) ∧
        X.map (yonedaEquiv W.1.hom).op x ∈ Z.obj (op W.1.left)) →
      x ∈ Z.obj (op T)

/-- On the scheme chart `w : W ⟶ X`, the subfunctor `Z` is *cut out by the ideals `I, J`* of
`Γ(W, 𝒪_W)`: a morphism `t : T ⟶ W` from an affine object of the site lands in `Z` exactly
when `I` maps to zero and `J` generates the unit ideal of `Γ(T, 𝒪_T)`. -/
def IsCutOutBy (Z : Subfunctor X) {W : BigFppfOver B S hS} (w : yoneda.obj W ⟶ X)
    (I J : Ideal Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) : Prop :=
  ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) → ∀ t : T ⟶ W,
    (X.map t.op (yonedaEquiv w) ∈ Z.obj (op T) ↔
      I.map ((BigFppfOver.toScheme B S hS).map t).appTop.hom = ⊥ ∧
        J.map ((BigFppfOver.toScheme B S hS).map t).appTop.hom = ⊤)

/-- Restricting the section `yonedaEquiv w` along `t` gives the value of `w` at `t`. -/
theorem map_op_yonedaEquiv {W T : BigFppfOver B S hS} (w : yoneda.obj W ⟶ X) (t : T ⟶ W) :
    X.map t.op (yonedaEquiv w) = w.app (op T) t := by
  rw [yonedaEquiv_naturality]
  rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- A cut-out description restricts along a morphism of charts. -/
theorem IsCutOutBy.comp {Z : Subfunctor X} {W W' : BigFppfOver B S hS} {w : yoneda.obj W ⟶ X}
    {I J : Ideal Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)} (h : IsCutOutBy Z w I J)
    (m : W' ⟶ W) :
    IsCutOutBy Z (yoneda.map m ≫ w) (I.map ((BigFppfOver.toScheme B S hS).map m).appTop.hom)
      (J.map ((BigFppfOver.toScheme B S hS).map m).appTop.hom) := by
  intro T hT t
  have h1 : X.map t.op (yonedaEquiv (yoneda.map m ≫ w)) = X.map (t ≫ m).op (yonedaEquiv w) := by
    rw [map_op_yonedaEquiv, map_op_yonedaEquiv]
    rfl
  have h2 : ((BigFppfOver.toScheme B S hS).map (t ≫ m)).appTop.hom =
      ((BigFppfOver.toScheme B S hS).map t).appTop.hom.comp
        ((BigFppfOver.toScheme B S hS).map m).appTop.hom := by
    rw [Functor.map_comp, Scheme.Hom.comp_appTop]
    rfl
  rw [h1, h T hT (t ≫ m), h2, Ideal.map_map, Ideal.map_map]

/-- Étale locality on the source, tested on a jointly surjective family of étale morphisms of
the site. -/
theorem IsEtaleLocalOnSource.mem_of_family {Z : Subfunctor X} (hZ : IsEtaleLocalOnSource Z)
    {T : BigFppfOver B S hS} (x : X.obj (op T)) {ι : Type*} {W : ι → BigFppfOver B S hS}
    (w : ∀ i, W i ⟶ T) (hw : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (w i)))
    (hcov : ∀ p : (BigFppfOver.toScheme B S hS).obj T,
      ∃ i, p ∈ Set.range ((BigFppfOver.toScheme B S hS).map (w i)).base)
    (hmem : ∀ i, X.map (w i).op x ∈ Z.obj (op (W i))) : x ∈ Z.obj (op T) := by
  refine hZ T x fun y => ?_
  obtain ⟨i, hi⟩ := hcov (pointsEquivScheme B S hS T y)
  refine ⟨⟨CostructuredArrow.mk (yoneda.map (w i)),
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (w i)).2 (hw i)⟩, ?_, ?_⟩
  · show y ∈ Set.range (pointsMap B S hS (yoneda.obj (W i)) (yoneda.map (w i)))
    rw [range_pointsMap_yoneda_map]
    exact ⟨_, hi, (pointsEquivScheme B S hS T).symm_apply_apply y⟩
  · show X.map (yonedaEquiv (yoneda.map (w i))).op x ∈ _
    rw [yonedaEquiv_yoneda_map]
    exact hmem i

/-- A jointly surjective family of étale morphisms of the site generates a covering sieve. -/
theorem sieve_generate_ofArrows_mem_topology_of_etale {T : BigFppfOver B S hS} {ι : Type*}
    {W : ι → BigFppfOver B S hS} (w : ∀ i, W i ⟶ T)
    (hw : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (w i)))
    (hcov : ∀ p : (BigFppfOver.toScheme B S hS).obj T,
      ∃ i, p ∈ Set.range ((BigFppfOver.toScheme B S hS).map (w i)).base) :
    Sieve.generate (Presieve.ofArrows W w) ∈ BigFppfOver.topology B S hS T :=
  BigFppfOver.sieve_generate_ofArrows_mem_topology W w
    (Scheme.etalePrecoverage_le_fppfPrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff _).2 ⟨hcov, hw⟩))

/-- Every object of the site is covered by a family of affine open subobjects. -/
theorem exists_affine_open_family (T : BigFppfOver B S hS) :
    ∃ (ι : Type u) (V : ι → BigFppfOver B S hS) (π : ∀ i, V i ⟶ T),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (V i))) ∧
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (π i))) ∧
      ∀ p : (BigFppfOver.toScheme B S hS).obj T,
        ∃ i, p ∈ Set.range ((BigFppfOver.toScheme B S hS).map (π i)).base := by
  choose V π hπ hrange hV using BigFppfOver.exists_affineOpen_restrict B S hS T
  refine ⟨_, V, π, hV, hπ, fun p => ?_⟩
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top _).ge (Set.mem_univ p))
  refine ⟨i, ?_⟩
  have := hrange i
  show p ∈ Set.range ((BigFppfOver.toScheme B S hS).map (π i))
  rw [this]
  exact hi

/-! ### The subfunctor on an affine chart is the functor of points of `V(I) ∩ D(J)` -/

/-- The subobject generated by an immersion has an immersion as its arrow. -/
theorem isImmersion_arrow_mk {A Y : Scheme.{u}} (f : Y ⟶ A)
    [_root_.AlgebraicGeometry.IsImmersion f] :
    _root_.AlgebraicGeometry.IsImmersion (Subobject.mk f).arrow := by
  rw [← Subobject.underlyingIso_hom_comp_eq_mk]
  infer_instance

/-- A morphism `t : T ⟶ W` is a point of the subscheme `Subobject.mk f` exactly when its image
under `BigFppfOver.toScheme` factors through `f`. -/
theorem mem_subschemePoints_mk_iff {W T : BigFppfOver B S hS} {Y : Scheme.{u}}
    (f : Y ⟶ (BigFppfOver.toScheme B S hS).obj W) [Mono f] (t : T ⟶ W) :
    t ∈ (subschemePoints B S hS (Subobject.mk f)).obj (op T) ↔
      ∃ h, h ≫ f = (BigFppfOver.toScheme B S hS).map t := by
  rw [mem_subschemePoints_iff, Subobject.mk_factors_iff]
  rfl

/-- A morphism `t : T ⟶ W` lies in the preimage of `Z` under `w` exactly when the restriction of
`yonedaEquiv w` along `t` lies in `Z`. -/
theorem mem_preimage_iff_map {Z : Subfunctor X} {W T : BigFppfOver B S hS}
    (w : yoneda.obj W ⟶ X) (t : T ⟶ W) :
    t ∈ (Z.preimage w).obj (op T) ↔ X.map t.op (yonedaEquiv w) ∈ Z.obj (op T) := by
  rw [map_op_yonedaEquiv]
  rfl

/-- A morphism lies in the subscheme `Subobject.mk f` of an immersion `f` as soon as it does on a
covering sieve. -/
private theorem mem_subschemePoints_mk_of_sieve {W T : BigFppfOver B S hS} {Y : Scheme.{u}}
    (f : Y ⟶ (BigFppfOver.toScheme B S hS).obj W)
    [_root_.AlgebraicGeometry.IsImmersion f] (t : T ⟶ W) {R : Sieve T}
    (hR : R ∈ BigFppfOver.topology B S hS T)
    (h : R ≤ (subschemePoints B S hS (Subobject.mk f)).sieveOfSection (U := op T) t) :
    t ∈ (subschemePoints B S hS (Subobject.mk f)).obj (op T) := by
  obtain ⟨V, i, e, he⟩ := exists_presentation B S hS _ (isImmersion_arrow_mk f)
  exact mem_subschemePoints_of_sieveOfSection B S hS i e he t
    ((BigFppfOver.topology B S hS).superset_covering h hR)

/-- A morphism lies in the subscheme `Subobject.mk f` of an immersion `f` as soon as its
restrictions to an open cover of its source do. -/
private theorem mem_subschemePoints_mk_of_openCover {W T : BigFppfOver B S hS} {Y : Scheme.{u}}
    (f : Y ⟶ (BigFppfOver.toScheme B S hS).obj W)
    [_root_.AlgebraicGeometry.IsImmersion f] (t : T ⟶ W) {ι : Type*} {V : ι → BigFppfOver B S hS}
    (π : ∀ i, V i ⟶ T)
    (hπ : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (π i)))
    (hcov : ∀ p : (BigFppfOver.toScheme B S hS).obj T,
      ∃ i, p ∈ Set.range ((BigFppfOver.toScheme B S hS).map (π i)).base)
    (h : ∀ k, π k ≫ t ∈ (subschemePoints B S hS (Subobject.mk f)).obj (op (V k))) :
    t ∈ (subschemePoints B S hS (Subobject.mk f)).obj (op T) := by
  refine mem_subschemePoints_mk_of_sieve f t
    (sieve_generate_ofArrows_mem_topology_of_etale π (fun k => by have := hπ k; infer_instance)
      hcov) ?_
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨k⟩
  exact h k

/-- **On an affine chart where it is cut out by `I, J`, an étale-local subfunctor is the functor
of points of the locally closed subscheme `V(I) ∩ D(J)`**, on all test objects and not only on
affine ones. -/
theorem preimage_eq_subschemePoints_of_isCutOutBy {Z : Subfunctor X}
    (hZ : IsEtaleLocalOnSource Z) {W : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] {w : yoneda.obj W ⟶ X}
    {I J : Ideal Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)} (h : IsCutOutBy Z w I J) :
    Z.preimage w = subschemePoints B S hS (Subobject.mk (Scheme.cutOutι I J)) := by
  have haff : ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      ∀ t : T ⟶ W, t ∈ (Z.preimage w).obj (op T) ↔
        t ∈ (subschemePoints B S hS (Subobject.mk (Scheme.cutOutι I J))).obj (op T) := by
    intro T hT t
    rw [mem_preimage_iff_map, h T hT t, mem_subschemePoints_mk_iff,
      Scheme.exists_comp_cutOutι_iff_of_isAffine]
  refine le_antisymm (fun T t ht => ?_) (fun T t ht => ?_)
  · obtain ⟨ι, V', π, hV', hπ, hcov⟩ := exists_affine_open_family T.unop
    exact mem_subschemePoints_mk_of_openCover _ t π hπ hcov fun k =>
      (haff _ (hV' k) _).1 ((Z.preimage w).map (π k).op ht)
  · obtain ⟨ι, V', π, hV', hπ, hcov⟩ := exists_affine_open_family T.unop
    rw [mem_preimage_iff_map]
    refine hZ.mem_of_family _ π (fun k => by have := hπ k; infer_instance) hcov fun k => ?_
    rw [← Functor.map_comp_apply, ← op_comp, ← mem_preimage_iff_map]
    exact (haff _ (hV' k) _).2 ((subschemePoints B S hS _).map (π k).op ht)

/-! ### The sheaf property -/

/-- **An étale-local subfunctor which is cut out by ideals on affine étale charts through every
point is an fppf sheaf.** On each chart it is the functor of points of a scheme, and a section
which lies in the subfunctor fppf locally lies in it on the base change of every chart. -/
theorem isSheaf_of_isCutOutBy (hX : IsAlgebraicSpace B S hS X) {Z : Subfunctor X}
    (hZ : IsEtaleLocalOnSource Z)
    (hchart : ∀ x : points B S hS X, ∃ V : SmallEtale B S hS X,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      IsAffine (chartScheme V) ∧ ∃ I J : Ideal Γ(chartScheme V, ⊤), IsCutOutBy Z V.1.hom I J) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z.toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type,
    Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type _ _).1 hX.isSheaf)]
  intro T x hx
  refine hZ T.unop x fun y => ?_
  set xT : yoneda.obj T.unop ⟶ X := yonedaEquiv.symm x with hxT
  obtain ⟨V, ⟨v, hv⟩, hVaff, I, J, hcut⟩ := hchart (pointsMap B S hS (yoneda.obj T.unop) xT y)
  have hrep := V.2.rep
  have hsq : IsPullback (hrep.fst xT) (yoneda.map (hrep.snd xT)) V.1.hom xT := hrep.isPullback xT
  have hq : Etale ((BigFppfOver.toScheme B S hS).map (hrep.snd xT)) := V.2.property_snd xT
  obtain ⟨p, -, hp2⟩ := exists_points_of_isPullback B S hS hsq v y hv
  refine ⟨⟨CostructuredArrow.mk (yoneda.map (hrep.snd xT)),
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2 hq⟩, ⟨p, hp2⟩, ?_⟩
  show X.map (yonedaEquiv (yoneda.map (hrep.snd xT))).op x ∈ _
  rw [yonedaEquiv_yoneda_map]
  set f : hrep.pullback xT ⟶ V.1.left := yoneda.preimage (hrep.fst xT) with hf
  have hfq : yoneda.map (hrep.snd xT) ≫ xT = yoneda.map f ≫ V.1.hom := by
    rw [hf, Functor.map_preimage]
    exact hsq.w.symm
  have hx' : ∀ {W : BigFppfOver B S hS} (k : W ⟶ hrep.pullback xT),
      X.map (k ≫ hrep.snd xT).op x = X.map (k ≫ f).op (yonedaEquiv V.1.hom) := by
    intro W k
    have h1 : x = yonedaEquiv xT := by rw [hxT, Equiv.apply_symm_apply]
    rw [h1, map_op_yonedaEquiv, map_op_yonedaEquiv]
    have h2 := congrArg (fun φ => yonedaEquiv (yoneda.map k ≫ φ)) hfq
    simp only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] at h2
    simpa using h2
  have hmem : f ∈ (Z.preimage V.1.hom).obj (op (hrep.pullback xT)) := by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) := hVaff
    rw [preimage_eq_subschemePoints_of_isCutOutBy hZ hcut] at ⊢
    refine mem_subschemePoints_mk_of_sieve _ f
      ((BigFppfOver.topology B S hS).pullback_stable (hrep.snd xT) hx) ?_
    intro W k hk
    show k ≫ f ∈ _
    rw [← preimage_eq_subschemePoints_of_isCutOutBy hZ hcut, mem_preimage_iff_map, ← hx' k]
    exact hk
  have := hx' (𝟙 _)
  rw [Category.id_comp, Category.id_comp] at this
  rw [this, ← mem_preimage_iff_map]
  exact hmem

/-! ### Over a disjoint union of charts -/

/-- A morphism into an object covered by open subobjects restricts, on an open cover of its
source, to morphisms into the members of the cover. -/
theorem exists_restrict_family {ι : Type*} {W : ι → BigFppfOver B S hS} {U : BigFppfOver B S hS}
    (j : ∀ i, W i ⟶ U)
    (hj : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j i)))
    (hcov : ∀ p : (BigFppfOver.toScheme B S hS).obj U,
      ∃ i, p ∈ Set.range ((BigFppfOver.toScheme B S hS).map (j i)).base)
    {T : BigFppfOver B S hS} (t : T ⟶ U) :
    ∃ (T' : ι → BigFppfOver B S hS) (π : ∀ i, T' i ⟶ T) (s : ∀ i, T' i ⟶ W i),
      (∀ i, _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (π i))) ∧
      (∀ p : (BigFppfOver.toScheme B S hS).obj T,
        ∃ i, p ∈ Set.range ((BigFppfOver.toScheme B S hS).map (π i)).base) ∧
      ∀ i, s i ≫ j i = π i ≫ t := by
  have key : ∀ i, ∃ (T' : BigFppfOver B S hS) (π : T' ⟶ T) (s : T' ⟶ W i),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map π) ∧
      Set.range ((BigFppfOver.toScheme B S hS).map π).base =
        ((BigFppfOver.toScheme B S hS).map t).base ⁻¹'
          Set.range ((BigFppfOver.toScheme B S hS).map (j i)).base ∧
      s ≫ j i = π ≫ t := by
    intro i
    obtain ⟨T', π, hπ, hrange, -⟩ := exists_restrict_bigFppfOver T
      ((BigFppfOver.toScheme B S hS).map t ⁻¹ᵁ ((BigFppfOver.toScheme B S hS).map (j i)).opensRange)
    have hrange' : Set.range ((BigFppfOver.toScheme B S hS).map π).base =
        ((BigFppfOver.toScheme B S hS).map t).base ⁻¹'
          Set.range ((BigFppfOver.toScheme B S hS).map (j i)).base := hrange
    obtain ⟨s, hs⟩ := exists_comp_eq_of_isOpenImmersion (j i) (hj i) (π ≫ t) (by
      rintro _ ⟨x, rfl⟩
      have hx : ((BigFppfOver.toScheme B S hS).map π).base x ∈
          Set.range ((BigFppfOver.toScheme B S hS).map π).base := ⟨x, rfl⟩
      rw [hrange'] at hx
      rw [Functor.map_comp, Scheme.Hom.comp_base]
      exact hx)
    exact ⟨T', π, s, hπ, hrange', hs⟩
  choose T' π s hπ hrange hs using key
  refine ⟨T', π, s, hπ, fun p => ?_, hs⟩
  obtain ⟨i, hi⟩ := hcov (((BigFppfOver.toScheme B S hS).map t).base p)
  refine ⟨i, ?_⟩
  rw [hrange i]
  exact hi

/-- A morphism `s` lies in the preimage of `Z` under `yoneda.map j ≫ g` exactly when `s ≫ j` lies
in the preimage of `Z` under `g`. -/
theorem mem_preimage_comp_iff {Z : Subfunctor X} {W U T : BigFppfOver B S hS} (j : W ⟶ U)
    (g : yoneda.obj U ⟶ X) (s : T ⟶ W) :
    s ∈ (Z.preimage (yoneda.map j ≫ g)).obj (op T) ↔ s ≫ j ∈ (Z.preimage g).obj (op T) :=
  Iff.rfl

variable {ι : Type u} {W : ι → BigFppfOver B S hS} {U : BigFppfOver B S hS}

/-- The disjoint union of subschemes of the members of a disjoint union, as a morphism into it. -/
noncomputable abbrev sigmaSubschemeι (j : ∀ i, W i ⟶ U) {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ (BigFppfOver.toScheme B S hS).obj (W i)) :
    ∐ Y ⟶ (BigFppfOver.toScheme B S hS).obj U :=
  Sigma.desc fun i => f i ≫ (BigFppfOver.toScheme B S hS).map (j i)

/-- `sigmaSubschemeι j f` is the coproduct of the maps `f i` followed by the map from the
coproduct of the `W i` to `U` induced by `j`. -/
theorem sigmaSubschemeι_eq (j : ∀ i, W i ⟶ U) {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ (BigFppfOver.toScheme B S hS).obj (W i)) :
    sigmaSubschemeι j f =
      Limits.Sigma.map f ≫ Sigma.desc fun i => (BigFppfOver.toScheme B S hS).map (j i) := by
  ext i
  simp

/-- If the schemes of a family of objects form a coproduct, the induced map from their coproduct
is an isomorphism. -/
private theorem isIso_sigma_desc_map_of_isColimit (j : ∀ i, W i ⟶ U)
    (hc : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj U)
      fun i => (BigFppfOver.toScheme B S hS).map (j i))) :
    IsIso (Sigma.desc fun i => (BigFppfOver.toScheme B S hS).map (j i)) :=
  (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk _ _)).1 ⟨hc⟩

/-- On a disjoint union, a property of morphisms local at the target holds for the disjoint
union of subschemes as soon as it holds for each of them. -/
theorem sigmaSubschemeι_property (j : ∀ i, W i ⟶ U)
    (hc : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj U)
      fun i => (BigFppfOver.toScheme B S hS).map (j i)))
    {Y : ι → Scheme.{u}} (f : ∀ i, Y i ⟶ (BigFppfOver.toScheme B S hS).obj (W i))
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P] (hP : ∀ i, P (f i)) :
    P (sigmaSubschemeι j f) := by
  have hiso := isIso_sigma_desc_map_of_isColimit j hc
  rw [sigmaSubschemeι_eq]
  exact (MorphismProperty.cancel_right_of_respectsIso P _ _).2
    (sigmaMap_property_of_components P _ _ f hP)

/-- **Over a disjoint union of affine charts, an étale-local subfunctor which is the functor of
points of a subscheme of every member is the functor of points of their disjoint union.** -/
theorem preimage_eq_subschemePoints_sigma {Z : Subfunctor X} (hZ : IsEtaleLocalOnSource Z)
    (j : ∀ i, W i ⟶ U)
    (hj : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (j i)))
    (hcov : ∀ p : (BigFppfOver.toScheme B S hS).obj U,
      ∃ i, p ∈ Set.range ((BigFppfOver.toScheme B S hS).map (j i)).base)
    (hc : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj U)
      fun i => (BigFppfOver.toScheme B S hS).map (j i)))
    (g : yoneda.obj U ⟶ X) {Y : ι → Scheme.{u}}
    (f : ∀ i, Y i ⟶ (BigFppfOver.toScheme B S hS).obj (W i))
    [∀ i, _root_.AlgebraicGeometry.IsImmersion (f i)]
    (hY : ∀ i, Z.preimage (yoneda.map (j i) ≫ g) = subschemePoints B S hS (Subobject.mk (f i))) :
    have : _root_.AlgebraicGeometry.IsImmersion (sigmaSubschemeι j f) :=
      sigmaSubschemeι_property j hc f _ fun _ => inferInstance
    Z.preimage g = subschemePoints B S hS (Subobject.mk (sigmaSubschemeι j f)) := by
  intro this
  have hiso := isIso_sigma_desc_map_of_isColimit j hc
  refine le_antisymm (fun T t ht => ?_) (fun T t ht => ?_)
  · obtain ⟨T', π, s, hπ, hπcov, hs⟩ := exists_restrict_family j hj hcov t
    refine mem_subschemePoints_mk_of_openCover _ t π hπ hπcov fun k => ?_
    have hsk : s k ∈ (Z.preimage (yoneda.map (j k) ≫ g)).obj (op (T' k)) := by
      rw [mem_preimage_comp_iff, hs k]
      exact (Z.preimage g).map (π k).op ht
    rw [hY k, mem_subschemePoints_mk_iff] at hsk
    obtain ⟨h, hh⟩ := hsk
    rw [mem_subschemePoints_mk_iff]
    refine ⟨h ≫ Sigma.ι _ k, ?_⟩
    rw [Category.assoc, Sigma.ι_desc, ← Category.assoc, hh, ← Functor.map_comp, hs k]
  · obtain ⟨h, hh⟩ := (mem_subschemePoints_mk_iff _ t).1 ht
    obtain ⟨T', π, s, hπ, hπcov, hs⟩ := exists_restrict_family j hj hcov t
    show g.app T t ∈ Z.obj T
    rw [← map_op_yonedaEquiv]
    refine hZ.mem_of_family _ π (fun k => by have := hπ k; infer_instance) hπcov fun k => ?_
    rw [← Functor.map_comp_apply, ← op_comp, ← mem_preimage_iff_map, ← hs k,
      ← mem_preimage_comp_iff, hY k, mem_subschemePoints_mk_iff]
    have hpb := sigmaMap_component_pullback Y (fun i => (BigFppfOver.toScheme B S hS).obj (W i))
      f k
    have hw : (BigFppfOver.toScheme B S hS).map (s k) ≫
        Sigma.ι (fun i => (BigFppfOver.toScheme B S hS).obj (W i)) k =
        ((BigFppfOver.toScheme B S hS).map (π k) ≫ h) ≫ Limits.Sigma.map f := by
      rw [← cancel_mono (Sigma.desc fun i => (BigFppfOver.toScheme B S hS).map (j i)),
        Category.assoc, Sigma.ι_desc, Category.assoc, Category.assoc, ← sigmaSubschemeι_eq, hh,
        ← Functor.map_comp, ← Functor.map_comp, hs k]
    exact ⟨hpb.lift _ _ hw, hpb.lift_fst _ _ _⟩

/-- **A subfunctor whose preimage on a chart is the functor of points of an immersed subscheme
`Z'` is, after base change to the chart, representable by `Z' ⟶ U`**: its base change has every
base-change stable property of `Z'.arrow`. -/
theorem presheaf_snd_of_preimage_eq_subschemePoints {Z : Subfunctor X} {U : BigFppfOver B S hS}
    (g : yoneda.obj U ⟶ X) (Z' : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (hZ' : _root_.AlgebraicGeometry.IsImmersion Z'.arrow)
    (h : Z.preimage g = subschemePoints B S hS Z')
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] (hP : P Z'.arrow) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd Z.ι g) := by
  have hRI : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hRI' : (MorphismProperty.presheaf
      (P.inverseImage (BigFppfOver.toScheme B S hS))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
      (P.inverseImage (BigFppfOver.toScheme B S hS))).respectsIso
  obtain ⟨V, i, e, hei⟩ := exists_presentation B S hS Z' hZ'
  have hmono : Mono ((BigFppfOver.toScheme B S hS).map i) :=
    mono_toScheme_map_of_presentation B S hS i e hei
  have : Mono i := (BigFppfOver.toScheme B S hS).mono_of_mono_map hmono
  have hrange : Subfunctor.range (yoneda.map i) = Z.preimage g := by
    rw [h, subschemePoints_eq_range B S hS i e hei]
  have hiso := Subfunctor.isIso_lift (p := yoneda.map i) hrange.le hrange.ge
  have hPi : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map i) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS P i).2
      ((property_toScheme_map_iff_of_presentation B S hS i e hei P).2 hP)
  have hfac : Subfunctor.lift (yoneda.map i) hrange.le ≫ (Z.preimage g).ι = yoneda.map i :=
    Subfunctor.lift_ι _ _
  have hPι : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (Z.preimage g).ι := by
    refine (MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.presheaf
      (P.inverseImage (BigFppfOver.toScheme B S hS)))
      (Subfunctor.lift (yoneda.map i) hrange.le) _).1 ?_
    rw [hfac]
    exact hPi
  have hpb := (Subfunctor.isPullback_fromPreimage Z g).flip
  refine (MorphismProperty.arrow_mk_iso_iff _
    (Arrow.isoMk ((IsPullback.of_hasPullback Z.ι g).flip.isoIsPullback _ _ hpb).symm
      (Iso.refl _) ?_)).1 hPι
  exact (IsPullback.of_hasPullback Z.ι g).flip.isoIsPullback_inv_fst _ _ hpb

/-! ### One surjective étale chart -/

section Chart

variable (R : ∀ {W : BigFppfOver B S hS},
  Ideal Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) →
    Ideal Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) → Prop)

/-- An affine étale neighbourhood of a point of an atlas mapping into a chart with cut-out data
satisfying `R`. -/
theorem exists_affine_etale_cutOut (_hX : IsAlgebraicSpace B S hS X) {Z : Subfunctor X}
    (hchart : ∀ x : points B S hS X, ∃ V : SmallEtale B S hS X,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      IsAffine (chartScheme V) ∧ ∃ I J : Ideal Γ(chartScheme V, ⊤), IsCutOutBy Z V.1.hom I J ∧
        R I J)
    {U₀ : BigFppfOver B S hS} (φ₀ : yoneda.obj U₀ ⟶ X) (u : (BigFppfOver.toScheme B S hS).obj U₀) :
    ∃ (A : BigFppfOver B S hS) (a : A ⟶ U₀) (V : SmallEtale B S hS X) (m : A ⟶ V.1.left)
      (I J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
      Etale ((BigFppfOver.toScheme B S hS).map a) ∧
      u ∈ Set.range ((BigFppfOver.toScheme B S hS).map a) ∧
      yoneda.map m ≫ V.1.hom = yoneda.map a ≫ φ₀ ∧ IsCutOutBy Z V.1.hom I J ∧ R I J := by
  obtain ⟨y, hy⟩ := (bijective_pointsToScheme B S hS U₀).2 u
  obtain ⟨V, ⟨v, hv⟩, -, I, J, hcut, hR⟩ := hchart (pointsMap B S hS (yoneda.obj U₀) φ₀ y)
  have hrep := V.2.rep
  have hsq : IsPullback (hrep.fst φ₀) (yoneda.map (hrep.snd φ₀)) V.1.hom φ₀ := hrep.isPullback φ₀
  have hq : Etale ((BigFppfOver.toScheme B S hS).map (hrep.snd φ₀)) := V.2.property_snd φ₀
  obtain ⟨p, -, hp2⟩ := exists_points_of_isPullback B S hS hsq v y hv
  let P := hrep.pullback φ₀
  let f : P ⟶ V.1.left := yoneda.preimage (hrep.fst φ₀)
  have hfq : yoneda.map f ≫ V.1.hom = yoneda.map (hrep.snd φ₀) ≫ φ₀ := by
    rw [Functor.map_preimage]
    exact hsq.w
  obtain ⟨_, ⟨O, hO, rfl⟩, hpO, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj P).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (pointsToScheme B S hS P p)) isOpen_univ
  let o := openSubHom P O
  refine ⟨openSub P O, o ≫ hrep.snd φ₀, V, o ≫ f, I, J, hO, ?_, ?_, ?_, hcut, hR⟩
  · rw [Functor.map_comp]
    have := etale_toScheme_map_openSubHom B S hS P O
    infer_instance
  · obtain ⟨q, hq⟩ : pointsToScheme B S hS P p ∈
        Set.range (Scheme.Opens.ι (X := (BigFppfOver.toScheme B S hS).obj P) O) := by
      rwa [Scheme.Opens.range_ι]
    have ho : (BigFppfOver.toScheme B S hS).map o = Scheme.Opens.ι O :=
      toScheme_map_openSubHom B S hS P O
    refine ⟨q, ?_⟩
    show ((BigFppfOver.toScheme B S hS).map (hrep.snd φ₀))
      (((BigFppfOver.toScheme B S hS).map o) q) = u
    rw [ho]
    refine (congrArg ((BigFppfOver.toScheme B S hS).map (hrep.snd φ₀)) hq).trans ?_
    rw [← hy, ← hp2, pointsToScheme_pointsMap_yoneda]
  · rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hfq]

/-- **One surjective étale chart on which the subfunctor is the functor of points of a disjoint
union of cut-out subschemes.** Over it, the base change of `Z ⟶ X` has every base-change stable,
Zariski-local property `P` of morphisms of schemes which holds for the cut-out immersions
`V(I) ∩ D(J) ⟶ W` of affine `W` whenever `R I J`. -/
theorem exists_chart_presheaf_snd (hX : IsAlgebraicSpace B S hS X) {Z : Subfunctor X}
    (hZ : IsEtaleLocalOnSource Z)
    (hR : ∀ {W W' : BigFppfOver B S hS} (m : W' ⟶ W)
      (I J : Ideal Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)),
      R I J → R (I.map ((BigFppfOver.toScheme B S hS).map m).appTop.hom)
        (J.map ((BigFppfOver.toScheme B S hS).map m).appTop.hom))
    (hchart : ∀ x : points B S hS X, ∃ V : SmallEtale B S hS X,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      IsAffine (chartScheme V) ∧ ∃ I J : Ideal Γ(chartScheme V, ⊤), IsCutOutBy Z V.1.hom I J ∧
        R I J) :
    ∃ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ X),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) g ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) g ∧
      ∀ (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] [IsZariskiLocalAtTarget P],
        (∀ (W : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
          (I J : Ideal Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)), R I J → P (Scheme.cutOutι I J)) →
        (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd Z.ι g) := by
  classical
  obtain ⟨U₀, φ₀, hs₀, he₀⟩ := hX.exists_atlas
  let T₀ := (BigFppfOver.toScheme B S hS).obj U₀
  let Q : T₀.affineOpens → Prop := fun O =>
    ∃ (A : BigFppfOver B S hS) (a : A ⟶ U₀) (V : SmallEtale B S hS X) (m : A ⟶ V.1.left)
      (I J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
      Etale ((BigFppfOver.toScheme B S hS).map a) ∧
      (O.1 : Set T₀) ⊆ Set.range ((BigFppfOver.toScheme B S hS).map a) ∧
      yoneda.map m ≫ V.1.hom = yoneda.map a ≫ φ₀ ∧ IsCutOutBy Z V.1.hom I J ∧ R I J
  choose A a V m I J hAaff hAet hAsub hm hcut hRk using fun k : {O // Q O} => k.2
  have hK : Cardinal.mk {O // Q O} ≤ T₀.size :=
    (Cardinal.mk_subtype_le _).trans (Scheme.mk_affineOpens_le_size T₀)
  have hAcov : ∀ x : T₀, ∃ k, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (a k)) := by
    intro x
    obtain ⟨A₀, a₀, V₀, m₀, I₀, J₀, hA₀, ha₀, hx₀, hm₀, hcut₀, hR₀⟩ :=
      exists_affine_etale_cutOut R hX hchart φ₀ x
    have hopen : IsOpen (Set.range ((BigFppfOver.toScheme B S hS).map a₀)) :=
      ((BigFppfOver.toScheme B S hS).map a₀).isOpenMap.isOpen_range
    obtain ⟨-, ⟨O, hO, rfl⟩, hxO, hOsub⟩ :=
      T₀.isBasis_affineOpens.exists_subset_of_mem_open hx₀ hopen
    exact ⟨⟨⟨O, hO⟩, A₀, a₀, V₀, m₀, I₀, J₀, hA₀, ha₀, hOsub, hm₀, hcut₀, hR₀⟩, hAsub _ hxO⟩
  have hAsize : ∀ k, ((BigFppfOver.toScheme B S hS).obj (A k)).size ≤ T₀.size := by
    intro k
    have _ := hAaff k
    have _ := hAet k
    exact Scheme.size_le_of_locallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (a k))
  obtain ⟨U, jj, q, hjq, hjopen, hjcov, hqsurj, hqet, -, -, ⟨hjsch⟩⟩ :=
    BigFppfOver.exists_surjective_etale_sigma_isColimit_of_etaleCover B S hS A U₀ a hAet hAcov
      U₀.left.property hK hAsize
  have := isMultiplicative_presheaf_surjective B S hS
  have := isMultiplicative_presheaf_etale B S hS
  refine ⟨U, yoneda.map q ≫ φ₀,
    MorphismProperty.comp_mem _ _ _
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqsurj) hs₀,
    MorphismProperty.comp_mem _ _ _
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqet) he₀, ?_⟩
  intro P _ _ hP
  let f : ∀ k, _ ⟶ (BigFppfOver.toScheme B S hS).obj (A k) := fun k =>
    Scheme.cutOutι ((I k).map ((BigFppfOver.toScheme B S hS).map (m k)).appTop.hom)
      ((J k).map ((BigFppfOver.toScheme B S hS).map (m k)).appTop.hom)
  have hPf : ∀ k, P (f k) := fun k => by
    have _ := hAaff k
    exact hP _ _ _ (hR (m k) _ _ (hRk k))
  have hYk : ∀ k, Z.preimage (yoneda.map (jj k) ≫ yoneda.map q ≫ φ₀) =
      subschemePoints B S hS (Subobject.mk (f k)) := by
    intro k
    have _ := hAaff k
    have e : yoneda.map (jj k) ≫ yoneda.map q ≫ φ₀ = yoneda.map (m k) ≫ (V k).1.hom := by
      rw [← Category.assoc, ← Functor.map_comp, hjq k, hm k]
    rw [e]
    exact preimage_eq_subschemePoints_of_isCutOutBy hZ ((hcut k).comp (m k))
  have hpre := preimage_eq_subschemePoints_sigma hZ jj hjopen hjcov hjsch (yoneda.map q ≫ φ₀) f hYk
  have himm : _root_.AlgebraicGeometry.IsImmersion (sigmaSubschemeι jj f) :=
    sigmaSubschemeι_property jj hjsch f _ fun _ => inferInstance
  have hRI : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine presheaf_snd_of_preimage_eq_subschemePoints _ (Subobject.mk (sigmaSubschemeι jj f))
    (isImmersion_arrow_mk (sigmaSubschemeι jj f)) hpre P ?_
  rw [← Subobject.underlyingIso_hom_comp_eq_mk]
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).2
    (sigmaSubschemeι_property jj hjsch f P hPf)

end Chart

/-! ### The main results -/

variable {Z : Subfunctor X}

/-- **An étale-local subfunctor cut out by ideals on affine étale charts through every point is a
locally closed subspace**: it is an algebraic space and its inclusion is an immersion. -/
theorem isAlgebraicSpace_and_isImmersion_of_isCutOutBy (hX : IsAlgebraicSpace B S hS X)
    (hZ : IsEtaleLocalOnSource Z)
    (hchart : ∀ x : points B S hS X, ∃ V : SmallEtale B S hS X,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      IsAffine (chartScheme V) ∧ ∃ I J : Ideal Γ(chartScheme V, ⊤), IsCutOutBy Z V.1.hom I J) :
    IsAlgebraicSpace B S hS Z.toFunctor ∧ IsImmersion B S hS Z.ι := by
  obtain ⟨U, g, hs, he, hP⟩ := exists_chart_presheaf_snd (fun _ _ => True) hX hZ
    (fun _ _ _ _ => trivial) fun x => by
      obtain ⟨V, hV, hA, I, J, h⟩ := hchart x
      exact ⟨V, hV, hA, I, J, h, trivial⟩
  exact isAlgebraicSpace_and_isImmersion_of_surjectiveEtaleChart
    (isSheaf_of_isCutOutBy hX hZ hchart) hX hs he
    (hP @_root_.AlgebraicGeometry.IsImmersion fun _ _ _ _ _ => inferInstance)

/-- **When every `J` is the unit ideal the subspace is closed**: its inclusion is a closed
immersion. -/
theorem isClosedImmersion_ι_of_isCutOutBy (hX : IsAlgebraicSpace B S hS X)
    (hZ : IsEtaleLocalOnSource Z)
    (hchart : ∀ x : points B S hS X, ∃ V : SmallEtale B S hS X,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      IsAffine (chartScheme V) ∧ ∃ I : Ideal Γ(chartScheme V, ⊤), IsCutOutBy Z V.1.hom I ⊤) :
    IsClosedImmersion B S hS Z.ι := by
  have hchart' : ∀ x : points B S hS X, ∃ V : SmallEtale B S hS X,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      IsAffine (chartScheme V) ∧ ∃ I J : Ideal Γ(chartScheme V, ⊤), IsCutOutBy Z V.1.hom I J ∧
        J = ⊤ := fun x => by
    obtain ⟨V, hV, hA, I, h⟩ := hchart x
    exact ⟨V, hV, hA, I, ⊤, h, rfl⟩
  obtain ⟨U, g, hs, he, hP⟩ := exists_chart_presheaf_snd (fun _ J => J = ⊤) hX hZ
    (fun _ _ _ hJ => by rw [hJ, Ideal.map_top]) hchart'
  exact (isAlgebraicSpace_and_isClosedImmersion_of_surjectiveEtaleChart
    (isSheaf_of_isCutOutBy hX hZ fun x => by
      obtain ⟨V, hV, hA, I, J, h, -⟩ := hchart' x
      exact ⟨V, hV, hA, I, J, h⟩) hX hs he
    (hP @_root_.AlgebraicGeometry.IsClosedImmersion fun _ _ I J hJ => by
      subst hJ; exact Scheme.isClosedImmersion_cutOutι_top I)).2

/-- **When every `I` and `J` is finitely generated the inclusion is of finite presentation.** -/
theorem isFinitePresentation_ι_of_isCutOutBy (hX : IsAlgebraicSpace B S hS X)
    (hZ : IsEtaleLocalOnSource Z)
    (hchart : ∀ x : points B S hS X, ∃ V : SmallEtale B S hS X,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      IsAffine (chartScheme V) ∧ ∃ I J : Ideal Γ(chartScheme V, ⊤), IsCutOutBy Z V.1.hom I J ∧
        I.FG ∧ J.FG) :
    IsFinitePresentation B S hS Z.ι := by
  have hchart₀ : ∀ x : points B S hS X, ∃ V : SmallEtale B S hS X,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj V.1.left) V.1.hom) ∧
      IsAffine (chartScheme V) ∧ ∃ I J : Ideal Γ(chartScheme V, ⊤), IsCutOutBy Z V.1.hom I J :=
    fun x => by
      obtain ⟨V, hV, hA, I, J, h, -⟩ := hchart x
      exact ⟨V, hV, hA, I, J, h⟩
  obtain ⟨hZalg, himm⟩ := isAlgebraicSpace_and_isImmersion_of_isCutOutBy hX hZ hchart₀
  obtain ⟨U, g, hs, he, hP⟩ := exists_chart_presheaf_snd (fun I J => I.FG ∧ J.FG) hX hZ
    (fun _ _ _ h => ⟨h.1.map _, h.2.map _⟩) hchart
  have hsq := IsPullback.of_hasPullback Z.ι g
  let : HasAffineProperty (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u})
      (sourceAffineLocally RingHom.FinitePresentation) :=
    HasRingHomProperty.HasAffineProperty _
  let : IsZariskiLocalAtTarget (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  let : IsZariskiLocalAtTarget (@_root_.AlgebraicGeometry.QuasiCompact.{u}) :=
    (HasAffineProperty.iff.mp
      instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat).1
  let : MorphismProperty.RespectsIso (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : MorphismProperty.RespectsIso (@_root_.AlgebraicGeometry.QuasiCompact.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.DescendsAlong (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u})
      (@Surjective ⊓ @Flat ⊓ @_root_.AlgebraicGeometry.LocallyOfFinitePresentation) :=
    descendsAlong_fppf_of_descendsAlong_fpqc _
  have : MorphismProperty.DescendsAlong (@_root_.AlgebraicGeometry.QuasiCompact.{u})
      (@Surjective ⊓ @Flat ⊓ @_root_.AlgebraicGeometry.LocallyOfFinitePresentation) :=
    descendsAlong_fppf_of_descendsAlong_fpqc _
  refine ⟨(isLocallyOfFinitePresentation_iff_presheaf B S hS hZalg hX himm.rep).2
    (presheaf_of_surjectiveEtaleChart_of_descendsAlong himm.rep hs he hsq
      (hP @_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u} fun _ _ I J h =>
        Scheme.locallyOfFinitePresentation_cutOutι I J h.1)),
    isQuasiCompact_of_presheaf_quasiCompact B S hS
      (presheaf_of_surjectiveEtaleChart_of_descendsAlong himm.rep hs he hsq
        (hP @_root_.AlgebraicGeometry.QuasiCompact.{u} fun _ _ I J h =>
          Scheme.quasiCompact_cutOutι I J h.2)),
    isQuasiSeparated_of_mono B S hS _ inferInstance⟩

end AlgebraicGeometry.Space

end
