module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.RepresentableFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesHomSheafAlgebraic

/-!
# The size bound for the sheaf of glueing-data morphisms

In a formal glueing situation write `P = homPresheaf D G` for the sheaf of glueing-data
morphisms into a triple `G` with affine legs, and `π : P ⟶ X` for its projection. Granted
clause (1) of Stacks 0AF4 over affine bases, `P` is affine over `X`, and
`AlgebraicGeometry.Space.FormalGlueingSituation.isAlgebraicSpace_homPresheaf_of_size_le` makes
it an algebraic space once its affine base changes over the opens of one chart `h_U ⟶ X` are
uniformly bounded in size. This module proves that bound, and with it the algebraicity of `P`
and the three equivalences of Stacks 0AF4 from the affine case.

The bound comes from the two legs. Let `W` represent `P ×_X V` for an open `V` of `U`. The
evaluations identify `P ×_X U` with `G_U` and `P ×_X Y` with `G_Y`; fix atlases `A_U` and `A_Y`
of them. Then `W ×_P A_•` is `V ×_X A_•`, an open of the fixed object `U ×_X A_•`, so it has size
at most `size (U ×_X A_•)`. A global section of `W` is a morphism `W ⟶ 𝔸¹_S`; by the
faithfulness of the functor of Stacks 0AF3 (whose proof uses the fpqc covering of Stacks 0AF1)
it is determined by its restrictions to `W ×_X U` and `W ×_X Y`, and these by their restrictions
along the surjective étale morphisms `W ×_P A_• ⟶ W ×_X •`. Hence `Γ(W)` injects into
`Γ(W ×_P A_U) × Γ(W ×_P A_Y)`, whose cardinality is bounded independently of `V` by
`AlgebraicGeometry.Scheme.mk_sections_le_two_pow_size`; the cutoff is a strong prelimit, so
the bound stays below it.

## Main results

All names are in the namespace `AlgebraicGeometry.Space.FormalGlueingSituation`.

* `hom_ext_of_restrictions`: morphisms out of an algebraic space over `X` are determined by their
  restrictions to `U` and to `Y`.
* `homPresheafSizeBound`: the size bound.
* `isAlgebraicSpace_homPresheaf`: `P` is an algebraic space.
* `isEquivalence_affineGlueingFunctor_of_affineBaseEssSurj`,
  `isEquivalence_closedGlueingFunctor_of_affineBaseEssSurj`,
  `isEquivalence_finiteGlueingFunctor_of_affineBaseEssSurj`: the three clauses of Stacks 0AF4,
  granted clause (1) over affine bases (`AffineBaseEssSurj`).

## References

* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
* [Stacks Project, Tag 0AF3](https://stacks.math.columbia.edu/tag/0AF3)
* [Stacks Project, Tag 000P](https://stacks.math.columbia.edu/tag/000P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
/-- Discrete limits of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_HomSheafSizeBound
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

local instance (priority := high) hasBinaryProducts_presheaf_HomSheafSizeBound :
    HasBinaryProducts ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  hasLimitsOfShape_discrete_presheaf_HomSheafSizeBound _

/-! ### The affine line over `S` in the site -/

section AffineLine

variable (B S hS)

/-- The affine line `𝔸¹_S` is contained in the big fppf site of `S`. -/
theorem contains_affineSpace_punit (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    B.Contains 𝔸(PUnit.{u + 1}; S) :=
  (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact (𝔸(PUnit.{u + 1}; S) ↘ S)).trans_lt hS

/-- The affine line over `S`, as an object of the big fppf site of `S`. -/
noncomputable abbrev affineLineSite : BigFppfOver B S hS :=
  siteObject B S hS (contains_affineSpace_punit B S hS) (𝔸(PUnit.{u + 1}; S) ↘ S)

/-- A global section of an object of the site is a morphism to the affine line. -/
theorem mk_sections_le_mk_hom_affineLineSite (W : BigFppfOver B S hS) :
    #Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) ≤ #(W ⟶ affineLineSite B S hS) := by
  refine Cardinal.mk_le_of_injective (f := fun s => Over.homMk
    (ObjectProperty.homMk (AffineSpace.homOfVector (B.inclusion.map W.hom) fun _ => s))
    (ObjectProperty.hom_ext _ (AffineSpace.homOfVector_over _ _))) ?_
  intro s s' h
  have := congrArg (fun g : W ⟶ affineLineSite B S hS =>
    g.left.hom.appTop (AffineSpace.coord S PUnit.unit)) h
  simp only [Over.homMk_left, ObjectProperty.homMk_hom] at this
  rwa [AffineSpace.homOfVector_appTop_coord, AffineSpace.homOfVector_appTop_coord] at this

/-- A morphism to the affine line is determined by a global section. -/
theorem mk_hom_affineLineSite_le_mk_sections (W : BigFppfOver B S hS) :
    #(W ⟶ affineLineSite B S hS) ≤ #Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) := by
  refine Cardinal.mk_le_of_injective
    (f := fun g : W ⟶ affineLineSite B S hS => g.left.hom.appTop (AffineSpace.coord S PUnit.unit))
    ?_
  intro g g' h
  have hw : ∀ k : W ⟶ affineLineSite B S hS, k.left.hom ≫ (𝔸(PUnit.{u + 1}; S) ↘ S) =
      (B.inclusion.map W.hom) := fun k => congrArg (fun t => t.hom) (Over.w k)
  refine Over.OverMorphism.ext (ObjectProperty.hom_ext _ (AffineSpace.hom_ext ?_ ?_))
  · rw [hw, hw]
  · intro i
    exact h

end AffineLine

/-! ### Morphisms out of a space over `X` are determined over `U` and over `Y` -/

/-- Two morphisms from an algebraic space `Z` over `X` to an algebraic space `T` agree as soon
as they agree after restriction to `Z ×_X U` and to `Z ×_X Y`. This is the faithfulness of the
functor of Stacks 0AF3, applied to the two morphisms `Z ⟶ T × X` over `X`. -/
theorem hom_ext_of_restrictions (D : FormalGlueingSituation B S hS)
    {Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    (hT : IsAlgebraicSpace B S hS T) (z : Z ⟶ D.X) {a b : Z ⟶ T}
    (hU : pullback.fst z D.U.ι ≫ a = pullback.fst z D.U.ι ≫ b)
    (hY : pullback.fst z D.f ≫ a = pullback.fst z D.f ≫ b) : a = b := by
  let X₁ : spacesOverX D := ⟨Over.mk z, hZ⟩
  let X₂ : spacesOverX D := ⟨Over.mk (prod.snd : T ⨯ D.X ⟶ D.X),
    isAlgebraicSpace_prod B S hS hT D.algebraicSpace_X⟩
  let a' : X₁ ⟶ X₂ := ObjectProperty.homMk (Over.homMk (prod.lift a z) (prod.lift_snd _ _))
  let b' : X₁ ⟶ X₂ := ObjectProperty.homMk (Over.homMk (prod.lift b z) (prod.lift_snd _ _))
  have hR : (restrictionDiagram D).map a'.hom = (restrictionDiagram D).map b'.hom := by
    refine Comma.hom_ext _ _ (Over.OverMorphism.ext (pullback.hom_ext ?_ ?_))
      (Over.OverMorphism.ext (pullback.hom_ext ?_ ?_))
    · show ((Over.pullback D.U.ι).map a'.hom).left ≫ _ =
        ((Over.pullback D.U.ι).map b'.hom).left ≫ _
      rw [overPullback_map_left_comp_fst, overPullback_map_left_comp_fst]
      refine prod.hom_ext ?_ ?_
      · simpa [a', b', X₁, X₂] using hU
      · simp [a', b', X₁, X₂]
    · show ((Over.pullback D.U.ι).map a'.hom).left ≫ _ =
        ((Over.pullback D.U.ι).map b'.hom).left ≫ _
      rw [overPullback_map_left_comp_snd, overPullback_map_left_comp_snd]
    · show ((Over.pullback D.f).map a'.hom).left ≫ _ =
        ((Over.pullback D.f).map b'.hom).left ≫ _
      rw [overPullback_map_left_comp_fst, overPullback_map_left_comp_fst]
      refine prod.hom_ext ?_ ?_
      · simpa [a', b', X₁, X₂] using hY
      · simp [a', b', X₁, X₂]
    · show ((Over.pullback D.f).map a'.hom).left ≫ _ =
        ((Over.pullback D.f).map b'.hom).left ≫ _
      rw [overPullback_map_left_comp_snd, overPullback_map_left_comp_snd]
  have key : a' = b' := by
    refine injective_formalGlueingFunctor_map D a' b' ?_
    have e := (formalGlueingFunctor D).2
    have ha := e.hom.naturality a'
    have hb := e.hom.naturality b'
    simp only [Functor.comp_map] at ha hb
    refine (ObjectProperty.ι _).map_injective ?_
    rw [← Iso.cancel_iso_hom_right _ _ (e.app X₂), Iso.app_hom, ha, hb]
    exact congrArg (e.hom.app X₁ ≫ ·) hR
  have := congrArg (fun g : X₁ ⟶ X₂ => g.hom.left ≫ prod.fst) key
  simpa [a', b'] using this

/-! ### One leg of the size bound -/

/-- A fibre product of two representables over an algebraic space is represented, as a
cartesian square of representables. -/
theorem exists_isPullback_yoneda {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {U V : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X)
    (b : yoneda.obj V ⟶ X) :
    ∃ (E : BigFppfOver B S hS) (f : yoneda.obj E ⟶ yoneda.obj U) (g : yoneda.obj E ⟶ yoneda.obj V),
      IsPullback f g a b := by
  obtain ⟨E, ⟨e⟩⟩ := (isRepresentable_pullback_yoneda B S hS hX a b).has_representation
  exact ⟨E, e.toIso.hom ≫ pullback.fst a b, e.toIso.hom ≫ pullback.snd a b,
    IsPullback.of_iso_pullback ⟨by simp only [Category.assoc, pullback.condition]⟩ e.toIso rfl rfl⟩

/-- **One leg of the size bound.** Let `π : P ⟶ X`, let `j : J ⟶ X` be a morphism from a sheaf
such that `P ×_X J` is an algebraic space, and let `x : h_U ⟶ X` be a morphism from an object
of the site. There is one cardinal `μ` below the cutoff such that whenever `W` represents the
base change of `π` to an open `V` of `U`, there is an object `E ⟶ W` of size at most `μ` along
which morphisms from `W ×_X J` to sheaves can be tested: `E` is `W ×_P A` for a fixed atlas `A` of
`P ×_X J`, an open subobject of the fixed `U ×_X A`. -/
theorem exists_legBound (D : FormalGlueingSituation B S hS)
    {P J : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : P ⟶ D.X) (j : J ⟶ D.X)
    (hJ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) J)
    (hQ : IsAlgebraicSpace B S hS (pullback π j)) {U : BigFppfOver B S hS}
    (x : yoneda.obj U ⟶ D.X) :
    ∃ μ : Cardinal.{u}, μ < B.cutoff ∧ ∀ (V : BigFppfOver B S hS) (v : V ⟶ U),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map v) →
      ∀ (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ P) (q : W ⟶ V),
        IsPullback p (yoneda.map q) π (yoneda.map v ≫ x) →
        ∃ (E : BigFppfOver B S hS) (e : E ⟶ W),
          ((BigFppfOver.toScheme B S hS).obj E).size ≤ μ ∧
          ∀ {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u},
            Presheaf.IsSheaf (BigFppfOver.topology B S hS) T →
            ∀ (a b : yoneda.obj W ⟶ T), yoneda.map e ≫ a = yoneda.map e ≫ b →
              pullback.fst (p ≫ π) j ≫ a = pullback.fst (p ≫ π) j ≫ b := by
  have := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS
    (@Surjective.{u} : MorphismProperty Scheme.{u})
  have := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS
    (@Etale.{u} : MorphismProperty Scheme.{u})
  have := BigFppfOver.isStableUnderBaseChange_inverseImage B S hS
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
  obtain ⟨A, c, hcs, hce⟩ := hQ.exists_atlas
  let r : yoneda.obj A ⟶ P := c ≫ pullback.fst π j
  obtain ⟨M, m₁, m₂, hM⟩ := exists_isPullback_yoneda D.algebraicSpace_X x (r ≫ π)
  refine ⟨((BigFppfOver.toScheme B S hS).obj M).size, M.left.2, ?_⟩
  intro V v hv W p q hpb
  obtain ⟨E, f₁, s, hE⟩ := exists_isPullback_yoneda D.algebraicSpace_X (yoneda.map v ≫ x) (r ≫ π)
  -- the object `E` maps to `W`, and is `W ×_P A`
  let e' : yoneda.obj E ⟶ yoneda.obj W := hpb.lift (s ≫ r) f₁ (by
    rw [Category.assoc, ← hE.w])
  have he'p : e' ≫ p = s ≫ r := hpb.lift_fst _ _ _
  have he'q : e' ≫ yoneda.map q = f₁ := hpb.lift_snd _ _ _
  have hEW : IsPullback e' s p r :=
    IsPullback.of_right (by rw [he'q]; exact hE) he'p hpb.flip
  -- the size of `E` is bounded by the size of `M`
  let k : yoneda.obj E ⟶ yoneda.obj M := hM.lift (f₁ ≫ yoneda.map v) s (by
    rw [Category.assoc, hE.w])
  have hkm₁ : k ≫ m₁ = f₁ ≫ yoneda.map v := hM.lift_fst _ _ _
  have hkm₂ : k ≫ m₂ = s := hM.lift_snd _ _ _
  have hk : IsPullback k f₁ m₁ (yoneda.map v) :=
    IsPullback.of_right (by rw [hkm₂]; exact hE.flip) hkm₁ hM.flip
  have hvo := (presheaf_yoneda_map_iff B S hS
    inferInstance v).2 hv
  have hko := (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback hk.flip hvo
  have hko' := prop_preimage_of_presheaf B S hS
    inferInstance k hko
  have : _root_.AlgebraicGeometry.IsOpenImmersion
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage k)) := hko'
  refine ⟨E, yoneda.preimage e',
    Scheme.size_le_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).map (yoneda.preimage k)),
    fun {T} hT a b hab => ?_⟩
  rw [Functor.map_preimage] at hab
  -- the base change of the atlas to `W ×_X J`
  let κ : pullback (p ≫ π) j ⟶ pullback π j :=
    pullback.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _) (by
      rw [Category.assoc, pullback.condition])
  have hbot : IsPullback (pullback.fst (p ≫ π) j) κ p (pullback.fst π j) :=
    IsPullback.of_bot (by rw [pullback.lift_snd]; exact IsPullback.of_hasPullback _ _)
      (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback π j)
  let ε : yoneda.obj E ⟶ pullback (p ≫ π) j :=
    pullback.lift e' (s ≫ c ≫ pullback.snd π j) (by
      rw [← Category.assoc, he'p, Category.assoc, Category.assoc, Category.assoc,
        pullback.condition, Category.assoc])
  have hεκ : ε ≫ κ = s ≫ c := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, he'p]
      rfl
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.assoc]
  have hε : IsPullback ε s κ c :=
    IsPullback.of_right (by rw [pullback.lift_fst]; exact hEW) hεκ hbot
  have hεs := (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback hε.flip hcs
  have hεe := (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback hε.flip hce
  have hK : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback (p ≫ π) j) :=
    Presheaf.isSheaf_pullback _ (p ≫ π) j (isAlgebraicSpace_yoneda B S hS W).isSheaf hJ
      D.algebraicSpace_X.isSheaf
  refine hom_ext_of_etale_atlas B S hS hK hT ε hεs hεe ?_
  rw [← Category.assoc, ← Category.assoc, pullback.lift_fst, hab]

/-! ### The size bound -/

/-- **The size bound for the sheaf of glueing-data morphisms**, granted clause (1) of Stacks
0AF4 over affine bases. Over any morphism `x : h_U ⟶ X` from an object of the site, the affine
objects representing the base changes of `P = homPresheaf D G` to the opens of `U` are of size
at most one cardinal below the cutoff.

Let `W` represent `P ×_X V` for an open `V` of `U`; it is affine. Fix atlases `A_U` of
`P ×_X U ≅ G_U` and `A_Y` of `P ×_X Y ≅ G_Y`. Then `E_• = W ×_P A_• = V ×_X A_•` is an open of
the fixed `U ×_X A_•`. A global section of `W` is a morphism `W ⟶ 𝔸¹_S`; by the faithfulness of
the functor of Stacks 0AF3 it is determined by its restrictions to `W ×_X U` and `W ×_X Y`, and
these by their restrictions along the surjective étale `E_• ⟶ W ×_X •`. So `Γ(W)` injects into
`Γ(E_U) × Γ(E_Y)`, of cardinality at most `2 ^ size (U ×_X A_U) * 2 ^ size (U ×_X A_Y)`. -/
theorem homPresheafSizeBound (hA : AffineBaseEssSurj B S hS)
    (D : FormalGlueingSituation B S hS) (G : glueingData D) (hG : affineLegs D G)
    {U : BigFppfOver B S hS} (x : yoneda.obj U ⟶ D.X) : HomPresheafSizeBound D G x := by
  let π := homPresheafProjection D G
  have hQU : IsAlgebraicSpace B S hS (pullback π D.U.ι) :=
    G.property.2.1.of_iso (@asIso _ _ _ _ (legEvalU D G) (isIso_legEvalU hA D G hG)).symm
  have hQY : IsAlgebraicSpace B S hS (pullback π D.f) :=
    G.property.2.2.of_iso (@asIso _ _ _ _ (legEvalY D G) (isIso_legEvalY hA D G hG)).symm
  obtain ⟨μU, hμU, hlegU⟩ := exists_legBound D π D.U.ι (isOpenSubspace_U D).1.isSheaf hQU x
  obtain ⟨μY, hμY, hlegY⟩ := exists_legBound D π D.f D.algebraicSpace_Y.isSheaf hQY x
  refine ⟨max ℵ₀ (2 ^ μU * 2 ^ μY), max_lt B.aleph0_lt_cutoff
    (mul_lt_of_lt B.aleph0_lt_cutoff.le (B.cutoff_isStrongPrelimit hμU)
      (B.cutoff_isStrongPrelimit hμY)), ?_⟩
  intro V v hv hVaff W p q hpb
  obtain ⟨EU, eU, hEU, hextU⟩ := hlegU V v hv W p q hpb
  obtain ⟨EY, eY, hEY, hextY⟩ := hlegY V v hv W p q hpb
  -- `W` is affine
  obtain ⟨W', p', q', hpb'⟩ := isAffineHom_homPresheafProjection hA D G hG ⟨V, hVaff⟩
    (yoneda.map v ≫ x)
  let eW : W ≅ (BigAffineFppf.inclusion B S hS).obj W' :=
    Yoneda.fullyFaithful.preimageIso (hpb.isoIsPullback _ _ hpb')
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((BigAffineFppf.inclusion B S hS).obj W')) :=
    W'.property
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W) :=
    .of_isIso ((BigFppfOver.toScheme B S hS).map eW.hom)
  rw [Scheme.size_of_isAffine]
  refine max_le_max le_rfl ?_
  -- global sections of `W` inject into those of `E_U` and `E_Y`
  have hinj : Function.Injective (fun g : W ⟶ affineLineSite B S hS => (eU ≫ g, eY ≫ g)) := by
    intro g g' h
    simp only [Prod.mk.injEq] at h
    have hT := (isAlgebraicSpace_yoneda B S hS (affineLineSite B S hS)).isSheaf
    refine Yoneda.fullyFaithful.map_injective (hom_ext_of_restrictions D
      (isAlgebraicSpace_yoneda B S hS W) (isAlgebraicSpace_yoneda B S hS _) (p ≫ π)
      (hextU hT _ _ ?_) (hextY hT _ _ ?_))
    · rw [← Functor.map_comp, ← Functor.map_comp, h.1]
    · rw [← Functor.map_comp, ← Functor.map_comp, h.2]
  calc #Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)
      ≤ #(W ⟶ affineLineSite B S hS) := mk_sections_le_mk_hom_affineLineSite B S hS W
    _ ≤ #((EU ⟶ affineLineSite B S hS) × (EY ⟶ affineLineSite B S hS)) :=
        Cardinal.mk_le_of_injective hinj
    _ = #(EU ⟶ affineLineSite B S hS) * #(EY ⟶ affineLineSite B S hS) := by
        rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    _ ≤ #Γ((BigFppfOver.toScheme B S hS).obj EU, ⊤) *
          #Γ((BigFppfOver.toScheme B S hS).obj EY, ⊤) :=
        mul_le_mul' (mk_hom_affineLineSite_le_mk_sections B S hS EU)
          (mk_hom_affineLineSite_le_mk_sections B S hS EY)
    _ ≤ 2 ^ μU * 2 ^ μY :=
        mul_le_mul' ((Scheme.mk_sections_le_two_pow_size _ ⊤).trans
            (power_le_power_left two_ne_zero hEU))
          ((Scheme.mk_sections_le_two_pow_size _ ⊤).trans (power_le_power_left two_ne_zero hEY))

/-! ### Algebraicity and the three equivalences, from the affine case -/

/-- **The sheaf of glueing-data morphisms into a triple with affine legs is an algebraic
space**, granted clause (1) of Stacks 0AF4 over affine bases. -/
theorem isAlgebraicSpace_homPresheaf (hA : AffineBaseEssSurj B S hS)
    (D : FormalGlueingSituation B S hS) (G : glueingData D) (hG : affineLegs D G) :
    IsAlgebraicSpace B S hS (homPresheaf D G) := by
  obtain ⟨U, x, hxs, hxe⟩ := D.algebraicSpace_X.exists_atlas
  exact isAlgebraicSpace_homPresheaf_of_size_le hA D G hG x hxs hxe
    (homPresheafSizeBound hA D G hG x)

/-- **Clause (1) of Stacks 0AF4, from the affine case**: the restriction functor is an
equivalence from algebraic spaces affine over `X` onto triples with affine legs. -/
theorem isEquivalence_affineGlueingFunctor_of_affineBaseEssSurj (hA : AffineBaseEssSurj B S hS)
    (D : FormalGlueingSituation B S hS) : (affineGlueingFunctor D).IsEquivalence :=
  isEquivalence_affineGlueingFunctor_of_isAlgebraicSpace hA
    (fun D G hG => isAlgebraicSpace_homPresheaf hA D G hG) D

/-- **Clause (2) of Stacks 0AF4, from the affine case**: the restriction functor is an
equivalence from closed immersions into `X` onto triples whose legs are closed immersions. -/
theorem isEquivalence_closedGlueingFunctor_of_affineBaseEssSurj (hA : AffineBaseEssSurj B S hS)
    (D : FormalGlueingSituation B S hS) : (closedGlueingFunctor D).IsEquivalence :=
  isEquivalence_closedGlueingFunctor_of_isAlgebraicSpace hA
    (fun D G hG => isAlgebraicSpace_homPresheaf hA D G hG) D

/-- **Clause (3) of Stacks 0AF4, from the affine case**: the restriction functor is an
equivalence from finite morphisms to `X` onto triples whose legs are finite. -/
theorem isEquivalence_finiteGlueingFunctor_of_affineBaseEssSurj (hA : AffineBaseEssSurj B S hS)
    (D : FormalGlueingSituation B S hS) : (finiteGlueingFunctor D).IsEquivalence :=
  isEquivalence_finiteGlueingFunctor_of_isAlgebraicSpace hA
    (fun D G hG => isAlgebraicSpace_homPresheaf hA D G hG) D

end AlgebraicGeometry.Space.FormalGlueingSituation

end
