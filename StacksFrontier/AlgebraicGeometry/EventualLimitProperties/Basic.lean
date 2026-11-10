module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksCore.Tactic.StacksAttribute

/-!
# Cofiltered limits of schemes: the affine-local toolkit

Mathlib's `Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean` develops inverse limits of
schemes with affine transition morphisms, but it does so for a diagram `D : I ⥤ Scheme.{u}`
whose index category `I` lives in the *same* universe `u` as the schemes.  The statements about
eventual properties in such a limit are naturally universe polymorphic in the index, so this
file redevelops the part of that toolkit which is needed for them with an index category in an
arbitrary universe.

The key point is that no large colimit of rings has to exist for this: as soon as every stage of
the diagram is *affine*, the fact that `Scheme.Spec` is a reflective right adjoint makes
`Scheme.Γ` preserve the colimit of the diagram (`AlgebraicGeometry.preservesColimit_Γ`), and that
instance is already universe polymorphic.  So the affine-local statements transfer verbatim,
and affineness of the relevant stages is arranged by restricting the diagram to the preimages of
one affine open of one stage.

## Main definitions

* `AlgebraicGeometry.EventualLimit.preimageDiagram`: for an open `U` of `D i`, the diagram
  `j ↦ D_{ji}⁻¹ U` indexed by `Over i`.
* `AlgebraicGeometry.EventualLimit.preimageCone`: the cone on it with vertex the preimage of `U`
  in the limit.
* `AlgebraicGeometry.EventualLimit.vanishingIdeal`: for a diagram of rings with a distinguished
  object `j₀`, the ideal of elements of the ring at `j₀` which die at some stage.

## Main results

* `AlgebraicGeometry.EventualLimit.isAffine_of_isLimit`: a limit of affine schemes is affine.
* `AlgebraicGeometry.EventualLimit.isLimitPreimageCone`: `preimageCone` is a limit cone.
* `AlgebraicGeometry.EventualLimit.preimageDiagram_isAffineHom`: a diagram with affine transition
  morphisms has a diagram of preimages with affine transition morphisms.
* `AlgebraicGeometry.EventualLimit.isAffineOpen_preimage_π_app`: the preimage of an affine open
  of a stage under a limit projection is affine.
* `AlgebraicGeometry.EventualLimit.surjective_ι`, `.exists_map_eq_zero`,
  `.ker_ι_eq_vanishingIdeal` and `.exists_isIso_ι`: the behaviour of a filtered colimit of rings
  whose structure maps out of a distinguished object are surjective.  The last of these says
  that if moreover the kernel at the distinguished object is finitely generated then the colimit
  maps are isomorphisms at all sufficiently late stages.

## References

* [The Stacks Project, Tag 01YT](https://stacks.math.columbia.edu/tag/01YT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

namespace EventualLimit

/-! ### Affineness of limits of affine schemes -/

/-- Two morphisms into an open subscheme agree as soon as their composites with the inclusion
of that open subscheme agree. -/
lemma hom_ext_opens {X Y : Scheme.{u}} {V : Y.Opens} {a b : X ⟶ V.toScheme}
    (h : a ≫ V.ι = b ≫ V.ι) : a = b :=
  (cancel_mono V.ι).mp h

/-- A limit of a diagram of affine schemes is affine.  Unlike the corresponding statement in
Mathlib there is no restriction on the universe of the index category: the limit cone is given,
so no large colimit of rings needs to exist. -/
lemma isAffine_of_isLimit {J : Type w} [Category.{v} J]
    (F : J ⥤ Scheme.{u}) (c : Cone F) (hc : IsLimit c)
    [∀ j, IsAffine (F.obj j)] : IsAffine c.pt := by
  let α : F ⟶ (F ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec :=
    Functor.whiskerLeft F ΓSpec.adjunction.unit
  have hα (j : J) : IsIso (α.app j) := IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  have hc' : IsLimit ((Cone.postcompose (asIso α).hom).obj c) :=
    (IsLimit.postcomposeHomEquiv (asIso α) c).symm hc
  have hcSpec : IsLimit (Scheme.Spec.mapCone (Scheme.Γ.rightOp.mapCone c)) :=
    isLimitOfPreserves Scheme.Spec (isLimitOfPreserves Scheme.Γ.rightOp hc)
  have : IsAffine (Scheme.Spec.mapCone (Scheme.Γ.rightOp.mapCone c)).pt := by
    dsimp
    infer_instance
  exact .of_isIso (hc'.conePointUniqueUpToIso hcSpec).hom

/-! ### The diagram of preimages of an open of a stage -/

attribute [local simp] Scheme.Hom.resLE_comp_resLE

variable {I : Type w} [Category.{v} I] (D : I ⥤ Scheme.{u})

/-- Given a diagram `{ Dᵢ }` of schemes and an open `U ⊆ Dᵢ`, this is the diagram of the
preimages `{ Dⱼᵢ⁻¹ U }` indexed by the objects over `i`.  This is the universe polymorphic
version of `AlgebraicGeometry.opensDiagram`. -/
@[simps]
noncomputable def preimageDiagram (i : I) (U : (D.obj i).Opens) : Over i ⥤ Scheme.{u} where
  obj j := D.map j.hom ⁻¹ᵁ U
  map {j k} g := (D.map g.left).resLE _ _
    (by rw [← Scheme.Hom.comp_preimage, ← D.map_comp, Over.w g])
  map_id _ := hom_ext_opens (by simp [Scheme.Hom.resLE_comp_ι])
  map_comp _ _ := hom_ext_opens (by simp [Scheme.Hom.resLE_comp_ι])

/-- The inclusion of `preimageDiagram` into the original diagram. -/
noncomputable def preimageDiagramι (i : I) (U : (D.obj i).Opens) :
    preimageDiagram D i U ⟶ Over.forget i ⋙ D where
  app _ := Scheme.Opens.ι _
  naturality _ _ _ := Scheme.Hom.resLE_comp_ι _ _

/-- Each component of `preimageDiagramι` is an open immersion. -/
instance (i : I) (U : (D.obj i).Opens) (j : Over i) :
    IsOpenImmersion ((preimageDiagramι D i U).app j) :=
  inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _))

/-- Given a cone `c` on `D` and an open `U ⊆ Dᵢ`, this is the cone on `preimageDiagram D i U`
with vertex the preimage of `U` in `c.pt`. -/
@[simps]
noncomputable def preimageCone (c : Cone D) (i : I) (U : (D.obj i).Opens) :
    Cone (preimageDiagram D i U) where
  pt := c.π.app i ⁻¹ᵁ U
  π :=
  { app j := (c.π.app j.left).resLE _ _ (by rw [← Scheme.Hom.comp_preimage, c.w])
    naturality _ _ _ :=
      hom_ext_opens (by simp [preimageDiagram, Scheme.Hom.resLE_comp_ι, c.w]) }

attribute [local instance] CategoryTheory.isConnected_of_hasTerminal

/-- The comparison morphism from `preimageCone`, pushed into the ambient diagram, to the
restriction of the ambient cone. -/
@[simps]
noncomputable def preimageConeι (c : Cone D) (i : I) (U : (D.obj i).Opens) :
    (Cone.postcompose (preimageDiagramι D i U)).obj (preimageCone D c i U) ⟶
      Cone.whisker (Over.forget i) c where
  hom := (c.π.app i ⁻¹ᵁ U).ι
  w j := (Scheme.Hom.resLE_comp_ι (c.π.app j.left) _).symm

/-- The morphism of cone points underlying `preimageConeι` is an open immersion. -/
instance (c : Cone D) (i : I) (U : (D.obj i).Opens) :
    IsOpenImmersion (preimageConeι D c i U).hom :=
  inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι _))

/-- The preimage of `U ⊆ Dᵢ` in the limit is the limit of the preimages of `U` in the stages
over `i`.  This is the universe polymorphic version of
`AlgebraicGeometry.isLimitOpensCone`. -/
noncomputable def isLimitPreimageCone (c : Cone D) (hc : IsLimit c) [IsCofiltered I]
    (i : I) (U : (D.obj i).Opens) : IsLimit (preimageCone D c i U) :=
  isLimitOfIsPullbackOfIsConnected (preimageDiagramι D i U) (preimageCone D c i U)
    (Cone.whisker (Over.forget i) c) (preimageConeι D c i U)
    (fun j => IsOpenImmersion.isPullback _ _ _ _
      ((Scheme.Hom.resLE_comp_ι (c.π.app j.left) _).symm)
      (by
        change c.π.app j.left ⁻¹ᵁ Scheme.Hom.opensRange (Scheme.Opens.ι (D.map j.hom ⁻¹ᵁ U)) =
          Scheme.Hom.opensRange (Scheme.Opens.ι (c.π.app i ⁻¹ᵁ U))
        rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι,
          ← Scheme.Hom.comp_preimage, c.w]))
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc)

/-- If `U` is an affine open of the stage `Dᵢ` and the transition morphisms are affine, then
every stage of `preimageDiagram D i U` is affine. -/
lemma isAffine_preimageDiagram_obj [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (i : I) {U : (D.obj i).Opens} (hU : IsAffineOpen U) (j : Over i) :
    IsAffine ((preimageDiagram D i U).obj j) :=
  hU.preimage (D.map j.hom)

/-- If the transition morphisms of `D` are closed immersions, then so are the transition
morphisms of the diagram of preimages of an open of a stage. -/
instance preimageDiagram_isClosedImmersion
    [∀ {i j : I} (g : i ⟶ j), IsClosedImmersion (D.map g)]
    (i : I) (U : (D.obj i).Opens) {j k : Over i} (g : j ⟶ k) :
    IsClosedImmersion ((preimageDiagram D i U).map g) := by
  have h : D.map j.hom ⁻¹ᵁ U = D.map g.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← D.map_comp, Over.w g]
  change IsClosedImmersion ((D.map g.left).resLE (D.map k.hom ⁻¹ᵁ U) (D.map j.hom ⁻¹ᵁ U) _)
  rw [Scheme.Hom.resLE_congr (D.map g.left) _ rfl h (@IsClosedImmersion),
    Scheme.Hom.resLE_eq_morphismRestrict]
  exact IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) inferInstance _

/-- If the transition morphisms of `D` are affine, then so are the transition morphisms of the
diagram of preimages of an open of a stage.  This is the proof of
`preimageDiagram_isClosedImmersion` verbatim, with the one difference that
`IsZariskiLocalAtTarget @IsAffineHom` is not an instance and has to be produced from
`AlgebraicGeometry.HasAffineProperty`. -/
instance preimageDiagram_isAffineHom
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (i : I) (U : (D.obj i).Opens) {j k : Over i} (g : j ⟶ k) :
    IsAffineHom ((preimageDiagram D i U).map g) := by
  have : IsZariskiLocalAtTarget (@IsAffineHom : MorphismProperty Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine
  have h : D.map j.hom ⁻¹ᵁ U = D.map g.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← D.map_comp, Over.w g]
  change IsAffineHom ((D.map g.left).resLE (D.map k.hom ⁻¹ᵁ U) (D.map j.hom ⁻¹ᵁ U) _)
  rw [Scheme.Hom.resLE_congr (D.map g.left) _ rfl h (@IsAffineHom),
    Scheme.Hom.resLE_eq_morphismRestrict]
  exact IsZariskiLocalAtTarget.restrict (P := @IsAffineHom) inferInstance _

/-- The preimage of an affine open of a stage under a limit projection is affine. -/
lemma isAffineOpen_preimage_π_app [IsCofiltered I]
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i : I) {U : (D.obj i).Opens} (hU : IsAffineOpen U) :
    IsAffineOpen (c.π.app i ⁻¹ᵁ U) := by
  have := isAffine_preimageDiagram_obj D i hU
  exact isAffine_of_isLimit _ _ (isLimitPreimageCone D c hc i U)

/-- The projections from a cofiltered limit of schemes with affine transition morphisms are
affine.  This is the universe polymorphic version of `AlgebraicGeometry.isAffineHom_π_app`. -/
lemma isAffineHom_π_app [IsCofiltered I]
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) (i : I) : IsAffineHom (c.π.app i) := by
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun x => ?_
  obtain ⟨a, ha⟩ := (D.obj i).affineCover.isOpenCover_opensRange.exists_mem x
  refine ⟨_, ha, isAffineOpen_opensRange ((D.obj i).affineCover.f a), ?_⟩
  exact isAffineOpen_preimage_π_app D c hc i (isAffineOpen_opensRange _)

/-! ### Filtered colimits of rings with surjective structure maps -/

variable {J : Type w} [Category.{v} J] {F : J ⥤ CommRingCat.{u}} {d : Cocone F}
  (hd : IsColimit d) (j₀ : J) (arr : ∀ j, j₀ ⟶ j)

/-- The cocone map at `j₀` factors through the structure map `arr j`. -/
private theorem ι_app_arr_apply (j : J) (x : F.obj j₀) :
    (d.ι.app j).hom ((F.map (arr j)).hom x) = (d.ι.app j₀).hom x := by
  rw [← ConcreteCategory.comp_apply, d.w (arr j)]

/-- An element killed by `arr j` is killed by `arr k` whenever there is a map `j ⟶ k`. -/
private theorem map_arr_eq_zero
    (harr : ∀ {j k : J} (g : j ⟶ k), arr j ≫ g = arr k) {j k : J} (g : j ⟶ k) {x : F.obj j₀}
    (h : (F.map (arr j)).hom x = 0) : (F.map (arr k)).hom x = 0 := by
  rw [← harr g, F.map_comp, ConcreteCategory.comp_apply, h, map_zero]

section Surjective

include hd

/-- If a cocone on a diagram of rings is a colimit and the structure maps out of a fixed object
`j₀` are surjective, then the cocone map at `j₀` is surjective. -/
lemma surjective_ι (hsurj : ∀ j, Function.Surjective (F.map (arr j)).hom) :
    Function.Surjective (d.ι.app j₀).hom := by
  set C : Subring d.pt := (d.ι.app j₀).hom.range
  have hmem (j : J) (y : F.obj j) : (d.ι.app j).hom y ∈ C := by
    obtain ⟨x, rfl⟩ := hsurj j y
    exact ⟨x, (ι_app_arr_apply (d := d) j₀ arr j x).symm⟩
  let e : Cocone F :=
    { pt := CommRingCat.of C
      ι :=
      { app j := CommRingCat.ofHom ((d.ι.app j).hom.codRestrict C (hmem j))
        naturality := fun j k g => by
          ext y
          refine Subtype.ext ?_
          change (d.ι.app k).hom ((F.map g).hom y) = (d.ι.app j).hom y
          rw [← ConcreteCategory.comp_apply, d.w g] } }
  have hcomp : hd.desc e ≫ CommRingCat.ofHom C.subtype = 𝟙 d.pt := by
    refine hd.hom_ext fun j => ?_
    rw [← Category.assoc, hd.fac e j, Category.comp_id]
    ext y
    rfl
  intro z
  obtain ⟨x, hx⟩ := ((hd.desc e).hom z).2
  refine ⟨x, hx.trans ?_⟩
  have h2 := congrArg (fun q : d.pt ⟶ d.pt => q.hom z) hcomp
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id,
    RingHom.id_apply, CommRingCat.hom_ofHom] at h2
  exact h2

end Surjective

section Kernel

variable [IsFiltered J] (harr : ∀ {j k : J} (g : j ⟶ k), arr j ≫ g = arr k)

/-- The elements of the ring at `j₀` which are killed by some structure map of the diagram.
Filteredness of the index category makes this an ideal. -/
def vanishingIdeal : Ideal (F.obj j₀) where
  carrier := {x | ∃ j, (F.map (arr j)).hom x = 0}
  zero_mem' := ⟨j₀, by simp⟩
  add_mem' := by
    rintro x y ⟨j, hj⟩ ⟨k, hk⟩
    obtain ⟨l, g, h, -⟩ := IsFilteredOrEmpty.cocone_objs j k
    refine ⟨l, ?_⟩
    have hx : (F.map (arr l)).hom x = 0 := by
      rw [← harr g, F.map_comp, ConcreteCategory.comp_apply, hj, map_zero]
    have hy : (F.map (arr l)).hom y = 0 := by
      rw [← harr h, F.map_comp, ConcreteCategory.comp_apply, hk, map_zero]
    rw [map_add, hx, hy, add_zero]
  smul_mem' := by
    rintro a x ⟨j, hj⟩
    exact ⟨j, by rw [smul_eq_mul, map_mul, hj, mul_zero]⟩

include hd harr

/-- If a cocone on a filtered diagram of rings whose structure maps out of `j₀` are surjective
is a colimit, then an element of the ring at `j₀` killed by the cocone map already dies at some
stage of the diagram. -/
lemma exists_map_eq_zero (harr_id : arr j₀ = 𝟙 j₀)
    (hsurj : ∀ j, Function.Surjective (F.map (arr j)).hom)
    (x : F.obj j₀) (hx : (d.ι.app j₀).hom x = 0) :
    ∃ j, (F.map (arr j)).hom x = 0 := by
  set K : Ideal (F.obj j₀) := vanishingIdeal j₀ arr harr
  have hker (j : J) : RingHom.ker (F.map (arr j)).hom ≤ K := fun y hy => ⟨j, hy⟩
  let ψ (j : J) : F.obj j →+* (F.obj j₀ ⧸ K) :=
    (Ideal.Quotient.lift (RingHom.ker (F.map (arr j)).hom) (Ideal.Quotient.mk K)
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hker j ha))).comp
      (RingHom.quotientKerEquivOfSurjective (hsurj j)).symm.toRingHom
  have hψ (j : J) (y : F.obj j₀) :
      ψ j ((F.map (arr j)).hom y) = Ideal.Quotient.mk K y := by
    have h1 : (RingHom.quotientKerEquivOfSurjective (hsurj j)).symm
        ((F.map (arr j)).hom y) = Ideal.Quotient.mk _ y := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    simp only [ψ, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, h1]
    rfl
  let e : Cocone F :=
    { pt := CommRingCat.of (F.obj j₀ ⧸ K)
      ι :=
      { app j := CommRingCat.ofHom (ψ j)
        naturality := fun j k g => by
          ext y
          obtain ⟨z, rfl⟩ := hsurj j y
          change ψ k ((F.map g).hom ((F.map (arr j)).hom z)) = ψ j ((F.map (arr j)).hom z)
          rw [← ConcreteCategory.comp_apply, ← F.map_comp, harr g, hψ, hψ] } }
  have h1 : ψ j₀ x = 0 := by
    have h := congrArg (fun q : F.obj j₀ ⟶ e.pt => q.hom x) (hd.fac e j₀)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h
    rw [hx, map_zero] at h
    exact h.symm
  have h2 := hψ j₀ x
  rw [harr_id, F.map_id] at h2
  simp only [CommRingCat.hom_id, RingHom.id_apply] at h2
  exact Ideal.Quotient.eq_zero_iff_mem.mp (h2 ▸ h1)

/-- The kernel of the colimit map at `j₀` is exactly the ideal of elements dying at some
stage. -/
lemma ker_ι_eq_vanishingIdeal (harr_id : arr j₀ = 𝟙 j₀)
    (hsurj : ∀ j, Function.Surjective (F.map (arr j)).hom) :
    RingHom.ker (d.ι.app j₀).hom = vanishingIdeal j₀ arr harr := by
  refine le_antisymm (fun x hx => exists_map_eq_zero hd j₀ arr harr harr_id hsurj x hx) ?_
  rintro x ⟨j, hj⟩
  simp only [RingHom.mem_ker, ← ι_app_arr_apply (d := d) j₀ arr j, hj, map_zero]

/-- Let a cocone on a filtered diagram of rings whose structure maps out of `j₀` are surjective
be a colimit, and assume that the kernel of the colimit map at `j₀` is finitely generated.  Then
the colimit map is an isomorphism at all sufficiently late stages. -/
lemma exists_isIso_ι (harr_id : arr j₀ = 𝟙 j₀)
    (hsurj : ∀ j, Function.Surjective (F.map (arr j)).hom)
    (hfg : (RingHom.ker (d.ι.app j₀).hom).FG) :
    ∃ j₁ : J, ∀ (j : J) (_ : j₁ ⟶ j), IsIso (d.ι.app j) := by
  classical
  have hK := ker_ι_eq_vanishingIdeal hd j₀ arr harr harr_id hsurj
  obtain ⟨σ, hσ⟩ := hfg
  have hmem (y : {y // y ∈ σ}) : ∃ j, (F.map (arr j)).hom y.1 = 0 := by
    have h : y.1 ∈ RingHom.ker (d.ι.app j₀).hom := by
      rw [← hσ]
      exact Ideal.subset_span y.2
    rwa [hK] at h
  choose jy hjy using hmem
  obtain ⟨j₁, hj₁⟩ := IsFiltered.sup_objs_exists (σ.attach.image jy)
  have hzero (y : {y // y ∈ σ}) : (F.map (arr j₁)).hom y.1 = 0 := by
    obtain ⟨g⟩ := hj₁ (Finset.mem_image_of_mem jy (Finset.mem_attach _ y))
    exact map_arr_eq_zero j₀ arr harr g (hjy y)
  have hle : RingHom.ker (d.ι.app j₀).hom ≤ RingHom.ker (F.map (arr j₁)).hom := by
    rw [← hσ, Ideal.span_le]
    exact fun y hy => hzero ⟨y, hy⟩
  refine ⟨j₁, fun j g => ?_⟩
  have hlej : RingHom.ker (d.ι.app j₀).hom ≤ RingHom.ker (F.map (arr j)).hom := by
    intro y hy
    have h1 := hle hy
    exact map_arr_eq_zero j₀ arr harr g h1
  refine (ConcreteCategory.isIso_iff_bijective (d.ι.app j)).mpr ⟨?_, ?_⟩
  · intro y z hyz
    rw [← sub_eq_zero] at hyz ⊢
    rw [← map_sub] at hyz
    obtain ⟨w, hw⟩ := hsurj j (y - z)
    rw [← hw] at hyz ⊢
    exact hlej (by rwa [RingHom.mem_ker, ← ι_app_arr_apply (d := d) j₀ arr j])
  · intro z
    obtain ⟨x, hx⟩ := surjective_ι hd j₀ arr hsurj z
    exact ⟨(F.map (arr j)).hom x, by rwa [ι_app_arr_apply (d := d) j₀ arr j]⟩

end Kernel

end EventualLimit

end AlgebraicGeometry
