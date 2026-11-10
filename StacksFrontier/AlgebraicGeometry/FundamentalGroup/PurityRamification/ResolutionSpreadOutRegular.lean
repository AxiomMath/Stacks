module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionSpreadOutIso
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibreStalk
public import StacksFrontier.AlgebraicGeometry.LocalSchemesFpqcCover.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.JTwo

/-!
# Spreading out a scheme over the local ring at a point: regularity

Continuing `PurityRamification/ResolutionSpreadOutIso.lean`. In the proof of [Stacks, Tag 0EA3]
the resolution `W ⟶ Spec(𝒪_{X, x})` is spread out to a proper `b : X' ⟶ U` over an affine open
neighbourhood `U` of `x`, and "after shrinking `X` further, we may assume `X'` is regular. Namely,
we know `W` is regular and `X'` is excellent and the regular locus of the spectrum of an excellent
ring is open." This file proves that step for a J-2 base: the regular locus of `X'` is open, its
complement has closed image under the proper `b`, and that image misses `x` because the local
rings of `X'` at the points over `x` are local rings of `W` (the projection
`W = X' ×_U Spec(𝒪_{X, x}) ⟶ X'` is a flat preimmersion). It also records that the other
properties of the model are kept when the neighbourhood is shrunk.

## Main results

* `AlgebraicGeometry.flat_fromSpecStalkOfMem`: the map `Spec(𝒪_{X, x}) ⟶ U` is flat.
* `AlgebraicGeometry.isPreimmersion_fromSpecStalkOfMem`: the map `Spec(𝒪_{X, x}) ⟶ U` is a
  preimmersion.
* `AlgebraicGeometry.isIso_pullback_snd_model_shrink`: being an isomorphism over `U ∩ V` survives
  shrinking `U`.
* `AlgebraicGeometry.exists_hom_isRegular_model`: the model is regular over a smaller affine open
  neighbourhood.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- If the base change of `b : Z ⟶ U` to `U ∩ V` is an isomorphism, so is the base change of
`Z ×_U U'` to `U' ∩ V` for a smaller affine open neighbourhood `U'`. -/
theorem isIso_pullback_snd_model_shrink (X : Scheme.{u}) (x : X) (V : X.Opens)
    {j k : AffineOpenNhds X x} (h : k ⟶ j) {Z : Scheme.{u}}
    (b : Z ⟶ (affineOpenNhdsDiagram X x).obj j)
    (hb : IsIso (pullback.snd b (Scheme.Opens.ι (X := X) j.obj.1 ⁻¹ᵁ V).ι)) :
    IsIso (pullback.snd (pullback.snd b ((affineOpenNhdsDiagram X x).map h))
      (Scheme.Opens.ι (X := X) k.obj.1 ⁻¹ᵁ V).ι) := by
  let D := affineOpenNhdsDiagram X x
  let Oj : (D.obj j).Opens := Scheme.Opens.ι (X := X) j.obj.1 ⁻¹ᵁ V
  let Ok : (D.obj k).Opens := Scheme.Opens.ι (X := X) k.obj.1 ⁻¹ᵁ V
  have e' : (k.obj.1 : X.Opens) ≤ j.obj.1 := leOfHom ((affineOpenNhds X x).ι.map h)
  have hQ : D.map h ⁻¹ᵁ Oj = Ok := by
    have h1 := Scheme.Hom.comp_preimage (X.homOfLE e') (Scheme.Opens.ι (X := X) j.obj.1) V
    rw [Scheme.homOfLE_ι] at h1
    exact h1.symm
  let σ : Ok.toScheme ⟶ Oj.toScheme := (D.map h).resLE Oj Ok hQ.ge
  have hσ : σ ≫ Oj.ι = Ok.ι ≫ D.map h := Scheme.Hom.resLE_comp_ι _ _
  refine (isIso_pullback_snd_snd_iff b (D.map h) Ok.ι).mpr ?_
  refine (isIso_pullback_snd_congr b hσ).mp ?_
  refine (isIso_pullback_snd_snd_iff b Oj.ι σ).mp ?_
  have : IsIso (pullback.snd b Oj.ι) := hb
  infer_instance

/-- The canonical map `Spec(𝒪_{X, x}) ⟶ U` to an open neighbourhood of `x` is flat. -/
theorem flat_fromSpecStalkOfMem {X : Scheme.{u}} (U : X.Opens) (x : X) (hx : x ∈ U) :
    Flat (U.fromSpecStalkOfMem x hx) := by
  have hsq : IsPullback (𝟙 _) (U.fromSpecStalkOfMem x hx) (U.fromSpecStalkOfMem x hx ≫ U.ι) U.ι :=
    IsPullback.of_isLimit' ⟨by rw [Category.id_comp]⟩
      (PullbackCone.IsLimit.mk _ (fun s => s.fst) (fun s => Category.comp_id _)
        (fun s => by rw [← cancel_mono U.ι, Category.assoc]; exact s.condition)
        (fun s m h₁ _ => by rw [← h₁, Category.comp_id]))
  have h : Flat (U.fromSpecStalkOfMem x hx ≫ U.ι) := by
    rw [Scheme.Opens.fromSpecStalkOfMem_ι]
    infer_instance
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat) hsq h

/-- The canonical map `Spec(𝒪_{X, x}) ⟶ U` to an open neighbourhood of `x` is a preimmersion. -/
theorem isPreimmersion_fromSpecStalkOfMem {X : Scheme.{u}} (U : X.Opens) (x : X) (hx : x ∈ U) :
    IsPreimmersion (U.fromSpecStalkOfMem x hx) := by
  have : IsPreimmersion (U.fromSpecStalkOfMem x hx ≫ U.ι) := by
    rw [Scheme.Opens.fromSpecStalkOfMem_ι]
    infer_instance
  exact IsPreimmersion.of_comp _ U.ι

/-- The leg `Spec(𝒪_{X, x}) ⟶ U` of the cone `specStalkCone X x` at an affine open neighbourhood
`U` of `x` is flat. -/
instance flat_specStalkCone_π_app (X : Scheme.{u}) (x : X) (j : AffineOpenNhds X x) :
    Flat ((specStalkCone X x).π.app j) :=
  flat_fromSpecStalkOfMem _ _ _

/-- The leg `Spec(𝒪_{X, x}) ⟶ U` of the cone `specStalkCone X x` at an affine open neighbourhood
`U` of `x` is a preimmersion. -/
instance isPreimmersion_specStalkCone_π_app (X : Scheme.{u}) (x : X) (j : AffineOpenNhds X x) :
    IsPreimmersion ((specStalkCone X x).π.app j) :=
  isPreimmersion_fromSpecStalkOfMem _ _ _

/-- A point of the model `Z` over the closed point of `Spec(𝒪_{X, x})` lies in the regular locus
of `Z`, when the base change `W` of `Z` to `Spec(𝒪_{X, x})` is regular. -/
private theorem mem_regularLocus_of_map_eq_closedPoint (X : Scheme.{u}) (x : X) {W : Scheme.{u}}
    (g : W ⟶ Spec (X.presheaf.stalk x)) (hW : IsRegular W) {j : AffineOpenNhds X x}
    (Z : Over ((affineOpenNhdsDiagram X x).obj j))
    (e : Over.mk g ≅ (Over.pullback ((specStalkCone X x).π.app j)).obj Z) {y : Z.left}
    (hy : Z.hom y = (specStalkCone X x).π.app j (IsLocalRing.closedPoint _)) :
    y ∈ regularLocus Z.left := by
  let c := specStalkCone X x
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback y _ hy
  have : IsIso ((pullback.fst Z.hom (c.π.app j)).stalkMap z) :=
    isIso_stalkMap_of_flat_of_isPreimmersion _ z
  have hP : IsRegularLocalRing ((pullback Z.hom (c.π.app j)).presheaf.stalk z) := by
    have : IsIso (e.inv.left.stalkMap z) :=
      inferInstanceAs (IsIso (((Over.forget _).mapIso e).inv.stalkMap z))
    have : IsRegularLocalRing ((Over.mk g).left.presheaf.stalk (e.inv.left z)) :=
      ((isRegular_iff_regular_stalks W).mp hW).2 (e.inv.left z)
    exact IsRegularLocalRing.of_ringEquiv
      (asIso (e.inv.left.stalkMap z)).commRingCatIsoToRingEquiv
  change IsRegularLocalRing (Z.left.presheaf.stalk y)
  rw [← hz]
  exact IsRegularLocalRing.of_ringEquiv
    (asIso ((pullback.fst Z.hom (c.π.app j)).stalkMap z)).commRingCatIsoToRingEquiv.symm

/-- **The model is regular over a smaller neighbourhood (the regularity step of the proof of
[Stacks, Tag 0EA3]).** Let `X` be a locally Noetherian J-2 scheme, `x ∈ X`, and let
`g : W ⟶ Spec(𝒪_{X, x})` with `W` regular be the base change of a proper morphism `Z ⟶ U`
locally of finite type over an affine open neighbourhood `U` of `x`. Then `Z ×_U U'` is regular
for some smaller affine open neighbourhood `U'` of `x`. -/
theorem exists_hom_isRegular_model (X : Scheme.{u}) [IsLocallyNoetherian X] (hJ : X.IsJ2)
    (x : X) {W : Scheme.{u}} (g : W ⟶ Spec (X.presheaf.stalk x)) (hW : IsRegular W)
    {j : AffineOpenNhds X x} (Z : Over ((affineOpenNhdsDiagram X x).obj j)) [IsProper Z.hom]
    [LocallyOfFiniteType Z.hom]
    (e : Over.mk g ≅ (Over.pullback ((specStalkCone X x).π.app j)).obj Z) :
    ∃ (k : AffineOpenNhds X x) (h : k ⟶ j),
      IsRegular (pullback Z.hom ((affineOpenNhdsDiagram X x).map h)) := by
  let D := affineOpenNhdsDiagram X x
  let c := specStalkCone X x
  let ιj : (affineOpenNhdsDiagram X x).obj j ⟶ X := Scheme.Opens.ι (X := X) j.obj.1
  have : IsOpenImmersion ιj := inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι (X := X) j.obj.1))
  have : LocallyOfFiniteType (Z.hom ≫ ιj) := inferInstance
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian (Z.hom ≫ ιj)
  have hopen : IsOpen (regularLocus Z.left) := hJ.isOpen_regularLocus (Z.hom ≫ ιj)
  let O : (D.obj j).Opens :=
    ⟨(Z.hom '' (regularLocus Z.left)ᶜ)ᶜ, (Z.hom.isClosedMap _ hopen.isClosed_compl).isOpen_compl⟩
  have hxO : c.π.app j (IsLocalRing.closedPoint _) ∈ O := by
    rintro ⟨y, hy, hyx⟩
    exact hy (mem_regularLocus_of_map_eq_closedPoint X x g hW Z e hyx)
  have hxU : x ∈ ιj ''ᵁ O := by
    refine ⟨_, hxO, ?_⟩
    change (c.π.app j ≫ ιj) _ = x
    rw [show c.π.app j ≫ ιj = X.fromSpecStalk x from Scheme.Opens.fromSpecStalkOfMem_ι _ _ _]
    exact Scheme.fromSpecStalk_closedPoint
  obtain ⟨k, hk⟩ := exists_affineOpenNhds_le (X := X) (x := x) ⟨ιj ''ᵁ O, hxU⟩
  have hkj : (k.obj.1 : X.Opens) ≤ j.obj.1 :=
    hk.trans (Scheme.Hom.image_le_opensRange ιj O |>.trans (by simp [ιj]))
  let h : k ⟶ j := ObjectProperty.homMk (homOfLE (show k.obj ≤ j.obj from hkj))
  have : IsOpenImmersion (D.map h) := inferInstanceAs (IsOpenImmersion (X.homOfLE hkj))
  let ιk : (affineOpenNhdsDiagram X x).obj k ⟶ X := Scheme.Opens.ι (X := X) k.obj.1
  have : IsOpenImmersion ιk := inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι (X := X) k.obj.1))
  have : LocallyOfFiniteType (pullback.snd Z.hom (D.map h) ≫ ιk) := inferInstance
  have : IsLocallyNoetherian (pullback Z.hom (D.map h)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Z.hom (D.map h) ≫ ιk)
  refine ⟨k, h, (isRegular_iff_regular_stalks _).mpr ⟨inferInstance, fun p => ?_⟩⟩
  rw [isRegularLocalRing_stalk_iff_of_isOpenImmersion (pullback.fst Z.hom (D.map h)) p]
  by_contra hreg
  have hmem : Z.hom (pullback.fst Z.hom (D.map h) p) ∉ O := fun hO => hO ⟨_, hreg, rfl⟩
  apply hmem
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  obtain ⟨q, hqO, hq⟩ := hk (pullback.snd Z.hom (D.map h) p).2
  have : D.map h (pullback.snd Z.hom (D.map h) p) = q := by
    apply ιj.isOpenEmbedding.injective
    refine Eq.trans ?_ hq.symm
    change (D.map h ≫ ιj) _ = _
    rw [show D.map h ≫ ιj = ιk from Scheme.homOfLE_ι X hkj]
    rfl
  rwa [this]

end AlgebraicGeometry

end
