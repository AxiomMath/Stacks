module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurveUnitIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineRootsOfUnity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafPushforwardNormal
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Composition
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.UniversallyOpen

/-!
# The unit `A ⟶ j_* j⁻¹ A` along `𝐆_m ⊆ 𝐀¹_k` at a constant sheaf

Let `X` be an integral normal scheme and `j : U ⟶ X` the inclusion of a nonempty open. For every
abelian group `A`, pulling back locally constant functions gives an isomorphism
`A_X ≅ j_* A_U` of abelian sheaves on `X_ét` (the abelian form of [Stacks, Tag 09Z5]). On sections
over an étale `V ⟶ X` it is restriction of locally constant functions along the open immersion
`V ×_X U ⟶ V`, whose image is dense (étale maps are open, and `U` is dense in `X`); since `V` is
normal and `X` integral, every point of `V` has an irreducible open neighbourhood, and on such a
space restriction of locally constant functions to a dense open is bijective.

As `j_*` is fully faithful (`j` is an open immersion), the unit of `j⁻¹ ⊣ j_*` is invertible at
every object of the essential image of `j_*`, so at `A_X`. For `j : 𝐆_m ⟶ 𝐀¹_k` this is
`Stacks.EtaleCohomology.Purity.AffineLineConstantUnitIso k`, for every field `k` and every
abelian group (torsion or not).

## Main results

* `Stacks.EtaleCohomology.Purity.bijective_locallyConstant_comap_of_denseRange`.
* `Stacks.EtaleCohomology.Purity.isIso_constantSheafDirectImageMap_opensι`.
* `Stacks.EtaleCohomology.Purity.affineLineConstantUnitIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.Purity

attribute [-instance] CategoryTheory.catToReflQuiver

section Topology

variable {X V M : Type*} [TopologicalSpace X] [TopologicalSpace V]

/-- A locally constant map on `V` is constant on the part of `V` lying over a preirreducible open
of `X`, along an open embedding `V ⟶ X`. -/
theorem locallyConstant_apply_eq_of_isPreirreducible (f : C(V, X))
    (hf : Topology.IsOpenEmbedding f) (t : LocallyConstant V M) {Z : Set X}
    (hZ : IsPreirreducible Z)
    {v w : V} (hv : f v ∈ Z) (hw : f w ∈ Z) : t v = t w := by
  obtain ⟨z, -, ⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩ := hZ _ _
    (hf.isOpenMap _ (t.isLocallyConstant {t v})) (hf.isOpenMap _ (t.isLocallyConstant {t w}))
    ⟨f v, hv, v, rfl, rfl⟩ ⟨f w, hw, w, rfl, rfl⟩
  rw [hf.injective hab] at hb
  exact (ha : t a = t v).symm.trans hb

/-- Restriction of locally constant functions along a continuous map with dense range is
injective. -/
private theorem injective_locallyConstant_comap_of_denseRange (f : C(V, X)) (hd : DenseRange f) :
    Function.Injective (fun s : LocallyConstant X M => s.comap f) := by
  intro s₁ s₂ h
  ext x
  obtain ⟨a, ha⟩ := hd.exists_mem_open
    ((s₁.isLocallyConstant {s₁ x}).inter (s₂.isLocallyConstant {s₂ x}))
    ⟨x, rfl, rfl⟩
  have h' := congrArg (fun s : LocallyConstant V M => s a) h
  simp only [LocallyConstant.coe_comap, Function.comp_apply] at h'
  rw [← (show s₁ (f a) = s₁ x from ha.1), ← (show s₂ (f a) = s₂ x from ha.2)]
  exact h'

/-- Restriction of locally constant functions along an open embedding with dense range into a
space whose points have preirreducible open neighbourhoods is surjective. -/
private theorem surjective_locallyConstant_comap_of_denseRange (f : C(V, X))
    (hf : Topology.IsOpenEmbedding f) (hd : DenseRange f)
    (hloc : ∀ x : X, ∃ Z : Set X, IsOpen Z ∧ x ∈ Z ∧ IsPreirreducible Z) :
    Function.Surjective (fun s : LocallyConstant X M => s.comap f) := by
  intro t
  choose Z hZo hZx hZ using hloc
  choose v hv using fun x => hd.exists_mem_open (hZo x) ⟨x, hZx x⟩
  have hFZ : ∀ x y, y ∈ Z x → t (v y) = t (v x) := by
    intro x y hy
    obtain ⟨w, hwx, hwy⟩ := hd.exists_mem_open ((hZo x).inter (hZo y)) ⟨y, hy, hZx y⟩
    exact (locallyConstant_apply_eq_of_isPreirreducible f hf t (hZ y) (hv y) hwy).trans
      (locallyConstant_apply_eq_of_isPreirreducible f hf t (hZ x) hwx (hv x))
  refine ⟨⟨fun x => t (v x), ?_⟩, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    exact fun x => ⟨Z x, hZo x, hZx x, hFZ x⟩
  · ext w
    simp only [LocallyConstant.coe_comap, Function.comp_apply, LocallyConstant.coe_mk]
    exact locallyConstant_apply_eq_of_isPreirreducible f hf t (hZ (f w)) (hv (f w)) (hZx (f w))

/-- **Restriction of locally constant functions to a dense open is bijective on a locally
preirreducible space**: if every point of `X` has a preirreducible open neighbourhood and
`f : V ⟶ X` is an open embedding with dense range, then `s ↦ s ∘ f` is a bijection from the
locally constant maps on `X` to those on `V`. -/
theorem bijective_locallyConstant_comap_of_denseRange (f : C(V, X))
    (hf : Topology.IsOpenEmbedding f) (hd : DenseRange f)
    (hloc : ∀ x : X, ∃ Z : Set X, IsOpen Z ∧ x ∈ Z ∧ IsPreirreducible Z) :
    Function.Bijective (fun s : LocallyConstant X M => s.comap f) :=
  ⟨injective_locallyConstant_comap_of_denseRange f hd,
    surjective_locallyConstant_comap_of_denseRange f hf hd hloc⟩

end Topology

/-- Every point of a scheme étale over an integral normal scheme has a preirreducible open
neighbourhood. -/
theorem exists_isPreirreducible_open_of_etale {X W : Scheme.{u}} [IsIntegral X] [IsNormal X]
    (g : W ⟶ X) [Etale g] (w : W) :
    ∃ Z : Set W, IsOpen Z ∧ w ∈ Z ∧ IsPreirreducible Z := by
  obtain ⟨Z, i, hi, hZ, hw⟩ := exists_isIntegral_open_of_etale g w
  refine ⟨Set.range i.base, i.isOpenEmbedding.isOpen_range, hw, ?_⟩
  rw [← Set.image_univ]
  exact ((IrreducibleSpace.isIrreducible_univ Z).image i.base
    i.base.hom.continuous.continuousOn).2

/-- **The constant sheaf on an integral normal scheme is the direct image of the constant sheaf
on a nonempty open** (the abelian form of [Stacks, Tag 09Z5]): pulling back locally constant
functions, `A_X ⟶ j_* A_U`, is an isomorphism. -/
theorem isIso_constantSheafDirectImageMap_opensι {X : Scheme.{u}} [IsIntegral X] [IsNormal X]
    (U : X.Opens) (hU : (U : Set X).Nonempty) (A : Type (u + 1)) [AddCommGroup A] :
    IsIso (constantSheafDirectImageMap.{u, 0} U.ι A) := by
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _), NatTrans.isIso_iff_isIso_app]
  rintro ⟨V⟩
  rw [ConcreteCategory.isIso_iff_bijective]
  let e := smallEtaleConstantSheafSectionsIsoLocallyConstantMapsAb.{u, 0} X A V
  let e' := smallEtaleConstantSheafSectionsIsoLocallyConstantMapsAb.{u, 0} U.toScheme A
    ((smallEtaleBaseChange U.ι).obj V)
  have hV : Etale V.hom := V.prop
  have hVo : IsOpenMap V.hom.base := by
    have h := Etale.iff_flat_and_formallyUnramified.mp hV
    have : Flat V.hom := h.1
    have : LocallyOfFinitePresentation V.hom := h.2.2
    have : UniversallyOpen V.hom := universallyOpen_of_flat_of_locallyOfFinitePresentation V.hom
    exact V.hom.isOpenMap
  have hdense : DenseRange (pullback.fst V.hom U.ι).base := by
    show Dense (Set.range (pullback.fst V.hom U.ι).base)
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    exact (U.isOpen.dense hU).preimage hVo
  have hb := bijective_locallyConstant_comap_of_denseRange (M := A)
    (pullback.fst V.hom U.ι).base.hom (pullback.fst V.hom U.ι).isOpenEmbedding hdense
    (exists_isPreirreducible_open_of_etale (X := X) V.hom)
  refine (Function.Bijective.of_comp_iff'
    ((ConcreteCategory.isIso_iff_bijective e'.hom).1 inferInstance) _).1 ?_
  have hfun : (e'.hom ∘ ((sheafToPresheaf _ _).map
      (constantSheafDirectImageMap.{u, 0} U.ι A)).app (op V)) =
      (fun s : LocallyConstant V.left A => s.comap (pullback.fst V.hom U.ι).base.hom) ∘ e.hom :=
    funext fun s => constantSheafDirectImageMap_app.{u, 0} U.ι A V s
  rw [hfun]
  exact hb.comp ((ConcreteCategory.isIso_iff_bijective e.hom).1 inferInstance)

/-- The unit of `j⁻¹ ⊣ j_*` along an étale monomorphism is invertible at every object of the
essential image of `j_*`: `j_*` is fully faithful. -/
theorem isIso_smallEtaleAdjunctionAb_unit_app_pushforward {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j] [Mono j] (B : Sheaf (smallEtaleTopology U) Ab.{u + 1}) :
    IsIso ((smallEtaleAdjunctionAb j).unit.app ((smallEtalePushforwardAb j).obj B)) := by
  have : IsIso ((smallEtaleAdjunctionAb j).unit.app ((smallEtalePushforwardAb j).obj B) ≫
      (smallEtalePushforwardAb j).map ((smallEtaleAdjunctionAb j).counit.app B)) := by
    rw [(smallEtaleAdjunctionAb j).right_triangle_components B]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_right _ ((smallEtalePushforwardAb j).map
    ((smallEtaleAdjunctionAb j).counit.app B))

/-- `𝐀¹_k` is a normal scheme. -/
theorem isNormal_affineLine (k : Type u) [Field k] : IsNormal (affineLine k) :=
  have := smooth_affineSpace_over (ULift.{u} (Fin 1)) (Spec (.of k))
  isNormal_of_smooth_over_field (affineLine k ↘ Spec (.of k))

/-- **The unit `A ⟶ j_* j⁻¹ A` along `j : 𝐆_m ⟶ 𝐀¹_k` is an isomorphism at every constant
abelian sheaf** (input A1b of relative purity), over every field `k`: the constant sheaf on
`𝐀¹_k` is the direct image of the constant sheaf on `𝐆_m`
(`Stacks.EtaleCohomology.Purity.isIso_constantSheafDirectImageMap_opensι`), and the unit is
invertible on the essential image of the fully faithful `j_*`. -/
theorem affineLineConstantUnitIso (k : Type u) [Field k] : AffineLineConstantUnitIso k := by
  intro M _ _ _ _
  have : IsIntegral (affineLine k) :=
    IsIntegral.of_isIso (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)).inv
  have := isNormal_affineLine k
  obtain ⟨⟨x, hx⟩⟩ := nonempty_punctured k
  have := isIso_constantSheafDirectImageMap_opensι (punctured k) ⟨x, hx⟩ M
  exact isIso_app_of_iso_of_isIso _
    (asIso (constantSheafDirectImageMap.{u, 0} (punctured k).ι M)).symm
    (isIso_smallEtaleAdjunctionAb_unit_app_pushforward (punctured k).ι
      ((constantSheaf (smallEtaleTopology (punctured k).toScheme) Ab.{u + 1}).obj M))

end Stacks.EtaleCohomology.Purity

end
