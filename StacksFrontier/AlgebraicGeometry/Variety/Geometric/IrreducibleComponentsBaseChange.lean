module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed

/-!
# Irreducible components after extending the base field

Let `K/k` be an extension of fields and let `X` be a scheme over `k`. The inverse image in
`X ×_{Spec k} Spec K` of an irreducible component of `X` is a union of irreducible components
of the base change, taking the image under the projection sends irreducible components of the
base change to irreducible components of `X`, and every irreducible component of `X` arises in
this way.

## Main results

* `AlgebraicGeometry.preimage_irreducibleComponent_eq_sUnion` identifies the inverse image of an
  irreducible component with the union of the irreducible components it contains.
* `AlgebraicGeometry.mapsTo_irreducibleComponents_baseChange` shows that taking images under the
  projection sends irreducible components to irreducible components.
* `AlgebraicGeometry.surjOn_irreducibleComponents_baseChange` shows that every irreducible
  component downstairs occurs as such an image.

## Implementation notes

The base change is the categorical pullback of the structure morphism along the map of spectra,
and the canonical map on irreducible components is `Z ↦ (pullback.fst _ _).base '' Z`. Writing
the inverse image of a component as the union of all components contained in it specifies which
components occur, including when that inverse image is empty.

The two statements about images are reduced to the separably closed case by comparing the base
change along `K/k` with the base change along the algebraic closures of `k` and of `K`; the key
topological input is that the projection is a closed generalizing map, which holds because it is
both flat and integral.

## References

* [Stacks Project, Tag 04KW](https://stacks.math.columbia.edu/tag/04KW)
* [Stacks Project, Tag 04KX](https://stacks.math.columbia.edu/tag/04KX)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- A point specializing to the generic point of an irreducible component equals it. -/
private theorem eq_of_specializes_of_isGenericPoint_of_mem_irreducibleComponents
    {α : Type*} [TopologicalSpace α] [T0Space α] {x η : α} {T : Set α}
    (hη : IsGenericPoint η T) (hT : T ∈ irreducibleComponents α) (hx : x ⤳ η) : x = η := by
  have hsub : closure {η} ⊆ closure {x} := specializes_iff_closure_subset.mp hx
  rw [hη.def] at hsub
  exact (hx.antisymm (specializes_iff_closure_subset.mpr
    (hη.def ▸ hT.2 isIrreducible_singleton.closure hsub))).eq

/-- **Stacks Project, Tag 04KW.** After extension of the base field, the inverse image
of an irreducible component is a union of irreducible components. -/
@[stacks 04KW]
public theorem preimage_irreducibleComponent_eq_sUnion
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (T : Set X) (hT : T ∈ irreducibleComponents X) :
    let p : Scheme.{u} :=
      pullback (C := Scheme) f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    let π : p ⟶ X :=
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    π.base ⁻¹' T =
      ⋃₀ {Z : Set p | Z ∈ irreducibleComponents p ∧ Z ⊆ π.base ⁻¹' T} := by
  classical
  dsimp only
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let p : Scheme.{u} := pullback f g
  let π : p ⟶ X := pullback.fst f g
  have : Flat π :=
    (Flat.isStableUnderBaseChange).of_isPullback (IsPullback.of_hasPullback f g).flip
      (Flat.SpecMap_iff.mpr ((RingHom.flat_algebraMap_iff).mpr inferInstance))
  let η : genericPoints X := genericPoints.ofComponent ⟨T, hT⟩
  have hη : IsGenericPoint (η : X) T := genericPoints.isGenericPoint_ofComponent ⟨T, hT⟩
  ext x
  refine ⟨fun hx ↦ ?_, fun ⟨Z, hZ, hxZ⟩ ↦ hZ.2 hxZ⟩
  obtain ⟨x', hx'x, hπx'⟩ := Flat.generalizingMap π (hη.specializes hx)
  let C : irreducibleComponents p :=
    ⟨irreducibleComponent x', irreducibleComponent_mem_irreducibleComponents x'⟩
  let ξ : p := genericPoints.ofComponent C
  have hξC : IsGenericPoint ξ (C : Set p) := genericPoints.isGenericPoint_ofComponent C
  have hxC : x ∈ (C : Set p) :=
    hx'x.mem_closed (isClosed_of_mem_irreducibleComponents _ C.2) mem_irreducibleComponent
  have hπξη : π ξ ⤳ (η : X) := by
    simpa [hπx'] using
      (hξC.specializes (mem_irreducibleComponent : x' ∈ (C : Set p))).map π.continuous
  have hπξeq : π ξ = (η : X) :=
    eq_of_specializes_of_isGenericPoint_of_mem_irreducibleComponents hη hT hπξη
  refine Set.mem_sUnion.mpr ⟨C, ⟨C.2, fun z hz ↦ hη.specializes_iff_mem.mp ?_⟩, hxC⟩
  simpa [hπξeq] using (hξC.specializes hz).map π.continuous

/-- The image of an irreducible component under a continuous closed generalizing map between
sober `T0` spaces is an irreducible component. -/
private theorem image_irreducibleComponent_of_closed_generalizing
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [T0Space X] [QuasiSober X] [T0Space Y] [QuasiSober Y]
    (f : X → Y) (hf : Continuous f) (hclosed : IsClosedMap f)
    (hgen : GeneralizingMap f) (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    f '' Z ∈ irreducibleComponents Y := by
  let η : genericPoints X := genericPoints.ofComponent ⟨Z, hZ⟩
  have hη : IsGenericPoint η.1 Z := genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩
  have hI : IsIrreducible (f '' Z) := hZ.1.image f hf.continuousOn
  have hIc : IsClosed (f '' Z) := hclosed Z (isClosed_of_mem_irreducibleComponents Z hZ)
  have hηI : IsGenericPoint (f η.1) (f '' Z) := by
    simpa only [hIc.closure_eq] using hη.image hf
  refine ⟨hI, fun V hV hIV ↦ ?_⟩
  obtain ⟨W, hW, hVW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible V hV
  have hIW : f '' Z ⊆ W := hIV.trans hVW
  let ξ : genericPoints Y := genericPoints.ofComponent ⟨W, hW⟩
  have hξ : IsGenericPoint ξ.1 W := genericPoints.isGenericPoint_ofComponent ⟨W, hW⟩
  obtain ⟨x, hx, hfx⟩ := hgen (hξ.specializes (hIW ⟨η.1, hη.mem, rfl⟩))
  have hxη : x = η.1 :=
    eq_of_specializes_of_isGenericPoint_of_mem_irreducibleComponents hη hZ hx
  have hξI : W = f '' Z := by rw [← hξ, ← hηI, ← hfx, hxη]
  rwa [hξI] at hVW

/-- For an algebraic extension the projection from the base change is closed and generalizing,
so it carries irreducible components to irreducible components. -/
@[ega "IV 2.3.5" "(ii), special case"]
private theorem mapsTo_irreducibleComponents_baseChange_of_isAlgebraic
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    Set.MapsTo
      (fun Z ↦ (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base '' Z)
      (irreducibleComponents
        (pullback (C := Scheme) f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
      (irreducibleComponents X) := by
  let p := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [IsIntegralHom.SpecMap_iff]
    change (algebraMap k K).IsIntegral
    exact algebraMap_isIntegral_iff.mpr Algebra.IsAlgebraic.isIntegral
  exact fun Z hZ ↦ image_irreducibleComponent_of_closed_generalizing p.base p.continuous
    p.isClosedMap (Flat.generalizingMap p) Z hZ

/-- An isomorphism of schemes carries irreducible components to irreducible components. -/
private theorem image_irreducibleComponent_of_iso
    {X Y : Scheme.{u}} (e : X ≅ Y) (Z : Set X)
    (hZ : Z ∈ irreducibleComponents X) : e.hom.base '' Z ∈ irreducibleComponents Y := by
  have hhomeo := (TopCat.isIso_iff_isHomeomorph _).mp
    (inferInstance : IsIso (Scheme.forgetToTop.map e.hom))
  exact image_irreducibleComponent_of_closed_generalizing e.hom.base e.hom.continuous
    hhomeo.isClosedMap hhomeo.isOpenEmbedding.generalizingMap Z hZ

/-- Base changing `X ⟶ S` first along `g₁` and then along `h₁` agrees, up to isomorphism over
`X`, with base changing along `g₂` and then along `h₂` whenever `h₁ ≫ g₁ = h₂ ≫ g₂`. -/
private theorem exists_iso_pullback_pullback_snd_comp_fst {X S A A' B : Scheme.{u}}
    (f : X ⟶ S) (g₁ : A ⟶ S) (h₁ : B ⟶ A) (g₂ : A' ⟶ S) (h₂ : B ⟶ A')
    (h : h₁ ≫ g₁ = h₂ ≫ g₂) :
    ∃ e : pullback (pullback.snd f g₁) h₁ ≅ pullback (pullback.snd f g₂) h₂,
      pullback.fst (pullback.snd f g₁) h₁ ≫ pullback.fst f g₁ =
        e.hom ≫ pullback.fst (pullback.snd f g₂) h₂ ≫ pullback.fst f g₂ := by
  let eMid : pullback f (h₁ ≫ g₁) ≅ pullback f (h₂ ≫ g₂) := pullback.congrHom rfl h
  refine ⟨pullbackLeftPullbackSndIso f g₁ h₁ ≪≫ eMid ≪≫
    (pullbackLeftPullbackSndIso f g₂ h₂).symm, ?_⟩
  have hMidFst : eMid.hom ≫ pullback.fst f (h₂ ≫ g₂) = pullback.fst f (h₁ ≫ g₁) := by
    simp only [eMid, pullback.congrHom_hom, pullback.map]
    exact pullback.lift_fst _ _ _
  calc
    pullback.fst (pullback.snd f g₁) h₁ ≫ pullback.fst f g₁ =
        (pullbackLeftPullbackSndIso f g₁ h₁).hom ≫ pullback.fst f (h₁ ≫ g₁) :=
      (pullbackLeftPullbackSndIso_hom_fst f g₁ h₁).symm
    _ = (pullbackLeftPullbackSndIso f g₁ h₁).hom ≫ eMid.hom ≫ pullback.fst f (h₂ ≫ g₂) := by
      simp only [hMidFst]
    _ = _ := by
      simp [eMid, Category.assoc]

/-- If `r ≫ p₁ = e.hom ≫ q ≫ p₂` with `e` an isomorphism and `q`, `p₂` sending irreducible
components to irreducible components, then so does `r ≫ p₁`. -/
private theorem image_image_mem_irreducibleComponents_of_comp_eq
    {Y Y' X₁ X₂ X : Scheme.{u}} (r : Y ⟶ X₁) (p₁ : X₁ ⟶ X) (e : Y ≅ Y') (q : Y' ⟶ X₂)
    (p₂ : X₂ ⟶ X) (hcomm : r ≫ p₁ = e.hom ≫ q ≫ p₂)
    (hq : Set.MapsTo (fun Z ↦ q.base '' Z) (irreducibleComponents Y') (irreducibleComponents X₂))
    (hp : Set.MapsTo (fun Z ↦ p₂.base '' Z) (irreducibleComponents X₂) (irreducibleComponents X))
    {W : Set Y} (hW : W ∈ irreducibleComponents Y) :
    p₁.base '' (r.base '' W) ∈ irreducibleComponents X := by
  have hfun : p₁.base ∘ r.base = p₂.base ∘ q.base ∘ e.hom.base := by
    funext y
    simpa [Scheme.Hom.comp_base] using congrArg (fun g : Y ⟶ X => g.base y) hcomm
  have himage : p₁.base '' (r.base '' W) = p₂.base '' (q.base '' (e.hom.base '' W)) := by
    simpa only [Set.image_image, Function.comp_def] using congrArg (· '' W) hfun
  rw [himage]
  exact hp (hq (image_irreducibleComponent_of_iso e W hW))

/-- Every irreducible component of `X` is the image of an irreducible component of the base
change, provided taking images sends irreducible components to irreducible components. -/
private theorem surjOn_irreducibleComponents_baseChange_of_mapsTo
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (hmaps : Set.MapsTo
      (fun Z ↦ (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base '' Z)
      (irreducibleComponents
        (pullback (C := Scheme) f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
      (irreducibleComponents X)) :
    Set.SurjOn
      (fun Z ↦ (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base '' Z)
      (irreducibleComponents
        (pullback (C := Scheme) f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
      (irreducibleComponents X) := by
  classical
  intro T hT
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hspecsurj : Function.Surjective g.base := by
    intro x
    obtain ⟨y⟩ : Nonempty (Spec (.of K)) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
    exact ⟨y, Subsingleton.elim _ _⟩
  have : Surjective g := (surjective_iff g).mpr hspecsurj
  let p : Scheme := pullback (C := Scheme) f g
  let π : p ⟶ X := pullback.fst f g
  obtain ⟨t, ht⟩ := hT.1.nonempty
  obtain ⟨z, hz⟩ := (surjective_iff π).mp (inferInstance : Surjective π) t
  have hpre : π.base ⁻¹' T = ⋃₀ {Z : Set p |
      Z ∈ irreducibleComponents p ∧ Z ⊆ π.base ⁻¹' T} := by
    simpa [p, π, g] using (preimage_irreducibleComponent_eq_sUnion k K X f T hT)
  have hzpre : z ∈ π.base ⁻¹' T := by simpa [hz] using ht
  rw [hpre] at hzpre
  obtain ⟨Z, hZ, -⟩ := Set.mem_sUnion.mp hzpre
  have hsub : π.base '' Z ⊆ T := Set.image_subset_iff.mpr hZ.2
  exact ⟨Z, hZ.1, hsub.antisymm ((hmaps hZ.1).2 hT.1 hsub)⟩

/-- **Stacks Project, Tag 04KX.** Let `K/k` be an extension of fields and let `X` be a scheme
over `k`. The image of every irreducible component of `X ×_{Spec k} Spec K` under the projection
to `X` is an irreducible component of `X`. -/
@[stacks 04KX, sga "3 VIA 2.6.0"]
public theorem mapsTo_irreducibleComponents_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    Set.MapsTo
      (fun Z ↦ (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base '' Z)
      (irreducibleComponents
        (pullback (C := Scheme) f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
      (irreducibleComponents X) := by
  classical
  let M := AlgebraicClosure k
  let L := AlgebraicClosure K
  let : Algebra k L := Algebra.compHom L (algebraMap k K)
  let ι : M →ₐ[k] L := IsAlgClosed.lift
  let : Algebra M L := ι.toRingHom.toAlgebra
  let gK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let gM := Spec.map (CommRingCat.ofHom (algebraMap k M))
  let gL := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let gKL := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let gML := Spec.map (CommRingCat.ofHom (algebraMap M L))
  have hcompK : gKL ≫ gK = gL := by
    dsimp [gKL, gK, gL]
    rw [← Spec.map_comp]
    congr 1
  have hcompM : gML ≫ gM = gL := by
    dsimp [gML, gM, gL]
    rw [← Spec.map_comp]
    congr 1
    ext x
    change ι (algebraMap k M x) = algebraMap k L x
    exact ι.commutes x
  let XK := pullback f gK
  let XM := pullback f gM
  obtain ⟨e, hcomm⟩ :=
    exists_iso_pullback_pullback_snd_comp_fst f gK gKL gM gML (hcompK.trans hcompM.symm)
  have : IsSepClosed M := IsSepClosed.of_isAlgClosed M
  have : IsSepClosed L := IsSepClosed.of_isAlgClosed L
  let fK := pullback.snd f gK
  let fM := pullback.snd f gM
  intro T hT
  obtain ⟨W, hW, hReq⟩ : ∃ W ∈ irreducibleComponents (pullback (C := Scheme) fK gKL),
      (pullback.fst fK gKL).base '' W = T :=
    surjOn_irreducibleComponents_baseChange_of_mapsTo K L XK fK
      (mapsTo_irreducibleComponents_baseChange_of_isAlgebraic K L XK fK) hT
  change (pullback.fst f gK).base '' T ∈ irreducibleComponents X
  rw [← hReq]
  exact image_image_mem_irreducibleComponents_of_comp_eq _ _ e (pullback.fst fM gML)
    (pullback.fst f gM) hcomm (bijOn_irreducibleComponents_baseChange_of_isSepClosed M L XM fM).1
    (mapsTo_irreducibleComponents_baseChange_of_isAlgebraic k M X f) hW

/-- **Stacks Project, Tag 04KX.** Let `K/k` be an extension of fields and let `X` be a scheme
over `k`. Every irreducible component of `X` is the image of an irreducible component of
`X ×_{ Spec k} Spec K` under the projection to `X`. -/
@[stacks 04KX]
public theorem surjOn_irreducibleComponents_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    Set.SurjOn
      (fun Z ↦ (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base '' Z)
      (irreducibleComponents
        (pullback (C := Scheme) f (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
      (irreducibleComponents X) :=
  surjOn_irreducibleComponents_baseChange_of_mapsTo k K X f
    (mapsTo_irreducibleComponents_baseChange k K X f)

end AlgebraicGeometry
