module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCoproduct
public import StacksFrontier.AlgebraicGeometry.SigmaSpecNaturality

/-!
# Functoriality of the finite coproduct in the big affine fppf category

`AlgebraicGeometry.BigAffineFppf.sigmaObj` is the explicit coproduct of a finite family of
objects of the big affine fppf category over `S`, computed on underlying schemes; its universal
property is `AlgebraicGeometry.BigAffineFppf.isColimitSigmaCofan`. This file makes it a
functor: a family of morphisms induces a morphism of coproducts, the construction is functorial,
and a finite family of diagrams indexed by a common category assembles into a single diagram of
coproducts. It also identifies the underlying scheme of such a coproduct with the spectrum of a
product of rings.

## Main definitions

* `AlgebraicGeometry.Cofan.isColimitOfIsoSummands`: a colimiting cofan read through a family of
  isomorphisms of its summands is colimiting.
* `AlgebraicGeometry.isColimitSpecPiCofan`: the spectrum of a finite product of rings, as a
  colimiting cofan on summands presented by the spectra of the factors.
* `AlgebraicGeometry.BigAffineFppf.sigmaDesc`: a morphism out of the explicit coproduct given
  by a family of morphisms out of the summands.
* `AlgebraicGeometry.BigAffineFppf.sigmaMap` and
  `AlgebraicGeometry.BigAffineFppf.sigmaMapIso`: the morphism, respectively isomorphism, of
  coproducts induced by a family of morphisms, respectively isomorphisms.
* `AlgebraicGeometry.BigAffineFppf.sigmaFunctor`: the pointwise coproduct of a finite family of
  diagrams indexed by a common category.
* `AlgebraicGeometry.BigAffineFppf.sigmaObjIsoSpecPi`: the underlying scheme of a finite
  coproduct in the big affine fppf category, identified with the spectrum of the product of the
  rings presenting the summands.

## Main results

* `AlgebraicGeometry.BigAffineFppf.sigma_hom_ext`: two morphisms out of the explicit coproduct
  agree as soon as they agree on each inclusion.
* `AlgebraicGeometry.BigAffineFppf.sigmaMap_id` and
  `AlgebraicGeometry.BigAffineFppf.sigmaMap_comp`: functoriality of the coproduct.
* `AlgebraicGeometry.BigAffineFppf.toScheme_map_sigmaIncl_comp_sigmaMap`: the underlying scheme
  morphism of an induced morphism of coproducts commutes with the coproduct inclusions.
* `AlgebraicGeometry.BigAffineFppf.property_toScheme_map_sigmaMap` and
  `AlgebraicGeometry.BigAffineFppf.isThickening_toScheme_map_sigmaMap`: that morphism has a
  property local at the target, respectively is a thickening, as soon as every summand does.
* `AlgebraicGeometry.BigAffineFppf.sigmaObjIsoSpecPi_hom_naturality`: the identification with
  the spectrum of a product is natural in the family, for a family of morphisms realised by
  ring maps on the presenting rings.

## Implementation notes

The index type `I` of a coproduct need only be `u`-small, whereas the product `∏ k, R k` of a
family of rings in `CommRingCat.{u}` needs its index type in `Type u`. The identification with
the spectrum of a product is therefore stated for an equivalence `ε : K ≃ I` with `K : Type u`,
and the family of rings is indexed by `K`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe w u

/-! ### Two auxiliary colimiting cofans -/

/-- A colimiting cofan read through a family of isomorphisms of its summands is again
colimiting. -/
noncomputable def Cofan.isColimitOfIsoSummands {C : Type*} [Category C] {J : Type*}
    {X Y : J → C} {P : C} {p : ∀ j, Y j ⟶ P} (hp : IsColimit (Cofan.mk P p))
    (e : ∀ j, X j ≅ Y j) : IsColimit (Cofan.mk P fun j ↦ (e j).hom ≫ p j) := by
  refine Cofan.IsColimit.mk _
    (fun t ↦ Cofan.IsColimit.desc hp fun j ↦ (e j).inv ≫ t.inj j) ?_ ?_
  · intro t j
    have hfac : p j ≫ Cofan.IsColimit.desc hp (fun j ↦ (e j).inv ≫ t.inj j) =
        (e j).inv ≫ t.inj j := Cofan.IsColimit.fac hp _ j
    simp only [cofan_mk_inj]
    rw [Category.assoc, hfac, Iso.hom_inv_id_assoc]
  · intro t m hm
    refine Cofan.IsColimit.hom_ext hp _ _ fun j ↦ ?_
    have hfac : p j ≫ Cofan.IsColimit.desc hp (fun j ↦ (e j).inv ≫ t.inj j) =
        (e j).inv ≫ t.inj j := Cofan.IsColimit.fac hp _ j
    simp only [cofan_mk_inj]
    rw [hfac, ← hm j, cofan_mk_inj, Category.assoc, Iso.inv_hom_id_assoc]

/-- The spectrum of a finite product of rings is the coproduct of the spectra of the factors:
for summands `X k ≅ Spec (R k)`, the cofan on `Spec (∏ k, R k)` whose injections are the spectra
of the projections is colimiting. -/
noncomputable def isColimitSpecPiCofan {K : Type u} [Finite K] {X : K → Scheme.{u}}
    (R : K → CommRingCat.{u}) (e : ∀ k, X k ≅ Spec (R k)) :
    IsColimit (Cofan.mk (Spec (.of <| Π k, R k)) fun k ↦ (e k).hom ≫
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun k ↦ (R k : Type u)) k))) :=
  Cofan.isColimitOfIso (Cofan.isColimitOfIsoSummands (coproductIsCoproduct _) e)
    (asIso (sigmaSpec R)) fun k ↦ by
      rw [Category.assoc, asIso_hom, ι_sigmaSpec]

namespace BigAffineFppf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {I : Type w} [Finite I] [Small.{u} I]

/-! ### Morphisms out of a finite coproduct -/

section Desc

variable {A : I → BigAffineFppf B S hS} {T : BigAffineFppf B S hS}

/-- The morphism out of the explicit coproduct of a finite family of objects of the big affine
fppf category over `S` determined by a family of morphisms out of the summands. -/
noncomputable def sigmaDesc (f : ∀ i, A i ⟶ T) : sigmaObj B S hS A ⟶ T :=
  Cofan.IsColimit.desc (isColimitSigmaCofan B S hS A) f

/-- The morphism `AlgebraicGeometry.BigAffineFppf.sigmaDesc` restricts to `f i` on the `i`-th
summand. -/
@[reassoc (attr := simp)]
theorem sigmaIncl_sigmaDesc (f : ∀ i, A i ⟶ T) (i : I) :
    sigmaIncl B S hS A i ≫ sigmaDesc B S hS f = f i :=
  Cofan.IsColimit.fac (isColimitSigmaCofan B S hS A) f i

/-- Two morphisms out of the explicit coproduct of a finite family of objects of the big affine
fppf category over `S` agree as soon as they agree on every inclusion. -/
theorem sigma_hom_ext {g h : sigmaObj B S hS A ⟶ T}
    (w : ∀ i, sigmaIncl B S hS A i ≫ g = sigmaIncl B S hS A i ≫ h) : g = h :=
  Cofan.IsColimit.hom_ext (isColimitSigmaCofan B S hS A) g h w

end Desc

/-! ### The coproduct of a family of morphisms -/

section Map

variable {A A' A'' : I → BigAffineFppf B S hS}

/-- The morphism of explicit coproducts induced by a family of morphisms of the summands. -/
noncomputable def sigmaMap (f : ∀ i, A i ⟶ A' i) :
    sigmaObj B S hS A ⟶ sigmaObj B S hS A' :=
  sigmaDesc B S hS fun i ↦ f i ≫ sigmaIncl B S hS A' i

/-- The induced morphism of coproducts restricts on the `i`-th summand to `f i` followed by the
inclusion. -/
@[reassoc (attr := simp)]
theorem sigmaIncl_sigmaMap (f : ∀ i, A i ⟶ A' i) (i : I) :
    sigmaIncl B S hS A i ≫ sigmaMap B S hS f = f i ≫ sigmaIncl B S hS A' i :=
  sigmaIncl_sigmaDesc B S hS _ i

/-- The coproduct of identity morphisms is the identity. -/
@[simp]
theorem sigmaMap_id : sigmaMap B S hS (fun i ↦ 𝟙 (A i)) = 𝟙 (sigmaObj B S hS A) :=
  sigma_hom_ext B S hS fun i ↦ by rw [sigmaIncl_sigmaMap, Category.id_comp, Category.comp_id]

/-- The coproduct of a family of composites is the composite of the coproducts. -/
theorem sigmaMap_comp (f : ∀ i, A i ⟶ A' i) (g : ∀ i, A' i ⟶ A'' i) :
    sigmaMap B S hS (fun i ↦ f i ≫ g i) = sigmaMap B S hS f ≫ sigmaMap B S hS g :=
  sigma_hom_ext B S hS fun i ↦ by
    rw [sigmaIncl_sigmaMap, sigmaIncl_sigmaMap_assoc, sigmaIncl_sigmaMap, Category.assoc]

/-- The underlying scheme morphisms of the morphism of coproducts induced by a family of
morphisms commute with the coproduct inclusions. -/
@[reassoc]
theorem toScheme_map_sigmaIncl_comp_sigmaMap (f : ∀ i, A i ⟶ A' i) (i : I) :
    (toScheme B S hS).map (sigmaIncl B S hS A i) ≫ (toScheme B S hS).map (sigmaMap B S hS f) =
      (toScheme B S hS).map (f i) ≫ (toScheme B S hS).map (sigmaIncl B S hS A' i) := by
  rw [← Functor.map_comp, ← Functor.map_comp, sigmaIncl_sigmaMap]

/-- A property of scheme morphisms local at the target holds for the underlying scheme morphism
of an induced morphism of coproducts as soon as it holds for every summand. -/
theorem property_toScheme_map_sigmaMap (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] (f : ∀ i, A i ⟶ A' i)
    (hf : ∀ i, P ((toScheme B S hS).map (f i))) :
    P ((toScheme B S hS).map (sigmaMap B S hS f)) :=
  IsZariskiLocalAtTarget.of_cofan (isColimitToSchemeSigmaCofan B S hS A)
    (isColimitToSchemeSigmaCofan B S hS A') (toScheme_map_sigmaIncl_comp_sigmaMap B S hS f) hf

/-- The underlying scheme morphism of an induced morphism of coproducts is a thickening as soon
as the underlying scheme morphism of every summand is. -/
theorem isThickening_toScheme_map_sigmaMap (f : ∀ i, A i ⟶ A' i)
    (hf : ∀ i, Stacks.Thickenings.IsThickening ((toScheme B S hS).map (f i))) :
    Stacks.Thickenings.IsThickening ((toScheme B S hS).map (sigmaMap B S hS f)) :=
  Stacks.Thickenings.isThickening_of_cofan (isColimitToSchemeSigmaCofan B S hS A)
    (isColimitToSchemeSigmaCofan B S hS A') _
    (toScheme_map_sigmaIncl_comp_sigmaMap B S hS f) hf

/-- The isomorphism of explicit coproducts induced by a family of isomorphisms of the
summands. -/
@[simps]
noncomputable def sigmaMapIso (e : ∀ i, A i ≅ A' i) :
    sigmaObj B S hS A ≅ sigmaObj B S hS A' where
  hom := sigmaMap B S hS fun i ↦ (e i).hom
  inv := sigmaMap B S hS fun i ↦ (e i).inv
  hom_inv_id := by simp [← sigmaMap_comp]
  inv_hom_id := by simp [← sigmaMap_comp]

end Map

/-! ### The pointwise coproduct of a finite family of diagrams -/

/-- The pointwise coproduct of a finite family of diagrams in the big affine fppf category over
`S` indexed by a common category: at an object it is the explicit coproduct of the values of
the members, and at a morphism the induced morphism of coproducts. -/
noncomputable def sigmaFunctor {K : Type*} [Category K]
    (D : I → (K ⥤ BigAffineFppf B S hS)) : K ⥤ BigAffineFppf B S hS where
  obj k := sigmaObj B S hS fun i ↦ (D i).obj k
  map g := sigmaMap B S hS fun i ↦ (D i).map g
  map_id k := by
    rw [← sigmaMap_id]
    exact congrArg (sigmaMap B S hS) (funext fun i ↦ (D i).map_id k)
  map_comp g g' := by
    rw [← sigmaMap_comp]
    exact congrArg (sigmaMap B S hS) (funext fun i ↦ (D i).map_comp g g')

/-- The value of the pointwise coproduct at an object is the coproduct of the values. -/
@[simp]
theorem sigmaFunctor_obj {K : Type*} [Category K] (D : I → (K ⥤ BigAffineFppf B S hS)) (k : K) :
    (sigmaFunctor B S hS D).obj k = sigmaObj B S hS fun i ↦ (D i).obj k := rfl

/-- The value of the pointwise coproduct at a morphism is the induced morphism of
coproducts. -/
@[simp]
theorem sigmaFunctor_map {K : Type*} [Category K] (D : I → (K ⥤ BigAffineFppf B S hS))
    {k k' : K} (g : k ⟶ k') :
    (sigmaFunctor B S hS D).map g = sigmaMap B S hS fun i ↦ (D i).map g := rfl

/-- The inclusions of the summands into the pointwise coproduct of a finite family of diagrams
are natural. -/
@[reassoc (attr := simp)]
theorem sigmaIncl_sigmaFunctor_map {K : Type*} [Category K]
    (D : I → (K ⥤ BigAffineFppf B S hS)) {k k' : K} (g : k ⟶ k') (i : I) :
    sigmaIncl B S hS (fun i ↦ (D i).obj k) i ≫ (sigmaFunctor B S hS D).map g =
      (D i).map g ≫ sigmaIncl B S hS (fun i ↦ (D i).obj k') i :=
  sigmaIncl_sigmaMap B S hS _ i

/-! ### The underlying scheme of a finite coproduct as the spectrum of a product -/

section SpecPi

variable {A A' : I → BigAffineFppf B S hS} {K : Type u} (ε : K ≃ I)

/-- The underlying scheme of the explicit coproduct of a finite family of objects of the big
affine fppf category over `S`, identified with the spectrum of the product of a family of rings
presenting the summands, indexed through an equivalence `ε : K ≃ I`. -/
noncomputable def sigmaObjIsoSpecPi (R : K → CommRingCat.{u})
    (e : ∀ k, (toScheme B S hS).obj (A (ε k)) ≅ Spec (R k)) :
    (toScheme B S hS).obj (sigmaObj B S hS A) ≅ Spec (.of <| Π k, R k) :=
  haveI : Finite K := ε.finite_iff.mpr ‹_›
  IsColimit.coconePointUniqueUpToIso
    (Cofan.isColimitEquivOfEquiv ε _ (isColimitToSchemeSigmaCofan B S hS A))
    (isColimitSpecPiCofan R e)

/-- Under `AlgebraicGeometry.BigAffineFppf.sigmaObjIsoSpecPi`, the inclusion of the summand at
`ε k` becomes `e k` followed by the spectrum of the `k`-th projection. -/
@[simp]
theorem toScheme_map_sigmaIncl_sigmaObjIsoSpecPi_hom (R : K → CommRingCat.{u})
    (e : ∀ k, (toScheme B S hS).obj (A (ε k)) ≅ Spec (R k)) (k : K) :
    (toScheme B S hS).map (sigmaIncl B S hS A (ε k)) ≫
        (sigmaObjIsoSpecPi B S hS ε R e).hom =
      (e k).hom ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun k ↦ (R k : Type u)) k)) :=
  have : Finite K := ε.finite_iff.mpr ‹_›
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (Cofan.isColimitEquivOfEquiv ε _ (isColimitToSchemeSigmaCofan B S hS A))
    (isColimitSpecPiCofan R e) ⟨k⟩

/-- The identification of the underlying scheme of a finite coproduct with the spectrum of a
product of rings is natural: a family of morphisms of the summands realised on the presenting
rings by ring maps `ψ k : R' k ⟶ R k` induces on the products the ring map assembled from the
composites `∏ R' ⟶ R' k ⟶ R k`. -/
theorem sigmaObjIsoSpecPi_hom_naturality (R R' : K → CommRingCat.{u})
    (e : ∀ k, (toScheme B S hS).obj (A (ε k)) ≅ Spec (R k))
    (e' : ∀ k, (toScheme B S hS).obj (A' (ε k)) ≅ Spec (R' k))
    (f : ∀ i, A i ⟶ A' i) (ψ : ∀ k, R' k ⟶ R k)
    (hψ : ∀ k, (toScheme B S hS).map (f (ε k)) ≫ (e' k).hom =
      (e k).hom ≫ Spec.map (ψ k)) :
    (toScheme B S hS).map (sigmaMap B S hS f) ≫ (sigmaObjIsoSpecPi B S hS ε R' e').hom =
      (sigmaObjIsoSpecPi B S hS ε R e).hom ≫ Spec.map (CommRingCat.ofHom
        (RingHom.pi fun k ↦ (ψ k).hom.comp
          (Pi.evalRingHom (fun k ↦ (R' k : Type u)) k))) := by
  have : Finite K := ε.finite_iff.mpr ‹_›
  refine Cofan.IsColimit.hom_ext
    (Cofan.isColimitEquivOfEquiv ε _ (isColimitToSchemeSigmaCofan B S hS A)) _ _ fun k ↦ ?_
  simp only [cofan_mk_inj]
  have hl : (toScheme B S hS).map (sigmaIncl B S hS A (ε k)) ≫
      (toScheme B S hS).map (sigmaMap B S hS f) ≫ (sigmaObjIsoSpecPi B S hS ε R' e').hom =
      (e k).hom ≫ Spec.map (ψ k) ≫
        Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun k ↦ (R' k : Type u)) k)) := by
    rw [← Functor.map_comp_assoc, sigmaIncl_sigmaMap, Functor.map_comp_assoc,
      toScheme_map_sigmaIncl_sigmaObjIsoSpecPi_hom, ← Category.assoc, hψ k, Category.assoc]
  have hr : (toScheme B S hS).map (sigmaIncl B S hS A (ε k)) ≫
      (sigmaObjIsoSpecPi B S hS ε R e).hom ≫ Spec.map (CommRingCat.ofHom
        (RingHom.pi fun k ↦ (ψ k).hom.comp (Pi.evalRingHom (fun k ↦ (R' k : Type u)) k))) =
      (e k).hom ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun k ↦ (R k : Type u)) k)) ≫
        Spec.map (CommRingCat.ofHom (RingHom.pi fun k ↦ (ψ k).hom.comp
          (Pi.evalRingHom (fun k ↦ (R' k : Type u)) k))) := by
    rw [← Category.assoc, toScheme_map_sigmaIncl_sigmaObjIsoSpecPi_hom, Category.assoc]
  rw [hl, hr, ← Spec.map_comp, ← Spec.map_comp]
  rfl

end SpecPi

end BigAffineFppf

end AlgebraicGeometry

end
