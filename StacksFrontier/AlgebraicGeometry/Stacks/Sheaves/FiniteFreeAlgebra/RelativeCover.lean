module

public import StacksFrontier.AlgebraicGeometry.Descent.Algebra.SpecOverFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.CarrierMapPushout
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.Presheaf

/-!
# The degree-`d` cover of a scheme attached to a free algebra structure on its global sections

A free `d`-dimensional algebra structure `m` on the global sections of a scheme `T` determines a
scheme over `T`: the base change along the canonical morphism `T ⟶ Spec Γ(T, 𝒪_T)` of the
spectrum of the algebra of `m`. That morphism is finite locally free of degree `d`, and the data
of a morphism `f : T ⟶ U` of schemes, a ring map `ψ` on global sections compatible with it, and an
isomorphism of `m` with the extension of scalars of a structure `n` on `Γ(U, 𝒪_U)` produce a
morphism of covers presenting the cover of `T` as the base change along `f` of the cover of `U`.

This is the assignment `m ↦ Spec(m)` of Stacks 05YQ, over an arbitrary, not necessarily affine,
base.

## Main definitions

* `AlgebraicGeometry.FiniteFreeAlgebra.specCoverIso`: the isomorphism of spectra attached to an
  isomorphism of free `d`-dimensional structures over a ring.
* `AlgebraicGeometry.FiniteFreeAlgebra.cover`: the degree-`d` cover of `T` attached to `m`.
* `AlgebraicGeometry.FiniteFreeAlgebra.coverMap`: the morphism of covers attached to a morphism
  of schemes together with an isomorphism onto an extension of scalars.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.StructureIso.toAlgEquiv_refl` and
  `AlgebraicGeometry.FiniteFreeAlgebra.StructureIso.toAlgEquiv_comp`: the algebra isomorphism of
  an isomorphism of structures is functorial.
* `AlgebraicGeometry.FiniteFreeAlgebra.isFiniteLocallyFreeOfRank_cover`: the cover is finite
  locally free of degree `d`.
* `AlgebraicGeometry.FiniteFreeAlgebra.isPullback_coverMap`: the morphism of covers presents the
  cover of `T` as the base change along `f` of the cover of `U`.
* `AlgebraicGeometry.FiniteFreeAlgebra.coverMap_id` and
  `AlgebraicGeometry.FiniteFreeAlgebra.coverMap_comp`: the morphism of covers is functorial.

## Implementation notes

Everything is built from one cartesian square, the defining square
`AlgebraicGeometry.FiniteFreeAlgebra.isPullback_cover` of the cover, so every morphism of covers
is a lift against it and every identity between such morphisms is an application of its
uniqueness clause. The compatibility of the morphism `f` with the ring map `ψ` on global sections
is taken in the only form used, as the commuting square with the two canonical morphisms to the
spectra of the global sections; for `ψ` the map induced by `f` it is the naturality of
`AlgebraicGeometry.Scheme.toSpecΓ`.

## References

* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

attribute [local implicit_reducible] FiniteFreeAlgebra.map

variable {R S : Type u} [CommRing R] [CommRing S] {d : ℕ} [NeZero d]

/-- Extending the scalars of a free `d`-dimensional structure along the identity changes
nothing. -/
theorem map_ringHom_id (m : FiniteFreeAlgebra R d) : m.map (RingHom.id R) = m := rfl

/-! ### Functoriality of the algebra isomorphism of an isomorphism of structures -/

/-- The algebra isomorphism of the identity isomorphism of structures is the identity. -/
theorem StructureIso.toAlgEquiv_refl (m : FiniteFreeAlgebra R d) :
    (StructureIso.refl m).toAlgEquiv = AlgEquiv.refl := by
  refine AlgEquiv.ext fun x => Carrier.ext fun k => ?_
  change (∑ i, ((1 : Matrix.GeneralLinearGroup (Fin d) R) :
      Matrix (Fin d) (Fin d) R) k i * x i) = x k
  rw [Finset.sum_eq_single k (fun i _ hi => by simp [Ne.symm hi])
    (fun h => absurd (Finset.mem_univ k) h)]
  simp

/-- The algebra isomorphism of a composite of isomorphisms of structures is the composite of the
two algebra isomorphisms. -/
theorem StructureIso.toAlgEquiv_comp {m n p : FiniteFreeAlgebra R d} (e : StructureIso m n)
    (f : StructureIso n p) :
    (e.comp f).toAlgEquiv = e.toAlgEquiv.trans f.toAlgEquiv := by
  refine AlgEquiv.ext fun x => Carrier.ext fun k => ?_
  change (∑ i, ((f.matrix * e.matrix : Matrix.GeneralLinearGroup (Fin d) R) :
      Matrix (Fin d) (Fin d) R) k i * x i) =
    ∑ t, (f.matrix : Matrix (Fin d) (Fin d) R) k t *
      ∑ i, (e.matrix : Matrix (Fin d) (Fin d) R) t i * x i
  simp only [Units.val_mul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by ring

/-- Extending the scalars of an isomorphism of structures is compatible with the coordinatewise
extension of scalars of the two algebras. -/
theorem StructureIso.toAlgEquiv_map (φ : R →+* S) {m n : FiniteFreeAlgebra R d}
    (e : StructureIso m n) :
    (Carrier.mapRingHom φ n).comp (e.toAlgEquiv : Carrier m →+* Carrier n) =
      ((e.map φ).toAlgEquiv : Carrier (m.map φ) →+* Carrier (n.map φ)).comp
        (Carrier.mapRingHom φ m) :=
  RingHom.ext fun x => Carrier.ext fun k => by
    change φ (∑ i, (e.matrix : Matrix (Fin d) (Fin d) R) k i * x i) =
      ∑ i, (Matrix.GeneralLinearGroup.map φ e.matrix : Matrix (Fin d) (Fin d) S) k i * φ (x i)
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [_root_.map_mul]; rfl

/-! ### The spectrum of the algebra of a structure, functorially -/

/-- The isomorphism of spectra attached to an isomorphism of free `d`-dimensional structures over
a ring. -/
noncomputable def specCoverIso {m n : FiniteFreeAlgebra R d} (e : StructureIso m n) :
    specCover m ≅ specCover n :=
  specOverMapIso e.toAlgEquiv.symm

/-- The isomorphism of spectra `specCoverIso e` is `structureIsoEquivSpecIso m n e`. -/
theorem specCoverIso_eq_structureIsoEquivSpecIso (m n : FiniteFreeAlgebra R d)
    (e : StructureIso m n) : specCoverIso e = structureIsoEquivSpecIso m n e := rfl

/-- The underlying morphism of `specCoverIso e` is the spectrum of the inverse of the algebra
isomorphism of `e`. -/
theorem specCoverIso_hom_left {m n : FiniteFreeAlgebra R d} (e : StructureIso m n) :
    (specCoverIso e).hom.left =
      Spec.map (ofHom (e.toAlgEquiv.symm : Carrier n →+* Carrier m)) := rfl

/-- The isomorphism of spectra of the identity isomorphism of structures is the identity. -/
theorem specCoverIso_refl_hom_left (m : FiniteFreeAlgebra R d) :
    (specCoverIso (StructureIso.refl m)).hom.left = 𝟙 (specCover m).left := by
  rw [specCoverIso_hom_left, StructureIso.toAlgEquiv_refl]
  rw [show ((AlgEquiv.refl : Carrier m ≃ₐ[R] Carrier m).symm : Carrier m →+* Carrier m) =
    RingHom.id (Carrier m) from rfl]
  rw [ofHom_id, Spec.map_id]
  rfl

/-- The isomorphism of spectra of a composite of isomorphisms of structures is the composite. -/
theorem specCoverIso_comp_hom_left {m n p : FiniteFreeAlgebra R d} (e : StructureIso m n)
    (f : StructureIso n p) :
    (specCoverIso (e.comp f)).hom.left =
      (specCoverIso e).hom.left ≫ (specCoverIso f).hom.left := by
  rw [specCoverIso_hom_left, specCoverIso_hom_left, specCoverIso_hom_left,
    ← Spec.map_comp, StructureIso.toAlgEquiv_comp]
  rfl

/-- **The isomorphism of spectra attached to an isomorphism of structures commutes with the
coordinatewise extension of scalars.** -/
@[reassoc]
theorem specCoverIso_mapRingHom (φ : R →+* S) {m n : FiniteFreeAlgebra R d}
    (e : StructureIso m n) :
    (specCoverIso (e.map φ)).hom.left ≫ Spec.map (ofHom (Carrier.mapRingHom φ n)) =
      Spec.map (ofHom (Carrier.mapRingHom φ m)) ≫ (specCoverIso e).hom.left := by
  have hring : (ofHom (Carrier.mapRingHom φ n) : of (Carrier n) ⟶ of (Carrier (n.map φ))) ≫
      ofHom ((e.map φ).toAlgEquiv.symm : Carrier (n.map φ) →+* Carrier (m.map φ)) =
        ofHom (e.toAlgEquiv.symm : Carrier n →+* Carrier m) ≫
          ofHom (Carrier.mapRingHom φ m) := by
    refine CommRingCat.hom_ext (RingHom.ext fun y => ?_)
    change (e.map φ).toAlgEquiv.symm (Carrier.mapRingHom φ n y) =
      Carrier.mapRingHom φ m (e.toAlgEquiv.symm y)
    refine (e.map φ).toAlgEquiv.injective ?_
    rw [AlgEquiv.apply_symm_apply]
    have h := RingHom.congr_fun (StructureIso.toAlgEquiv_map φ e) (e.toAlgEquiv.symm y)
    rw [RingHom.comp_apply, RingHom.comp_apply] at h
    rw [show ((e.toAlgEquiv : Carrier m →+* Carrier n) (e.toAlgEquiv.symm y)) = y from
      e.toAlgEquiv.apply_symm_apply y] at h
    exact h
  rw [specCoverIso_hom_left, specCoverIso_hom_left, ← Spec.map_comp, ← Spec.map_comp, hring]

/-! ### The cover of a scheme attached to a structure on its global sections -/

/-- The degree-`d` cover of a scheme `T` attached to a free `d`-dimensional algebra structure on
its global sections: the base change along `T ⟶ Spec Γ(T, 𝒪_T)` of the spectrum of the algebra of
the structure. -/
@[implicit_reducible]
noncomputable def cover (T : Scheme.{u}) (m : FiniteFreeAlgebra Γ(T, ⊤) d) : Over T :=
  (Over.pullback T.toSpecΓ).obj (specCover m)

/-- The structure morphism of the cover is the second projection of the defining pullback. -/
theorem cover_hom (T : Scheme.{u}) (m : FiniteFreeAlgebra Γ(T, ⊤) d) :
    (cover T m).hom = pullback.snd (specCover m).hom T.toSpecΓ := rfl

/-- The projection of the cover to the spectrum of the algebra of the structure. -/
noncomputable abbrev coverProj (T : Scheme.{u}) (m : FiniteFreeAlgebra Γ(T, ⊤) d) :
    (cover T m).left ⟶ (specCover m).left :=
  pullback.fst (specCover m).hom T.toSpecΓ

/-- The defining cartesian square of the cover. -/
theorem isPullback_cover (T : Scheme.{u}) (m : FiniteFreeAlgebra Γ(T, ⊤) d) :
    IsPullback (coverProj T m) (cover T m).hom (specCover m).hom T.toSpecΓ :=
  IsPullback.of_hasPullback _ _

/-- **The cover attached to a free `d`-dimensional structure is finite locally free of
degree `d`.** -/
instance isFiniteLocallyFreeOfRank_cover (T : Scheme.{u}) (m : FiniteFreeAlgebra Γ(T, ⊤) d) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (cover T m).hom d :=
  haveI : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (specCover m).hom d :=
    isFiniteLocallyFreeOfRank_specCover m
  Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback (isPullback_cover T m)

/-! ### Morphisms of covers -/

section Map

variable {T U V : Scheme.{u}}

/-- The underlying morphism of spectra of a morphism of covers. -/
noncomputable def specMapOf {ψ : Γ(U, ⊤) →+* Γ(T, ⊤)} {m : FiniteFreeAlgebra Γ(T, ⊤) d}
    {n : FiniteFreeAlgebra Γ(U, ⊤) d} (e : StructureIso m (n.map ψ)) :
    (specCover m).left ⟶ (specCover n).left :=
  (specCoverIso e).hom.left ≫ Spec.map (ofHom (Carrier.mapRingHom ψ n))

/-- The underlying morphism of spectra of a morphism of covers is the isomorphism of spectra of
`e` followed by the spectrum of the coordinatewise extension of scalars along `ψ`. -/
theorem specMapOf_eq {ψ : Γ(U, ⊤) →+* Γ(T, ⊤)} {m : FiniteFreeAlgebra Γ(T, ⊤) d}
    {n : FiniteFreeAlgebra Γ(U, ⊤) d} (e : StructureIso m (n.map ψ)) :
    specMapOf e = (specCoverIso e).hom.left ≫ Spec.map (ofHom (Carrier.mapRingHom ψ n)) := rfl

/-- The square of spectra underlying a morphism of covers is cartesian. -/
theorem isPullback_specMapOf {ψ : Γ(U, ⊤) →+* Γ(T, ⊤)} {m : FiniteFreeAlgebra Γ(T, ⊤) d}
    {n : FiniteFreeAlgebra Γ(U, ⊤) d} (e : StructureIso m (n.map ψ)) :
    IsPullback (specMapOf e) (specCover m).hom (specCover n).hom (Spec.map (ofHom ψ)) := by
  rw [specMapOf_eq]
  have : IsIso ((specCoverIso e).hom.left) :=
    ⟨(specCoverIso e).inv.left,
      by rw [← Over.comp_left, (specCoverIso e).hom_inv_id, Over.id_left],
      by rw [← Over.comp_left, (specCoverIso e).inv_hom_id, Over.id_left]⟩
  have hiso : IsPullback ((specCoverIso e).hom.left) (specCover m).hom
      (specCover (n.map ψ)).hom (𝟙 (Spec (.of Γ(T, ⊤)))) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w (specCoverIso e).hom⟩
  have h := hiso.paste_horiz (isPullback_specCover_map ψ n)
  rwa [Category.id_comp] at h

/-- The cartesian square of a morphism of covers, read against the spectrum of the algebra of the
target structure. -/
theorem isPullback_coverComp (f : T ⟶ U) {ψ : Γ(U, ⊤) →+* Γ(T, ⊤)}
    (hψ : T.toSpecΓ ≫ Spec.map (ofHom ψ) = f ≫ U.toSpecΓ)
    {m : FiniteFreeAlgebra Γ(T, ⊤) d} {n : FiniteFreeAlgebra Γ(U, ⊤) d}
    (e : StructureIso m (n.map ψ)) :
    IsPullback (coverProj T m ≫ specMapOf e) (cover T m).hom (specCover n).hom
      (f ≫ U.toSpecΓ) := by
  have h := (isPullback_cover T m).paste_horiz (isPullback_specMapOf e)
  rwa [hψ] at h

/-- The morphism of covers attached to a morphism `f : T ⟶ U` of schemes, a ring map `ψ` on
global sections compatible with it, and an isomorphism of `m` with the extension of scalars of
`n` along `ψ`. -/
noncomputable def coverMap (f : T ⟶ U) {ψ : Γ(U, ⊤) →+* Γ(T, ⊤)}
    (hψ : T.toSpecΓ ≫ Spec.map (ofHom ψ) = f ≫ U.toSpecΓ)
    {m : FiniteFreeAlgebra Γ(T, ⊤) d} {n : FiniteFreeAlgebra Γ(U, ⊤) d}
    (e : StructureIso m (n.map ψ)) : (cover T m).left ⟶ (cover U n).left :=
  (isPullback_cover U n).lift (coverProj T m ≫ specMapOf e) ((cover T m).hom ≫ f)
    ((isPullback_coverComp f hψ e).w.trans (Category.assoc _ _ _).symm)

/-- The morphism of covers commutes with the projections to the spectra, via `specMapOf e`. -/
@[reassoc (attr := simp)]
theorem coverMap_proj (f : T ⟶ U) {ψ : Γ(U, ⊤) →+* Γ(T, ⊤)}
    (hψ : T.toSpecΓ ≫ Spec.map (ofHom ψ) = f ≫ U.toSpecΓ)
    {m : FiniteFreeAlgebra Γ(T, ⊤) d} {n : FiniteFreeAlgebra Γ(U, ⊤) d}
    (e : StructureIso m (n.map ψ)) :
    coverMap f hψ e ≫ coverProj U n = coverProj T m ≫ specMapOf e :=
  (isPullback_cover U n).lift_fst _ _ _

/-- The morphism of covers lies over `f`. -/
@[reassoc (attr := simp)]
theorem coverMap_hom (f : T ⟶ U) {ψ : Γ(U, ⊤) →+* Γ(T, ⊤)}
    (hψ : T.toSpecΓ ≫ Spec.map (ofHom ψ) = f ≫ U.toSpecΓ)
    {m : FiniteFreeAlgebra Γ(T, ⊤) d} {n : FiniteFreeAlgebra Γ(U, ⊤) d}
    (e : StructureIso m (n.map ψ)) :
    coverMap f hψ e ≫ (cover U n).hom = (cover T m).hom ≫ f :=
  (isPullback_cover U n).lift_snd _ _ _

/-- **A morphism of covers presents the cover of `T` as the base change along `f` of the cover of
`U`.** This is the degree-`d` clause of Stacks 05YQ for the morphisms of `ℋ_d`. -/
theorem isPullback_coverMap (f : T ⟶ U) {ψ : Γ(U, ⊤) →+* Γ(T, ⊤)}
    (hψ : T.toSpecΓ ≫ Spec.map (ofHom ψ) = f ≫ U.toSpecΓ)
    {m : FiniteFreeAlgebra Γ(T, ⊤) d} {n : FiniteFreeAlgebra Γ(U, ⊤) d}
    (e : StructureIso m (n.map ψ)) :
    IsPullback (coverMap f hψ e) (cover T m).hom (cover U n).hom f :=
  (isPullback_coverComp f hψ e).of_right' (isPullback_cover U n)

/-- **The morphism of covers of the identity data is the identity.** -/
theorem coverMap_id (m : FiniteFreeAlgebra Γ(T, ⊤) d)
    (hψ : T.toSpecΓ ≫ Spec.map (ofHom (RingHom.id Γ(T, ⊤))) = 𝟙 T ≫ T.toSpecΓ) :
    coverMap (𝟙 T) hψ (StructureIso.refl m) = 𝟙 (cover T m).left := by
  refine (isPullback_cover T m).hom_ext ?_ ?_
  · rw [coverMap_proj, Category.id_comp, specMapOf_eq, specCoverIso_refl_hom_left,
      Category.id_comp,
      show (Carrier.mapRingHom (RingHom.id Γ(T, ⊤)) m) = RingHom.id (Carrier m) from rfl,
      ofHom_id, Spec.map_id]
    exact Category.comp_id _
  · rw [coverMap_hom, Category.comp_id, Category.id_comp]

/-- **The morphism of covers of a composite of data is the composite.** -/
theorem coverMap_comp (g : V ⟶ T) (f : T ⟶ U) {χ : Γ(T, ⊤) →+* Γ(V, ⊤)}
    {ψ : Γ(U, ⊤) →+* Γ(T, ⊤)}
    (hχ : V.toSpecΓ ≫ Spec.map (ofHom χ) = g ≫ T.toSpecΓ)
    (hψ : T.toSpecΓ ≫ Spec.map (ofHom ψ) = f ≫ U.toSpecΓ)
    (hχψ : V.toSpecΓ ≫ Spec.map (ofHom (χ.comp ψ)) = (g ≫ f) ≫ U.toSpecΓ)
    {l : FiniteFreeAlgebra Γ(V, ⊤) d} {m : FiniteFreeAlgebra Γ(T, ⊤) d}
    {n : FiniteFreeAlgebra Γ(U, ⊤) d}
    (e₁ : StructureIso l (m.map χ)) (e₂ : StructureIso m (n.map ψ)) :
    coverMap g hχ e₁ ≫ coverMap f hψ e₂ =
      coverMap (g ≫ f) hχψ (e₁.comp (e₂.map χ)) := by
  refine (isPullback_cover U n).hom_ext ?_ ?_
  · rw [Category.assoc, coverMap_proj, coverMap_proj_assoc, coverMap_proj, specMapOf,
      specMapOf, specMapOf, specCoverIso_comp_hom_left,
      show (Carrier.mapRingHom (χ.comp ψ) n) =
          (Carrier.mapRingHom χ (n.map ψ)).comp (Carrier.mapRingHom ψ n) from rfl,
      show (ofHom ((Carrier.mapRingHom χ (n.map ψ)).comp (Carrier.mapRingHom ψ n)) :
          of (Carrier n) ⟶ of (Carrier ((n.map ψ).map χ))) =
        ofHom (Carrier.mapRingHom ψ n) ≫ ofHom (Carrier.mapRingHom χ (n.map ψ)) from rfl,
      Spec.map_comp]
    simp only [Category.assoc]
    rw [specCoverIso_mapRingHom_assoc χ e₂]
  · rw [Category.assoc, coverMap_hom, coverMap_hom_assoc, coverMap_hom]

end Map

end AlgebraicGeometry.FiniteFreeAlgebra

end
