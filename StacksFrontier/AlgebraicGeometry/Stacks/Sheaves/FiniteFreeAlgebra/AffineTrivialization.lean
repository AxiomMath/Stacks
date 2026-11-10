module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Degree
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.FreeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.OfBasis
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.RelativeCover

/-!
# Trivialising a degree-`d` cover over a small enough affine open

A degree-`d` finite locally free morphism `π : Z ⟶ X` is, over a small enough affine open `V` of
`X`, the cover `AlgebraicGeometry.FiniteFreeAlgebra.cover` attached to a free `d`-dimensional
algebra structure on `Γ(V, 𝒪_V)`: the sections of `𝒪_Z` over `π⁻¹(V)` are free over `Γ(V, 𝒪_V)`
on a basis whose first vector is the unit, and the structure constants in such a basis are the
structure sought.

This is clause (b) of the proof of Stacks 05YQ: a degree-`d` cover is trivialised by a covering
family of open immersions of affine opens of the base, over each of which the cover is the one
attached to a free `d`-dimensional structure.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.exists_iso_cover_of_algEquiv`: over an affine base, a
  morphism whose sections are the algebra of a free `d`-dimensional structure *is* the cover
  attached to that structure.
* `AlgebraicGeometry.FiniteFreeAlgebra.exists_isAffineOpen_isPullback_cover`: **clause (b) of the
  proof of Stacks 05YQ.** Every point of the base of a degree-`d` finite locally free morphism
  has an affine open neighbourhood over which the morphism is the cover of a free
  `d`-dimensional structure, the identification being a cartesian square over the open immersion.

## Implementation notes

The hypothesis of `AlgebraicGeometry.FiniteFreeAlgebra.exists_iso_cover_of_algEquiv` is taken
with the base ring and the algebra *abstract*, together with ring isomorphisms onto the two rings
of sections, and its conclusion is stated for `m.map α`, the structure with scalars extended along
the isomorphism `α` onto the sections of the base.

## References

* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable {R S : Type u} [CommRing R] [CommRing S] {d : ℕ} [NeZero d]

/-! ### Extension of scalars along a ring isomorphism -/

/-- Applying a ring isomorphism to each coordinate, as an isomorphism between the algebra of a
free `d`-dimensional structure and the algebra of the structure with extended scalars. -/
noncomputable def Carrier.mapRingEquiv (α : R ≃+* S) (m : FiniteFreeAlgebra R d) :
    Carrier m ≃+* Carrier (m.map (α : R →+* S)) :=
  RingEquiv.ofBijective (Carrier.mapRingHom (α : R →+* S) m)
    ⟨fun _ _ h => Carrier.ext fun k => α.injective (congrFun h k),
     fun z => ⟨(fun k => α.symm (z k) : Carrier m),
      Carrier.ext fun k => α.apply_symm_apply (z k)⟩⟩

/-- The `k`-th coordinate of the image of `x` under `Carrier.mapRingEquiv α m` is `α` applied to
the `k`-th coordinate of `x`. -/
@[simp]
theorem Carrier.mapRingEquiv_apply (α : R ≃+* S) (m : FiniteFreeAlgebra R d) (x : Carrier m)
    (k : Fin d) : Carrier.mapRingEquiv α m x k = α (x k) := rfl

/-! ### The cover of an affine base attached to a free structure on its sections -/

/-- **Over an affine base, a morphism whose sections form the algebra of a free `d`-dimensional
structure is the cover attached to that structure.** The structure is given over an abstract ring
`R` identified with the sections of the base by `α`, and the sections of the source are
identified with its algebra by `β ∘ e⁻¹`; the cover is then formed from the structure with
scalars extended along `α`. -/
theorem exists_iso_cover_of_algEquiv {W Y : Scheme.{u}} [IsAffine W] [IsAffine Y] (g : Y ⟶ W)
    {A : Type u} [CommRing A] [Algebra R A] (m : FiniteFreeAlgebra R d)
    (e : A ≃ₐ[R] Carrier m) (α : R ≃+* ↑Γ(W, ⊤)) (β : A ≃+* ↑Γ(Y, ⊤))
    (hαβ : ∀ r : R, β (algebraMap R A r) = g.appTop.hom (α r)) :
    ∃ κ : Y ≅ (cover W (m.map (α : R →+* ↑Γ(W, ⊤)))).left,
      κ.hom ≫ (cover W (m.map (α : R →+* ↑Γ(W, ⊤)))).hom = g := by
  set φ : Carrier (m.map (α : R →+* ↑Γ(W, ⊤))) ≃+* ↑Γ(Y, ⊤) :=
    (Carrier.mapRingEquiv α m).symm.trans (e.symm.toRingEquiv.trans β) with hφdef
  have hφ : (φ : Carrier (m.map (α : R →+* ↑Γ(W, ⊤))) →+* ↑Γ(Y, ⊤)).comp
      (algebraMap ↑Γ(W, ⊤) (Carrier (m.map (α : R →+* ↑Γ(W, ⊤))))) = g.appTop.hom := by
    refine RingHom.ext fun x => ?_
    have hx : algebraMap ↑Γ(W, ⊤) (Carrier (m.map (α : R →+* ↑Γ(W, ⊤)))) x =
        Carrier.mapRingEquiv α m (algebraMap R (Carrier m) (α.symm x)) := by
      have h := RingHom.congr_fun (Carrier.mapRingHom_comp_algebraMap (α : R →+* ↑Γ(W, ⊤)) m)
        (α.symm x)
      rw [RingHom.comp_apply, RingHom.comp_apply,
        show (α : R →+* ↑Γ(W, ⊤)) (α.symm x) = x from α.apply_symm_apply x] at h
      exact h.symm
    rw [RingHom.comp_apply, hx, hφdef]
    change β (e.symm ((Carrier.mapRingEquiv α m).symm
      (Carrier.mapRingEquiv α m (algebraMap R (Carrier m) (α.symm x))))) = _
    rw [RingEquiv.symm_apply_apply, AlgEquiv.commutes, hαβ, α.apply_symm_apply]
  have hiso : IsIso (ofHom (φ : Carrier (m.map (α : R →+* ↑Γ(W, ⊤))) →+* ↑Γ(Y, ⊤))) :=
    Iso.isIso_hom φ.toCommRingCatIso
  set θ : Y ⟶ (specCover (m.map (α : R →+* ↑Γ(W, ⊤)))).left :=
    Y.toSpecΓ ≫ Spec.map (ofHom (φ : Carrier (m.map (α : R →+* ↑Γ(W, ⊤))) →+* ↑Γ(Y, ⊤)))
    with hθdef
  have hθiso : IsIso θ := by rw [hθdef]; infer_instance
  have hsq : θ ≫ (specCover (m.map (α : R →+* ↑Γ(W, ⊤)))).hom = g ≫ W.toSpecΓ := by
    rw [hθdef, Category.assoc,
      show Spec.map (ofHom (φ : Carrier (m.map (α : R →+* ↑Γ(W, ⊤))) →+* ↑Γ(Y, ⊤))) ≫
          (specCover (m.map (α : R →+* ↑Γ(W, ⊤)))).hom =
        Spec.map (ofHom g.appTop.hom) by
        rw [show (specCover (m.map (α : R →+* ↑Γ(W, ⊤)))).hom =
            Spec.map (ofHom (algebraMap ↑Γ(W, ⊤)
              (Carrier (m.map (α : R →+* ↑Γ(W, ⊤)))))) from rfl,
          ← Spec.map_comp]
        congr 1
        exact CommRingCat.hom_ext hφ]
    exact (Scheme.toSpecΓ_naturality g).symm
  have hpb : IsPullback θ g (specCover (m.map (α : R →+* ↑Γ(W, ⊤)))).hom W.toSpecΓ :=
    IsPullback.of_horiz_isIso ⟨hsq⟩
  refine ⟨hpb.isoIsPullback _ _ (isPullback_cover W (m.map (α : R →+* ↑Γ(W, ⊤)))), ?_⟩
  exact hpb.isoIsPullback_hom_snd _ _ (isPullback_cover W (m.map (α : R →+* ↑Γ(W, ⊤))))

/-! ### Clause (b) of the proof of Stacks 05YQ -/

/-- A degree-`d` finite locally free morphism with `d` positive is surjective. -/
theorem surjective_of_isFiniteLocallyFreeOfRank {X Z : Scheme.{u}} (π : Z ⟶ X)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank π d] : Surjective π := by
  have h := (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    π).mp (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree π d)
  have : IsFinite π := h.1
  have : Flat π := h.2.1
  refine π.one_le_finrank_iff_surjective.mp fun y => ?_
  have hfr : Scheme.Hom.finrank π y = d :=
    (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq π d).mp inferInstance y
  change 1 ≤ Scheme.Hom.finrank π y
  rw [hfr]
  exact Nat.pos_of_ne_zero (NeZero.ne d)

/-- The compatibility of the sections of a restriction of a morphism over an open of the target
with the sections of the morphism itself, read through
`AlgebraicGeometry.Scheme.Opens.topIso`. -/
theorem topIso_inv_app_eq {X Z : Scheme.{u}} (π : Z ⟶ X) (V : X.Opens) (r : ↑Γ(X, V)) :
    (π ⁻¹ᵁ V).topIso.inv.hom ((π.app V).hom r) =
      (π ∣_ V).appTop.hom (V.topIso.inv.hom r) := by
  have hres : (π ∣_ V).appTop = V.topIso.hom ≫ π.app V ≫ (π ⁻¹ᵁ V).topIso.inv := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict π (U := V), Scheme.Hom.appTop,
      Scheme.Hom.resLE_app_top, Scheme.Hom.appLE_eq_app]
  have hr : V.topIso.hom.hom (V.topIso.inv.hom r) = r :=
    congrArg (fun h : Γ(X, V) ⟶ Γ(X, V) => h.hom r) V.topIso.inv_hom_id
  rw [hres]
  change (π ⁻¹ᵁ V).topIso.inv.hom ((π.app V).hom r) =
    (π ⁻¹ᵁ V).topIso.inv.hom ((π.app V).hom (V.topIso.hom.hom (V.topIso.inv.hom r)))
  rw [hr]

/-- **Clause (b) of the proof of Stacks 05YQ.** Every point of the base of a degree-`d` finite
locally free morphism has an affine open neighbourhood over which the morphism is the cover
attached to a free `d`-dimensional algebra structure on the sections of that neighbourhood: the
identification is a cartesian square over the open immersion of the neighbourhood. -/
theorem exists_isAffineOpen_isPullback_cover {X Z : Scheme.{u}} (π : Z ⟶ X)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank π d] (u : X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : u ∈ V)
      (m : FiniteFreeAlgebra ↑Γ(V.toScheme, ⊤) d) (ψ : (cover V.toScheme m).left ⟶ Z),
      IsPullback ψ (cover V.toScheme m).hom π V.ι := by
  have : Stacks.Morphisms.IsFiniteLocallyFree π :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree π d
  have hsurj : Surjective π := surjective_of_isFiniteLocallyFreeOfRank (d := d) π
  obtain ⟨V, hV, huV, d', hd', b, hb⟩ :=
    exists_isAffineOpen_basis_one π u (hsurj.surj u)
  have : IsAffine V.toScheme := hV
  have : IsAffine (π ⁻¹ᵁ V).toScheme := IsAffineHom.isAffine_preimage V hV
  let : Algebra ↑Γ(X, V) ↑Γ(Z, π ⁻¹ᵁ V) := (π.app V).hom.toAlgebra
  obtain ⟨κ, hκ⟩ := exists_iso_cover_of_algEquiv (π ∣_ V) (ofBasis b hb)
    (algEquivCarrierOfBasis b hb) V.topIso.symm.commRingCatIsoToRingEquiv
    (π ⁻¹ᵁ V).topIso.symm.commRingCatIsoToRingEquiv (topIso_inv_app_eq π V)
  have hrank : d' = d := by
    have h1 : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (π ∣_ V) d' :=
      hκ ▸ Stacks.Morphisms.isFiniteLocallyFreeOfRank_precomp κ _
        (isFiniteLocallyFreeOfRank_cover _ _)
    have h2 : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (π ∣_ V) d :=
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property_iff (π ∣_ V) d).mp
        (IsZariskiLocalAtTarget.restrict
          (P := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property d)
          ((Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property_iff π d).mpr inferInstance) V)
    exact Stacks.Morphisms.IsFiniteLocallyFreeOfRank.rank_eq_of_point (π ∣_ V) ⟨u, huV⟩ h1 h2
  subst hrank
  refine ⟨V, hV, huV, _, κ.inv ≫ (π ⁻¹ᵁ V).ι, ?_⟩
  have hleft : IsPullback κ.inv
      (cover V.toScheme ((ofBasis b hb).map
        (V.topIso.symm.commRingCatIsoToRingEquiv : ↑Γ(X, V) →+* ↑Γ(V.toScheme, ⊤)))).hom
      (π ∣_ V) (𝟙 V.toScheme) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, ← hκ, Iso.inv_hom_id_assoc]⟩
  have h := hleft.paste_horiz (isPullback_morphismRestrict π V).flip
  rwa [Category.id_comp] at h

end AlgebraicGeometry.FiniteFreeAlgebra

end
