module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonOriginFibreScheme
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.BasePointChangeEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TorsorCharacterBaseChange

/-!
# The Artin–Schreier factor of Laumon's family is trivial on the fibre over the origin

Let `K = pr₁^*ℱ_{σ₁} ⊗ L_ψ'(t (xⁿ⁰ + c x))` be the family sheaf of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) on `𝔸² = Spec k'[x][t]` and `Y` a fibre of
`pr₂` over the origin `y` (`t = 0`) of the `t`-line. The kernel `g = t (xⁿ⁰ + c x)` vanishes in
`Γ(Y, 𝒪_Y)` because `t` does at `y` (`Stacks.EtaleCohomology.laumonFibre_appTop_laumonKernel`),
so the Artin–Schreier cover `T^q - T = g` acquires the section `T ↦ 0` over `Y`
(`Stacks.ArtinSchreier.exists_lift_cover_of_appTop_eq_zero`). A torsor cover with a section over
`Y` has trivial character on `π₁(Y)`
(`AlgebraicGeometry.TorsorCover.baseChange_character_eq_one_of_lift`); with the invariance of the
character under changes of base point, the Artin–Schreier character of the family composed with
`π₁(Y, ȳ) → π₁(𝔸², i(ȳ)) ≅ π₁(𝔸², z)` is trivial
(`Stacks.EtaleCohomology.artinSchreierCharacter_laumonFibre_eq_one`).

The fibre `Y` is `U ×_k κ(y) ≅ Spec κ(y)[x]` for the curve `U ≅ 𝔸¹_k`, hence connected
(`Stacks.EtaleCohomology.connectedSpace_laumonFibre`).

## Main results

* `AlgebraicGeometry.TorsorCover.baseChange_character_eq_one_of_lift`.
* `Stacks.ArtinSchreier.exists_lift_cover_of_appTop_eq_zero`.
* `Stacks.EtaleCohomology.laumonPointRingHom_X_eq_zero`,
  `Stacks.EtaleCohomology.laumonFibre_appTop_laumonKernel`.
* `Stacks.EtaleCohomology.artinSchreierCharacter_laumonFibre_eq_one`.
* `Stacks.EtaleCohomology.connectedSpace_laumonFibre`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace AlgebraicGeometry.TorsorCover

attribute [-instance] CategoryTheory.catToReflQuiver

variable {X Y : Scheme.{u}} {K : Type*} [AddCommGroup K] (T : TorsorCover X K) (f : Y ⟶ X)

/-- **A torsor cover with a lift of `f : Y ⟶ X` has trivial character after base change along
`f`**: the lift is a morphism from the trivial cover of `Y` to the base change, and `π₁(Y)` fixes
the unique point of the fibre of the trivial cover, hence its image. -/
public theorem baseChange_character_eq_one_of_lift [ConnectedSpace Y] (s : Y ⟶ T.cover.left)
    (hs : s ≫ T.cover.hom = f) (y : GeometricPoint Y)
    (p₀ : (finiteEtaleFiberFunctor y).obj (T.baseChange f).cover) (γ : EtaleFundamentalGroup Y y) :
    (T.baseChange f).character y p₀ γ = 1 := by
  let I : FiniteEtaleOver Y := MorphismProperty.Over.mk ⊤ (𝟙 Y) ⟨inferInstance, inferInstance⟩
  let σ : I ⟶ (T.baseChange f).cover :=
    MorphismProperty.Over.homMk (pullback.lift s (𝟙 Y) (hs.trans (Category.id_comp f).symm))
      (pullback.lift_snd _ _ _)
  let q : (finiteEtaleFiberFunctor y).obj I := ⟨y.hom, Category.comp_id _⟩
  have hq : ∀ q' : (finiteEtaleFiberFunctor y).obj I, q' = q := fun q' =>
    Subtype.ext ((Category.comp_id _).symm.trans q'.2)
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  refine (T.baseChange f).character_eq_of_smul y p₀ γ ((finiteEtaleFiberFunctor y).map σ q) ?_
  have hσ : γ • (finiteEtaleFiberFunctor y).map σ q =
      (finiteEtaleFiberFunctor y).map σ (γ • q) :=
    ConcreteCategory.congr_hom (γ.hom.naturality σ) q
  rw [hσ, hq (γ • q), (T.baseChange f).τ_zero, CategoryTheory.Functor.map_id]
  rfl

end AlgebraicGeometry.TorsorCover

namespace Stacks.ArtinSchreier

variable (k : Type u) [Field k] [Fintype k] {A : Type u} [CommRing A] [Algebra k A] (g : A)

/-- **A morphism `i : Y ⟶ Spec A` on whose global sections `g` vanishes lifts to the
Artin–Schreier cover `T^q - T = g`**, by `T ↦ 0`. -/
public theorem exists_lift_cover_of_appTop_eq_zero {Y : Scheme.{u}} (i : Y ⟶ Spec (.of A))
    (hg : ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ i.appTop).hom g = 0) :
    ∃ s : Y ⟶ (cover k A g).left, s ≫ (cover k A g).hom = i := by
  let iΓ := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ i.appTop
  have hp : (poly k g).eval₂ iΓ.hom 0 = 0 := by
    simp only [poly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_add, eval₂_C,
      zero_pow (Fintype.card_ne_zero (α := k)), zero_add]
    rw [show iΓ.hom g = 0 from hg, sub_zero]
  let ψ : Ring k g →+* Γ(Y, ⊤) := AdjoinRoot.lift iΓ.hom 0 hp
  refine ⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), ?_⟩
  have hψ : CommRingCat.ofHom (algebraMap A (Ring k g)) ≫ CommRingCat.ofHom ψ = iΓ := by
    ext a
    exact AdjoinRoot.lift_of hp
  show Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫
    Spec.map (CommRingCat.ofHom (algebraMap A (Ring k g))) = i
  rw [← Spec.map_comp, hψ, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

end Stacks.ArtinSchreier

namespace Stacks.EtaleCohomology

section Origin

variable (k' : Type u) [Field k'] {B : BigEtaleSite.{u}}
  {hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k')))}

/-- **`t` vanishes at the origin of the `t`-line.** -/
public theorem laumonPointRingHom_X_eq_zero
    (y : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1)
    (hy : y.asIdeal = Ideal.span {Polynomial.X}) :
    laumonPointRingHom (𝟙 _) y Polynomial.X = 0 := by
  by_contra h
  simp only [laumonPointRingHom, RingHom.comp_apply] at h
  have h2 : (B.inclusion.map (𝟙 (Stacks.ArtinSchreier.specObject (Polynomial k') B hL))) y ∈
      (Spec (CommRingCat.of (Polynomial k'))).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k'))).inv Polynomial.X) :=
    (Scheme.preimage_basicOpen
      (B.inclusion.map (𝟙 (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)))
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k'))).inv Polynomial.X)).ge
      ((Scheme.evaluation_ne_zero_iff_mem_basicOpen _ _ _ _).1 h)
  rw [basicOpen_eq_of_affine, CategoryTheory.Functor.map_id] at h2
  exact (PrimeSpectrum.mem_basicOpen _ _).1 h2 (hy ▸ Ideal.subset_span rfl)

variable {hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k'))))}

/-- **The kernel `t (xⁿ⁰ + c x)` vanishes on a fibre of `pr₂` over the origin.** -/
public theorem laumonFibre_appTop_laumonKernel (n₀ : ℕ) (c : k')
    (y : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1)
    (hy : y.asIdeal = Ideal.span {Polynomial.X}) {Y : B.Scheme}
    (i : Y ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS)
    (fY : Y.1 ⟶
      Spec (.of ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y)))
    (hY : IsPullback (B.inclusion.map i) fY (B.inclusion.map (laumonFamilyProjection k' B hS hL))
      ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.fromSpecResidueField y)) :
    ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial (Polynomial k')))).inv ≫
      (B.inclusion.map i).appTop).hom (laumonKernel k' n₀ c) = 0 := by
  have hfrom : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.fromSpecResidueField y =
      Spec.map (CommRingCat.ofHom (laumonPointRingHom (𝟙 _) y)) := by
    have h := fromSpecResidueField_comp_SpecMap_laumonPointRingHom k' y
      (𝟙 (CommRingCat.of (Polynomial k')))
    rwa [Spec.map_id, Category.comp_id, Category.id_comp] at h
  have hw : B.inclusion.map i ≫ Spec.map (CommRingCat.ofHom
      (mapRingHom (algebraMap k' (Polynomial k')))) =
      fY ≫ Spec.map (CommRingCat.ofHom (laumonPointRingHom (𝟙 _) y)) :=
    hY.w.trans (congrArg (fY ≫ ·) hfrom)
  have key : CommRingCat.ofHom (mapRingHom (algebraMap k' (Polynomial k'))) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (Polynomial (Polynomial k')))).inv ≫
        (B.inclusion.map i).appTop =
      CommRingCat.ofHom (laumonPointRingHom (𝟙 _) y) ≫
        (Scheme.ΓSpecIso (CommRingCat.of
          ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y))).inv ≫
          fY.appTop := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.ΓSpecIso_inv_naturality_assoc]
    exact congrArg (fun φ => (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k'))).inv ≫ φ.appTop) hw
  have hX : ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial (Polynomial k')))).inv ≫
      (B.inclusion.map i).appTop).hom Polynomial.X = 0 := by
    have h := congrArg (fun φ => φ.hom (Polynomial.X : Polynomial k')) key
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, coe_mapRingHom,
      map_X, laumonPointRingHom_X_eq_zero k' y hy, map_zero] using h
  rw [laumonKernel, map_mul, hX, mul_zero]

variable [Fintype k'] [ConnectedSpace (Spec (.of (Polynomial (Polynomial k'))))]

/-- **The Artin–Schreier character of Laumon's family is trivial on a fibre over the origin**:
composed with `π₁(Y, ȳ) → π₁(𝔸², i(ȳ)) ≅ π₁(𝔸², z)` (any change of base point `t`) it is `1`. -/
public theorem artinSchreierCharacter_laumonFibre_eq_one {E : Type} [CommRing E]
    (ψ' : AddChar k' E) (n₀ : ℕ) (c : k')
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (p₀ : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonKernel k' n₀ c)))
    (y : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1)
    (hy : y.asIdeal = Ideal.span {Polynomial.X}) {Y : B.Scheme} [ConnectedSpace Y.1]
    (i : Y ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS)
    (fY : Y.1 ⟶
      Spec (.of ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y)))
    (hY : IsPullback (B.inclusion.map i) fY (B.inclusion.map (laumonFamilyProjection k' B hS hL))
      ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.fromSpecResidueField y))
    (yb : GeometricPoint Y.1)
    (t : finiteEtaleFiberFunctor z ≅ finiteEtaleFiberFunctor (yb.map i.hom))
    (γ : EtaleFundamentalGroup Y.1 yb) :
    Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
      (laumonKernel k' n₀ c) ψ' z p₀
        (etaleFundamentalGroupBasePointHom t (etaleFundamentalGroupMap i.hom yb γ)) = 1 := by
  let T := Stacks.ArtinSchreier.torsorCover k' (Polynomial (Polynomial k')) (laumonKernel k' n₀ c)
  obtain ⟨s, hs⟩ := Stacks.ArtinSchreier.exists_lift_cover_of_appTop_eq_zero k'
    (laumonKernel k' n₀ c) (B.inclusion.map i)
    (laumonFibre_appTop_laumonKernel k' n₀ c y hy i fY hY)
  let q₀ : (finiteEtaleFiberFunctor (yb.map i.hom)).obj T.cover := t.hom.app T.cover p₀
  let p' := (finiteEtaleFiberProjectionEquiv i.hom yb T.cover).symm q₀
  have h1 : T.character z p₀ (etaleFundamentalGroupBasePointHom t
      (etaleFundamentalGroupMap i.hom yb γ)) =
      T.character (yb.map i.hom) q₀ (etaleFundamentalGroupMap i.hom yb γ) := by
    have h := T.character_etaleFundamentalGroupMulEquiv t p₀ q₀
      (etaleFundamentalGroupBasePointHom t (etaleFundamentalGroupMap i.hom yb γ))
    rw [etaleFundamentalGroupMulEquiv_basePointHom] at h
    exact h.symm
  have h2 : T.character (yb.map i.hom) q₀ (etaleFundamentalGroupMap i.hom yb γ) = 1 := by
    have h := T.baseChange_character i.hom yb p' γ
    rw [show finiteEtaleFiberProjection i.hom yb T.cover p' = q₀ from
      (finiteEtaleFiberProjectionEquiv i.hom yb T.cover).apply_symm_apply q₀] at h
    exact h.symm.trans (T.baseChange_character_eq_one_of_lift i.hom s hs yb p' γ)
  apply Units.ext
  rw [Stacks.ArtinSchreier.artinSchreierCharacter_apply]
  show ψ' (-Multiplicative.toAdd (T.character z p₀ _)) = 1
  rw [h1, h2, toAdd_one, neg_zero, AddChar.map_zero_eq_one]

end Origin

section Connected

variable (k : Type u) [Field k] (k' : Type u) [Field k'] [Algebra k k'] {B : BigEtaleSite.{u}}
  {hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k')))}
  {hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k'))))}

/-- **A fibre of `pr₂` over a point `y` of the `t`-line is `Spec κ(y)[x]`, hence connected**: it
is `U ×_k κ(y)` (`Stacks.EtaleCohomology.isPullback_laumonFibre_curve`) and
`𝔸¹_k ×_k κ(y) = Spec κ(y)[x]`. -/
public theorem connectedSpace_laumonFibre {U : Scheme.{u}} (f : U ⟶ Spec (.of k))
    (e : U ⟶ Spec (.of (Polynomial k))) [IsIso e]
    (he : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (y : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1) {Y : B.Scheme}
    (i : Y ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS)
    (fY : Y.1 ⟶
      Spec (.of ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y)))
    (hY : IsPullback (B.inclusion.map i) fY (B.inclusion.map (laumonFamilyProjection k' B hS hL))
      ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.fromSpecResidueField y)) :
    ConnectedSpace Y.1 := by
  let : Algebra k ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y) :=
    laumonPointAlgebra (𝟙 _) y k
  have hP1 := isPullback_laumonFibre_curve k k' f e he y i fY hY
  have t : IsPullback (inv e) (Spec.map (CommRingCat.ofHom (C : k →+* Polynomial k))) f (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [← he, IsIso.inv_hom_id_assoc, Category.comp_id, Polynomial.algebraMap_eq]⟩
  have hP2 := (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_C_mapRingHom k
    ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y))).flip.paste_horiz t
  rw [Category.comp_id] at hP2
  let φ := hP2.isoIsPullback _ _ hP1
  have : IsDomain (CommRingCat.of (Polynomial
      ((Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1.residueField y))) :=
    inferInstanceAs (IsDomain (Polynomial _))
  exact (Scheme.homeoOfIso φ).surjective.connectedSpace (Scheme.homeoOfIso φ).continuous

end Connected

end Stacks.EtaleCohomology

end
