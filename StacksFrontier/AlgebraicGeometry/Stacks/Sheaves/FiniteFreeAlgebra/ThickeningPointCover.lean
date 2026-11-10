module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.ThickeningLift
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.UniversalBaseChange

/-!
# A degree-`d` cover over a first-order thickening is a base change of the universal cover

Let `ι : T ⟶ T'` be a first-order thickening with `T'` affine, let `p' : Z' ⟶ T'` be finite
locally free of degree `d`, and suppose the base change of `p'` along `ι` is already exhibited as
a base change of the universal degree-`d` cover of **Stacks 05YM** along a point
`q : T ⟶ Spec Γ(X_d, 𝒪)`. Then `q` extends to a point `q' : T' ⟶ Spec Γ(X_d, 𝒪)` along which `p'`
itself is a base change of the universal cover, compatibly with the given one.

This is the geometric form of the formal smoothness of the atlas candidate of `ℋ_d`: the atlas
sends a point of the scheme of structure constants to the base change of the universal cover
along it, so the statement above says precisely that a first-order lifting problem for that
1-morphism has a solution.

## Main results

* `FiniteFreeAlgebra.exists_point_isPullback_universalFiniteCoverMap_of_thickening`: the
  extension, with the compatibility.

## Implementation notes

The algebra is
`AlgebraicGeometry.FiniteFreeAlgebra.exists_structure_lift_of_thickening`; everything here is the
translation between a cartesian square over the universal cover and an identification of global
sections with the algebra of a structure.

In both directions that translation is
`AlgebraicGeometry.FiniteFreeAlgebra.isPullback_universalFiniteCoverMap_point`, which exhibits
the cover of the structure a point classifies as the base change of the universal cover along
that point: comparing it with the given square produces the identification going in, and pasting
it against `Spec` of the identification found by the algebra produces the square coming out.
Morphisms into an affine scheme are compared through their maps of global sections, by
`AlgebraicGeometry.ext_of_isAffine` after cancelling the isomorphism
`AlgebraicGeometry.Scheme.ΓSpecIso`; the point of the scheme of structure constants attached to a
structure is `AlgebraicGeometry.FiniteFreeAlgebra.map_appTop_universalStructure`, which is what
lets the lifted structure be read as a point of that scheme.

No `@[stacks]` attribute is placed here. What **Stacks 05YM** asserts is the representability of
free `d`-dimensional structures, which is
`AlgebraicGeometry.FiniteFreeAlgebra.representation`; the clause of **Stacks 05YQ** that this
serves is the smoothness of `AlgebraicGeometry.Stack.finiteCoverUniversalAtlas`, a statement
about that 1-morphism.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

/-- Two morphisms into the spectrum of a ring which induce the same map of global sections are
equal. -/
private theorem hom_ext_of_spec_target {W : Scheme.{u}} {C : CommRingCat.{u}} {f g : W ⟶ Spec C}
    (h : (Scheme.ΓSpecIso C).inv ≫ f.appTop = (Scheme.ΓSpecIso C).inv ≫ g.appTop) :
    f = g :=
  ext_of_isAffine ((cancel_epi (Scheme.ΓSpecIso C).inv).mp h)

/-- The map of global sections of a morphism into an affine scheme followed by `Spec` of a ring
map. -/
private theorem ΓSpecIso_inv_comp_appTop_specMap {W : Scheme.{u}} {C A : CommRingCat.{u}}
    (h : W ⟶ Spec A) (φ : C ⟶ A) :
    (Scheme.ΓSpecIso C).inv ≫ (h ≫ Spec.map φ).appTop =
      φ ≫ (Scheme.ΓSpecIso A).inv ≫ h.appTop := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
    Category.assoc]

/-- The map of global sections of the canonical morphism of an affine scheme to the spectrum of
its global sections is the identity. -/
private theorem ΓSpecIso_inv_comp_isoSpec_hom_appTop (W : Scheme.{u}) [IsAffine W] :
    (Scheme.ΓSpecIso Γ(W, ⊤)).inv ≫ W.isoSpec.hom.appTop = 𝟙 Γ(W, ⊤) := by
  rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop, Iso.inv_hom_id]

/-- **Extending a point of the scheme of structure constants over a first-order thickening.** Let
`ι : T ⟶ T'` be a first-order thickening with `T'` affine, let `p' : Z' ⟶ T'` be finite locally
free of degree `d`, and let the base change of `p'` along `ι` be the base change of the universal
degree-`d` cover along a point `q` of the spectrum of the global sections of the scheme of
structure constants. Then there is a point `q'` over `T'` restricting to `q` along `ι` for which
`p'` itself is the base change of the universal cover, compatibly with the given cartesian
square. -/
theorem exists_point_isPullback_universalFiniteCoverMap_of_thickening (d : ℕ) [NeZero d]
    {T T' Z' Zx : Scheme.{u}} [IsAffine T'] {ι : T ⟶ T'} {p' : Z' ⟶ T'}
    (hι : Stacks.Thickenings.IsFirstOrderThickening ι)
    (hp' : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p' d)
    {px : Zx ⟶ T} {α : Zx ⟶ Z'} (hα : IsPullback α px p' ι)
    {q : T ⟶ Spec (.of Γ(FiniteFreeAlgebra.scheme.{u} d, ⊤))}
    {gx : Zx ⟶ (specCover (universalStructure.{u} d)).left}
    (hx : IsPullback gx px (specCover (universalStructure.{u} d)).hom q) :
    ∃ (q' : T' ⟶ Spec (.of Γ(FiniteFreeAlgebra.scheme.{u} d, ⊤)))
      (g' : Z' ⟶ (specCover (universalStructure.{u} d)).left),
      ι ≫ q' = q ∧
        IsPullback g' p' (specCover (universalStructure.{u} d)).hom q' ∧ α ≫ g' = gx := by
  classical
  have : IsClosedImmersion ι := hι.1
  have : IsAffine T := isAffine_of_isAffineHom ι
  have : IsAffineHom p' := hp'.toIsAffineHom
  have : IsAffine Z' := isAffine_of_isAffineHom p'
  have : IsAffineHom px :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) hα
      hp'.toIsAffineHom
  have : IsAffine Zx := isAffine_of_isAffineHom px
  let : Algebra Γ(T, ⊤) Γ(Zx, ⊤) := px.appTop.hom.toAlgebra
  let : Algebra Γ(T', ⊤) Γ(T, ⊤) := ι.appTop.hom.toAlgebra
  let : Algebra Γ(T', ⊤) Γ(Z', ⊤) := p'.appTop.hom.toAlgebra
  -- read the point `q` as a morphism to the scheme of structure constants
  obtain ⟨xpt, rfl⟩ : ∃ y : T ⟶ FiniteFreeAlgebra.scheme.{u} d,
      y ≫ (FiniteFreeAlgebra.scheme.{u} d).isoSpec.hom = q :=
    ⟨q ≫ (FiniteFreeAlgebra.scheme.{u} d).isoSpec.inv, by
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩
  -- the cover of a structure is the base change of the universal cover along its point
  have hup : ∀ {S : Scheme.{u}} [IsAffine S] (y : S ⟶ FiniteFreeAlgebra.scheme.{u} d),
      IsPullback
        (Spec.map (ofHom (Carrier.mapRingHom y.appTop.hom (universalStructure.{u} d))))
        ((specCover (map y.appTop.hom (universalStructure.{u} d))).hom ≫ S.isoSpec.inv)
        (specCover (universalStructure.{u} d)).hom
        (y ≫ (FiniteFreeAlgebra.scheme.{u} d).isoSpec.hom) := fun y => by
    have h := isPullback_universalFiniteCoverMap_point d _ y
    rwa [Scheme.isoSpec_hom_naturality y] at h
  -- compare the two cartesian squares over the same cospan
  let κ := hx.isoIsPullback _ _ (hup xpt)
  have hκ1 : κ.hom ≫
      Spec.map (ofHom (Carrier.mapRingHom xpt.appTop.hom (universalStructure.{u} d))) = gx :=
    IsPullback.isoIsPullback_hom_fst _ _ hx (hup xpt)
  have hκ2 : κ.hom ≫ ((specCover (map xpt.appTop.hom (universalStructure.{u} d))).hom ≫
      T.isoSpec.inv) = px :=
    IsPullback.isoIsPullback_hom_snd _ _ hx (hup xpt)
  have hκ2' : κ.hom ≫ Spec.map (ofHom (algebraMap Γ(T, ⊤)
      (Carrier (map xpt.appTop.hom (universalStructure.{u} d))))) = px ≫ T.isoSpec.hom := by
    rw [← hκ2]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  -- the identification of the global sections of `Zx` with the algebra of the structure
  have : IsIso (Scheme.Hom.appTop κ.hom) := by
    have : IsIso κ.hom := Iso.isIso_hom κ
    change IsIso (Scheme.Γ.map κ.hom.op)
    infer_instance
  let σ : CommRingCat.of (Carrier (map xpt.appTop.hom (universalStructure.{u} d))) ⟶ Γ(Zx, ⊤) :=
    (Scheme.ΓSpecIso _).inv ≫ κ.hom.appTop
  have : IsIso σ := by
    dsimp only [σ]
    infer_instance
  have hσalg : ofHom (algebraMap Γ(T, ⊤)
      (Carrier (map xpt.appTop.hom (universalStructure.{u} d)))) ≫ σ = px.appTop := by
    have h1 := ΓSpecIso_inv_comp_appTop_specMap
      (A := CommRingCat.of (Carrier (map xpt.appTop.hom (universalStructure.{u} d))))
      (C := Γ(T, ⊤)) κ.hom (ofHom (algebraMap Γ(T, ⊤)
        (Carrier (map xpt.appTop.hom (universalStructure.{u} d)))))
    rw [hκ2', Scheme.Hom.comp_appTop, ← Category.assoc,
      ΓSpecIso_inv_comp_isoSpec_hom_appTop, Category.id_comp] at h1
    exact h1.symm
  let ρ : Carrier (map xpt.appTop.hom (universalStructure.{u} d)) ≃+* Γ(Zx, ⊤) :=
    (asIso σ).commRingCatIsoToRingEquiv
  let eA : Γ(Zx, ⊤) ≃ₐ[Γ(T, ⊤)]
      Carrier (map xpt.appTop.hom (universalStructure.{u} d)) :=
    AlgEquiv.ofRingEquiv (f := ρ.symm) (by
      intro r
      refine ρ.injective ?_
      rw [ρ.apply_symm_apply]
      exact (congrArg (fun k : Γ(T, ⊤) ⟶ Γ(Zx, ⊤) => k.hom r) hσalg).symm)
  have heAsymm : ∀ v, eA.symm v = σ.hom v := fun _ => rfl
  -- lift the structure along the thickening
  obtain ⟨m', eA', hmap, hcomp⟩ :=
    exists_structure_lift_of_thickening d hι hp' hα
      (map xpt.appTop.hom (universalStructure.{u} d)) eA
  -- read the lifted structure as a point of the scheme of structure constants
  obtain ⟨xpt', hxpt'⟩ : ∃ y : T' ⟶ FiniteFreeAlgebra.scheme.{u} d,
      map y.appTop.hom (universalStructure.{u} d) = m' :=
    ⟨((representation.{u} d).equiv T').symm m', map_appTop_universalStructure d T' m'⟩
  subst hxpt'
  have hιxpt : ι ≫ xpt' = xpt := by
    refine ((representation.{u} d).equiv T).injective ?_
    rw [← (representation.{u} d).naturality ι xpt', ← map_universalStructure d xpt',
      ← map_universalStructure d xpt]
    exact hmap
  -- the identification of the global sections of `Z'` with the algebra of the lifted structure
  let ρ' : Carrier (map xpt'.appTop.hom (universalStructure.{u} d)) ≃+* Γ(Z', ⊤) :=
    eA'.symm.toRingEquiv
  let ζ : Z' ≅ Spec (.of (Carrier (map xpt'.appTop.hom (universalStructure.{u} d)))) :=
    Z'.isoSpec ≪≫ specIsoOfRingEquiv ρ'
  have hζsec : (Scheme.ΓSpecIso
        (.of (Carrier (map xpt'.appTop.hom (universalStructure.{u} d))))).inv ≫ ζ.hom.appTop =
      ofHom ρ'.toRingHom := by
    have h1 : (Scheme.ΓSpecIso
          (.of (Carrier (map xpt'.appTop.hom (universalStructure.{u} d))))).inv ≫
          ζ.hom.appTop =
        ofHom ρ'.toRingHom ≫ (Scheme.ΓSpecIso Γ(Z', ⊤)).inv ≫ Z'.isoSpec.hom.appTop :=
      ΓSpecIso_inv_comp_appTop_specMap (A := Γ(Z', ⊤)) Z'.isoSpec.hom (ofHom ρ'.toRingHom)
    rw [h1, ΓSpecIso_inv_comp_isoSpec_hom_appTop]
    exact Category.comp_id _
  have hζsecα : (Scheme.ΓSpecIso
        (.of (Carrier (map xpt'.appTop.hom (universalStructure.{u} d))))).inv ≫
      ζ.hom.appTop ≫ α.appTop = ofHom ρ'.toRingHom ≫ α.appTop := by
    rw [← Category.assoc, hζsec]
  have hmul : ofHom (algebraMap Γ(T', ⊤)
        (Carrier (map xpt'.appTop.hom (universalStructure.{u} d)))) ≫ ofHom ρ'.toRingHom =
      p'.appTop := by
    ext r
    exact eA'.symm.commutes r
  have hζbase : ζ.hom ≫
      (specCover (map xpt'.appTop.hom (universalStructure.{u} d))).hom =
      p' ≫ T'.isoSpec.hom := by
    change (Z'.isoSpec.hom ≫ Spec.map (ofHom ρ'.toRingHom)) ≫
      Spec.map (ofHom (algebraMap Γ(T', ⊤)
        (Carrier (map xpt'.appTop.hom (universalStructure.{u} d))))) = _
    rw [Category.assoc, ← Spec.map_comp, hmul, Scheme.isoSpec_hom_naturality]
  have hζover : ζ.hom ≫
      ((specCover (map xpt'.appTop.hom (universalStructure.{u} d))).hom ≫ T'.isoSpec.inv) =
      p' := by
    rw [← Category.assoc, hζbase, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : IsIso ζ.hom := Iso.isIso_hom ζ
  have hisoSq : IsPullback ζ.hom p'
      ((specCover (map xpt'.appTop.hom (universalStructure.{u} d))).hom ≫ T'.isoSpec.inv)
      (𝟙 T') :=
    IsPullback.of_horiz_isIso ⟨by rw [hζover, Category.comp_id]⟩
  have hpaste := hisoSq.paste_horiz (hup xpt')
  rw [Category.id_comp] at hpaste
  refine ⟨xpt' ≫ (FiniteFreeAlgebra.scheme.{u} d).isoSpec.hom, _, ?_, hpaste, ?_⟩
  · rw [← Category.assoc, hιxpt]
  · refine hom_ext_of_spec_target ?_
    rw [← hκ1, ← Category.assoc α ζ.hom _, ΓSpecIso_inv_comp_appTop_specMap,
      ΓSpecIso_inv_comp_appTop_specMap, Scheme.Hom.comp_appTop, hζsecα]
    ext v
    refine eA.injective ?_
    change eA (α.appTop.hom (ρ' (Carrier.mapRingHom xpt'.appTop.hom
      (universalStructure.{u} d) v))) =
      eA (σ.hom (Carrier.mapRingHom xpt.appTop.hom (universalStructure.{u} d) v))
    rw [← heAsymm, eA.apply_symm_apply]
    refine Carrier.ext fun k => ?_
    rw [← hcomp]
    change ι.appTop.hom (eA' (eA'.symm (Carrier.mapRingHom xpt'.appTop.hom
      (universalStructure.{u} d) v)) k) = _
    rw [eA'.apply_symm_apply, Carrier.mapRingHom_apply, Carrier.mapRingHom_apply, ← hιxpt,
      Scheme.Hom.comp_appTop]
    rfl

end AlgebraicGeometry.FiniteFreeAlgebra

end
