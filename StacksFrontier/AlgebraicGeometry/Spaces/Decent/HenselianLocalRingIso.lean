module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence

/-!
# The henselian local ring along an isomorphism

Let `e : X ≅ X'` be an isomorphism of decent algebraic spaces over a scheme `S`, let `x` be a
point of `X` and let `x'` be its image in `|X'|`. Composing with `e` carries an elementary étale
neighborhood `(U, u) → X` of `x` to the elementary étale neighborhood `(U, u) → X'` of `x'`,
with the same scheme and the same distinguished point, and composing with `e⁻¹` undoes it. The
henselian local ring of Stacks 0BGW is the colimit of the rings of global sections of the
elementary étale neighborhoods, and the global sections do not change, so `e` induces an
isomorphism

`𝒪^h_{X, x} ≅ 𝒪^h_{X', x'}`

matching the canonical images of the sections of `U` on both sides.

## Main definitions

* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.mapIso`: an elementary étale neighborhood
  composed with an isomorphism.
* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.mapIsoHom`: a morphism of elementary étale
  neighborhoods as a morphism of the composed neighborhoods.
* `AlgebraicGeometry.Space.henselianLocalRingHomOfIso`: the ring homomorphism of henselian local
  rings induced by an isomorphism of algebraic spaces.
* `AlgebraicGeometry.Space.henselianLocalRingEquivOfIso`: the isomorphism of henselian local
  rings induced by an isomorphism of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.henselianLocalRingEquivOfIso_sectionHom`: the isomorphism carries the
  image of a section of an elementary étale neighborhood to the image of the same section of the
  composed neighborhood.

## References

* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
* [Stacks Project, Tag 0BGW](https://stacks.math.columbia.edu/tag/0BGW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
    {hX' : IsAlgebraicSpace B S hS X'}

namespace ElementaryEtaleNeighborhood

/-- An elementary étale neighborhood of `x` composed with an isomorphism `e : X ≅ X'`: the same
scheme and distinguished point, with the étale map to `X'` the composite with `e`. -/
@[simps]
abbrev mapIso (e : X ≅ X') {x : points B S hS X} {x' : points B S hS X'}
    (hx : pointsMap B S hS X e.hom x = x') (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    ElementaryEtaleNeighborhood B S hS X' hX' x' where
  scheme := U.scheme
  point := U.point
  residueField_contained := U.residueField_contained
  toSpace := U.toSpace ≫ e.hom
  etale_toSpace := isEtale_comp B S hS U.etale_toSpace (isEtale_of_isIso B S hS e.hom)
  map_point := by rw [pointsMap_comp, Function.comp_apply, U.map_point, hx]
  mono_residueField := by
    rw [← Category.assoc]
    have := U.mono_residueField
    exact mono_comp _ _

/-- A morphism of elementary étale neighborhoods is a morphism of the composed neighborhoods. -/
@[simps]
def mapIsoHom (e : X ≅ X') {x : points B S hS X} {x' : points B S hS X'}
    (hx : pointsMap B S hS X e.hom x = x') {U V : ElementaryEtaleNeighborhood B S hS X hX x}
    (f : U ⟶ V) : mapIso (hX' := hX') e hx U ⟶ mapIso (hX' := hX') e hx V where
  hom := f.hom
  over := by
    change yoneda.map f.hom ≫ V.toSpace ≫ e.hom = U.toSpace ≫ e.hom
    rw [← Category.assoc, f.over]
  map_point := f.map_point

/-- Composing with `e` and then with `e⁻¹` gives back the neighborhood. -/
theorem mapIso_mapIso_symm (e : X ≅ X') {x : points B S hS X} {x' : points B S hS X'}
    (hx : pointsMap B S hS X e.hom x = x') (hx' : pointsMap B S hS X' e.inv x' = x)
    (U : ElementaryEtaleNeighborhood B S hS X hX x) :
    mapIso (hX' := hX) e.symm hx' (mapIso (hX' := hX') e hx U) = U := by
  cases U
  simp only [mapIso, Iso.symm_hom, Category.assoc, e.hom_inv_id, Category.comp_id]

end ElementaryEtaleNeighborhood

variable (hdec : IsDecentSpace B S hS X) (hdec' : IsDecentSpace B S hS X') (e : X ≅ X')
    {x : points B S hS X} {x' : points B S hS X'}

/-- The ring homomorphism `𝒪^h_{X, x} → 𝒪^h_{X', x'}` induced by an isomorphism `e : X ≅ X'`
sending `x` to `x'`. -/
def henselianLocalRingHomOfIso (hx : pointsMap B S hS X e.hom x = x') :
    henselianLocalRing B S hS X hX x hdec →+* henselianLocalRing B S hS X' hX' x' hdec' :=
  (existsUnique_lift B S hS X hX x hdec (henselianLocalRing B S hS X' hX' x' hdec')
    (fun U => sectionHom B S hS X' hX' x' hdec'
      (op (ElementaryEtaleNeighborhood.mapIso e hx U.unop)))
    (fun f s => sectionHom_naturality B S hS X' hX' x' hdec'
      (ElementaryEtaleNeighborhood.mapIsoHom e hx f.unop).op s)).exists.choose

/-- The homomorphism induced by an isomorphism carries the image of a section of an elementary
étale neighborhood to the image of the same section of the composed neighborhood. -/
theorem henselianLocalRingHomOfIso_sectionHom (hx : pointsMap B S hS X e.hom x = x')
    (U : (ElementaryEtaleNeighborhood B S hS X hX x)ᵒᵖ)
    (s : (globalSections B S hS X hX x).obj U) :
    henselianLocalRingHomOfIso hdec hdec' e hx (sectionHom B S hS X hX x hdec U s) =
      sectionHom B S hS X' hX' x' hdec' (op (ElementaryEtaleNeighborhood.mapIso e hx U.unop))
        s := by
  refine Exists.choose_spec (p := fun φ : _ →+* henselianLocalRing B S hS X' hX' x' hdec' =>
    ∀ U s, φ (sectionHom B S hS X hX x hdec U s) = _) ?_ U s

/-- A ring endomorphism of the henselian local ring fixing the image of every section is the
identity. -/
theorem henselianLocalRing_ringHom_ext_id
    (ψ : henselianLocalRing B S hS X hX x hdec →+* henselianLocalRing B S hS X hX x hdec)
    (hψ : ∀ U s, ψ (sectionHom B S hS X hX x hdec U s) = sectionHom B S hS X hX x hdec U s) :
    ψ = RingHom.id _ :=
  (existsUnique_lift B S hS X hX x hdec (henselianLocalRing B S hS X hX x hdec)
    (sectionHom B S hS X hX x hdec)
    (fun f s => sectionHom_naturality B S hS X hX x hdec f s)).unique hψ fun _ _ => rfl

/-- Composing with `e⁻¹` and then with `e` is the identity on the henselian local ring. -/
theorem henselianLocalRingHomOfIso_comp_symm (hx : pointsMap B S hS X e.hom x = x')
    (hx' : pointsMap B S hS X' e.inv x' = x) :
    (henselianLocalRingHomOfIso hdec hdec' e hx).comp
        (henselianLocalRingHomOfIso (hX := hX') (hX' := hX) hdec' hdec e.symm hx') =
      RingHom.id _ := by
  refine henselianLocalRing_ringHom_ext_id (hX := hX') hdec' _ fun U s => ?_
  rw [RingHom.comp_apply,
    henselianLocalRingHomOfIso_sectionHom (hX := hX') (hX' := hX) hdec' hdec e.symm hx' U s]
  let g : U.unop ⟶ ElementaryEtaleNeighborhood.mapIso (hX' := hX') e hx
      (ElementaryEtaleNeighborhood.mapIso (hX' := hX) e.symm hx' U.unop) :=
    { hom := 𝟙 _
      over := by
        show yoneda.map (𝟙 U.unop.scheme) ≫ U.unop.toSpace ≫ e.inv ≫ e.hom = U.unop.toSpace
        simp
      map_point := rfl }
  have h₁ := henselianLocalRingHomOfIso_sectionHom (hX' := hX') hdec hdec' e hx
    (op (ElementaryEtaleNeighborhood.mapIso (hX' := hX) e.symm hx' U.unop)) s
  have h₂ := sectionHom_naturality B S hS X' hX' x' hdec' g.op s
  refine h₁.trans (h₂.symm.trans ?_)
  congr 1

/-- An isomorphism `e : X ≅ X'` of decent algebraic spaces over `S` induces an isomorphism
`𝒪^h_{X, x} ≅ 𝒪^h_{X', x'}` of the henselian local rings at a point `x` and its image `x'`. -/
def henselianLocalRingEquivOfIso (hx : pointsMap B S hS X e.hom x = x') :
    henselianLocalRing B S hS X hX x hdec ≃+* henselianLocalRing B S hS X' hX' x' hdec' :=
  have hx' : pointsMap B S hS X' e.inv x' = x := by
    rw [← hx, ← Function.comp_apply (f := pointsMap B S hS X' e.inv), ← pointsMap_comp,
      e.hom_inv_id, pointsMap_id, id]
  RingEquiv.ofRingHom (henselianLocalRingHomOfIso hdec hdec' e hx)
    (henselianLocalRingHomOfIso (hX := hX') (hX' := hX) hdec' hdec e.symm hx')
    (henselianLocalRingHomOfIso_comp_symm hdec hdec' e hx hx')
    (by simpa using
      henselianLocalRingHomOfIso_comp_symm (hX := hX') (hX' := hX) hdec' hdec e.symm hx' hx)

/-- The isomorphism of henselian local rings induced by an isomorphism carries the image of a
section of an elementary étale neighborhood to the image of the same section of the composed
neighborhood. -/
theorem henselianLocalRingEquivOfIso_sectionHom (hx : pointsMap B S hS X e.hom x = x')
    (U : (ElementaryEtaleNeighborhood B S hS X hX x)ᵒᵖ)
    (s : (globalSections B S hS X hX x).obj U) :
    henselianLocalRingEquivOfIso hdec hdec' e hx (sectionHom B S hS X hX x hdec U s) =
      sectionHom B S hS X' hX' x' hdec' (op (ElementaryEtaleNeighborhood.mapIso e hx U.unop))
        s :=
  henselianLocalRingHomOfIso_sectionHom hdec hdec' e hx U s

end AlgebraicGeometry.Space

end
