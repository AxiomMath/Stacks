module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhoodBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhoodPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleLocalRingStrictHenselization
public import StacksFrontier.AlgebraicGeometry.Spaces.HenselianCompletionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# Elementary étale neighborhoods along a morphism of spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, let `x` be a point of `X` with image
`y`, let `(V, v)` be an elementary étale neighborhood of `y` and let `(U, u)` be an elementary
étale neighborhood of a point `x'` of `V ×_Y X` lying over `v` and over `x`. Then `(U, u)` sits
over `(V, v)`: the chart of `U` maps to the chart of `V` by a morphism of schemes over `f`
carrying `u` to `v`.

## Main definitions

* `AlgebraicGeometry.Space.neighborhoodOver` is the morphism of chart schemes, and
  `AlgebraicGeometry.Space.neighborhoodToSource` the étale chart of `X` the upper neighborhood
  determines.

## Main results

* `AlgebraicGeometry.Space.yoneda_map_neighborhoodOver_comp`: the square of the two charts over
  `f` commutes.
* `AlgebraicGeometry.Space.neighborhoodOver_point`: the morphism of chart schemes carries the
  distinguished point of the upper neighborhood to that of the lower one.
* `AlgebraicGeometry.Space.exists_henselianLocalRingMap_of_neighborhood`: a pointed morphism of
  elementary étale neighborhoods over two decent spaces induces a local homomorphism of their
  henselian local rings, over the map of neighborhood stalks.

## Implementation notes

The morphism of chart schemes is read off from the composite of the structure morphism of `U`
with the projection of the fibre product to `V`, which is a morphism between representable
presheaves and hence the image of a unique morphism of the site. That it carries `u` to `v` is
the same statement on points of the represented presheaves, where the distinguished points are
the residue-field points of `u` and `v`, transported by the comparison of the point set of a
representable presheaf with that of its scheme.

The homomorphism of henselian local rings is the one the universal property of the henselization
supplies: `𝒪^h_{Y, y}` is a henselization of `𝒪_{W, w}` by Stacks 0EMY, and `𝒪^h_{X, x}` is a
henselian local ring receiving `𝒪_{W, w}` through the map of stalks along `j`, so Stacks 04GS
gives a unique local map over `𝒪_{W, w}`. This is the square of henselian local rings of the
remark; the square of étale local rings above it, and the morphisms out of the spectra of the
henselian and étale local rings down to the spaces, are not constructed here — those rings live
one universe up, so their spectra are not objects of the ambient site.

## References

* [Stacks Project, Tag 04GS](https://stacks.math.columbia.edu/tag/04GS)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 0EPL](https://stacks.math.columbia.edu/tag/0EPL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_ElementaryEtaleNeighborhoodDiagram
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_ElementaryEtaleNeighborhoodDiagram
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_ElementaryEtaleNeighborhoodDiagram B S hS).has_limit _

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {x : points B S hS X.1}
  (V : ElementaryEtaleNeighborhood B S hS Y.1 Y.property
    (pointsMap B S hS X.1 f.hom x))
  {x' : points B S hS (pullback V.toSpace f.hom)}
  (U : ElementaryEtaleNeighborhood B S hS (pullback V.toSpace f.hom)
    (isAlgebraicSpace_pullback B S hS V.toSpace f.hom
      (isAlgebraicSpace_yoneda B S hS V.scheme) X.property Y.property) x')

/-- The morphism of chart schemes from an elementary étale neighborhood of a point of `V ×_Y X`
to the chart of `V`. -/
def neighborhoodOver : U.scheme ⟶ V.scheme :=
  yoneda.preimage (U.toSpace ≫ pullback.fst V.toSpace f.hom)

/-- The étale chart of the source determined by an elementary étale neighborhood of a point of
`V ×_Y X`. -/
def neighborhoodToSource : yoneda.obj U.scheme ⟶ X.1 :=
  U.toSpace ≫ pullback.snd V.toSpace f.hom

theorem yoneda_map_neighborhoodOver :
    yoneda.map (neighborhoodOver B S hS f V U) =
      U.toSpace ≫ pullback.fst V.toSpace f.hom :=
  yoneda.map_preimage _

/-- **Stacks 0EPL.** The two charts form a commutative square over `f`: the chart of the upper
elementary étale neighborhood maps to the chart of the lower one compatibly with `f`. -/
@[stacks 0EPL "the square of charts over f"]
theorem yoneda_map_neighborhoodOver_comp :
    yoneda.map (neighborhoodOver B S hS f V U) ≫ V.toSpace =
      neighborhoodToSource B S hS f V U ≫ f.hom := by
  rw [yoneda_map_neighborhoodOver, neighborhoodToSource, Category.assoc, Category.assoc]
  exact congrArg (U.toSpace ≫ ·) pullback.condition

/-- **Stacks 0EPL.** The morphism of chart schemes carries the distinguished point of the upper
elementary étale neighborhood to that of the lower one. -/
@[stacks 0EPL "the morphism of charts is pointed"]
theorem neighborhoodOver_point
    (hx' : pointsMap B S hS (pullback V.toSpace f.hom) (pullback.fst V.toSpace f.hom) x' =
      presheafPoint B S hS V.scheme V.point V.residueField_contained) :
    (BigFppfOver.toScheme B S hS).map (neighborhoodOver B S hS f V U) U.point = V.point := by
  have h₁ : pointsMap B S hS (yoneda.obj U.scheme)
      (yoneda.map (neighborhoodOver B S hS f V U))
      (presheafPoint B S hS U.scheme U.point U.residueField_contained) =
      presheafPoint B S hS V.scheme V.point V.residueField_contained := by
    rw [yoneda_map_neighborhoodOver, pointsMap_comp, Function.comp_apply, U.map_point, hx']
  have h₂ := pointsToScheme_pointsMap_yoneda B S hS (neighborhoodOver B S hS f V U)
    (presheafPoint B S hS U.scheme U.point U.residueField_contained)
  rw [h₁, pointsToScheme_presheafPoint, pointsToScheme_presheafPoint] at h₂
  exact h₂.symm

/-! ### The upper neighborhood as a neighborhood of the source -/

section Mono

variable {T A Z W R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A monomorphism into a fibre product whose first projection factors through a monomorphism
into the base has a monomorphic second projection: the factorization exhibits it as a
monomorphism into the base change of that monomorphism, whose projection is monic. -/
theorem mono_comp_pullback_snd (α : A ⟶ Z) (β : W ⟶ Z) (r : R ⟶ A) (m : R ⟶ Z)
    (hm : r ≫ α = m) [Mono m] (a : T ⟶ pullback α β) [Mono a] (c : T ⟶ R)
    (hc : c ≫ r = a ≫ pullback.fst α β) :
    Mono (a ≫ pullback.snd α β) := by
  have hcomm : c ≫ m = (a ≫ pullback.snd α β) ≫ β := by
    rw [← hm, ← Category.assoc, hc, Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨g, hgfst, hgsnd⟩ :
      ∃ g : pullback m β ⟶ pullback α β,
        g ≫ pullback.fst α β = pullback.fst m β ≫ r ∧
          g ≫ pullback.snd α β = pullback.snd m β :=
    ⟨pullback.lift _ _ (by rw [Category.assoc, hm]; exact pullback.condition),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨a', ha'fst, ha'snd⟩ :
      ∃ a' : T ⟶ pullback m β,
        a' ≫ pullback.fst m β = c ∧
          a' ≫ pullback.snd m β = a ≫ pullback.snd α β :=
    ⟨pullback.lift c (a ≫ pullback.snd α β) hcomm,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hfac : a' ≫ g = a := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hgfst, ← Category.assoc, ha'fst, hc]
    · rw [Category.assoc, hgsnd, ha'snd]
  have : Mono a' := by
    have : Mono (a' ≫ g) := by rw [hfac]; infer_instance
    exact mono_of_mono a' g
  have : Mono (pullback.snd m β) := (IsPullback.of_hasPullback m β).mono_snd_of_mono
  rw [← ha'snd]
  infer_instance

end Mono

/-- **Stacks 0EPL.** An elementary étale neighborhood of a point `x'` of `V ×_Y X` lying over
the distinguished point of `V` and over `x` is an elementary étale neighborhood of `x` in `X`.

This is what makes the identifications of the remark available at `(U, u)`: Stacks 0EMY and
Properties of Spaces, Lemma 04KF both ask for an elementary étale neighborhood of the point of
the space whose local rings are being computed. -/
@[stacks 0EPL "the upper neighborhood is one of the source"]
def neighborhoodOverSource
    (hfst : pointsMap B S hS (pullback V.toSpace f.hom) (pullback.fst V.toSpace f.hom) x' =
      presheafPoint B S hS V.scheme V.point V.residueField_contained)
    (hsnd : pointsMap B S hS (pullback V.toSpace f.hom) (pullback.snd V.toSpace f.hom) x' = x) :
    ElementaryEtaleNeighborhood B S hS X.1 X.property x where
  scheme := U.scheme
  point := U.point
  residueField_contained := U.residueField_contained
  toSpace := neighborhoodToSource B S hS f V U
  etale_toSpace :=
    isEtale_comp B S hS U.etale_toSpace
      (isEtale_pullback_snd B S hS X.property Y.property
        (isAlgebraicSpace_yoneda B S hS V.scheme) V.toSpace f.hom V.etale_toSpace)
  map_point := by
    change pointsMap B S hS (pullback V.toSpace f.hom) (pullback.snd V.toSpace f.hom)
        (pointsMap B S hS (yoneda.obj U.scheme) U.toSpace
          (presheafPoint B S hS U.scheme U.point U.residueField_contained)) = x
    rw [U.map_point, hsnd]
  mono_residueField := by
    classical
    have hamono : Mono (yoneda.map
        (residueFieldMap B S hS U.scheme U.point U.residueField_contained) ≫ U.toSpace) :=
      U.mono_residueField
    have hmmono : Mono (yoneda.map
        (residueFieldMap B S hS V.scheme V.point V.residueField_contained) ≫ V.toSpace) :=
      V.mono_residueField
    -- The residue-field point of `u`, pushed to the chart of `V`, has the same class as the
    -- residue-field point of `v`, which is monic there; so it factors through it.
    obtain ⟨c, hc⟩ : ∃ c : residueFieldObject B S hS U.scheme U.point
          U.residueField_contained ⟶
        residueFieldObject B S hS V.scheme V.point V.residueField_contained,
        yoneda.map c ≫
            yoneda.map (residueFieldMap B S hS V.scheme V.point V.residueField_contained) =
          (yoneda.map (residueFieldMap B S hS U.scheme U.point U.residueField_contained) ≫
            U.toSpace) ≫ pullback.fst V.toSpace f.hom := by
      set qu : FieldValuedPoint B S hS (pullback V.toSpace f.hom) :=
        neighborhoodFieldPoint B S hS (pullback V.toSpace f.hom)
          (isAlgebraicSpace_pullback B S hS V.toSpace f.hom
            (isAlgebraicSpace_yoneda B S hS V.scheme) X.property Y.property) x' U with hqu
      set q0 : FieldValuedPoint B S hS (yoneda.obj V.scheme) :=
        { carrier := V.scheme.left.1.residueField V.point
          contained := V.residueField_contained
          toBase := V.scheme.left.1.fromSpecResidueField V.point ≫ V.scheme.hom.1
          value := residueFieldMap B S hS V.scheme V.point V.residueField_contained } with hq0
      set quV : FieldValuedPoint B S hS (yoneda.obj V.scheme) :=
        FieldValuedPoint.map B S hS (pullback V.toSpace f.hom)
          (pullback.fst V.toSpace f.hom) qu with hquV
      have hq0mor : fieldMorphism B S hS (yoneda.obj V.scheme) q0 =
          yoneda.map (residueFieldMap B S hS V.scheme V.point V.residueField_contained) :=
        fieldMorphism_yoneda B S hS q0
      have hqumor : fieldMorphism B S hS (pullback V.toSpace f.hom) qu =
          yoneda.map (residueFieldMap B S hS U.scheme U.point U.residueField_contained) ≫
            U.toSpace :=
        neighborhoodFieldPoint_morphism B S hS (pullback V.toSpace f.hom) _ x' U
      have hquVmor : fieldMorphism B S hS (yoneda.obj V.scheme) quV =
          (yoneda.map (residueFieldMap B S hS U.scheme U.point U.residueField_contained) ≫
            U.toSpace) ≫ pullback.fst V.toSpace f.hom :=
        (fieldMorphism_map B S hS (pullback V.toSpace f.hom)
          (pullback.fst V.toSpace f.hom) qu).trans
          (congrArg (· ≫ pullback.fst V.toSpace f.hom) hqumor)
      have hclass : q0.class B S hS (yoneda.obj V.scheme) =
          quV.class B S hS (yoneda.obj V.scheme) := by
        have h1 : quV.class B S hS (yoneda.obj V.scheme) =
            pointsMap B S hS (pullback V.toSpace f.hom) (pullback.fst V.toSpace f.hom)
              (qu.class B S hS (pullback V.toSpace f.hom)) := rfl
        rw [h1, neighborhoodFieldPoint_class, hfst]
        rfl
      have : Mono (yonedaEquiv.symm q0.value) := by
        rw [show yonedaEquiv.symm q0.value =
            yoneda.map (residueFieldMap B S hS V.scheme V.point V.residueField_contained) from
          hq0mor]
        exact mono_yoneda_map_residueFieldMap B S hS V.scheme V.point V.residueField_contained
      obtain ⟨c, hcval, -⟩ := FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B S hS
        (yoneda.obj V.scheme) (isAlgebraicSpace_yoneda B S hS V.scheme) q0 quV hclass
      have h2 : yoneda.map c ≫ fieldMorphism B S hS (yoneda.obj V.scheme) q0 =
          fieldMorphism B S hS (yoneda.obj V.scheme) quV := by
        change yoneda.map c ≫ yonedaEquiv.symm q0.value = yonedaEquiv.symm quV.value
        rw [yonedaEquiv_symm_naturality_left c (yoneda.obj V.scheme) q0.value, hcval]
      exact ⟨c, (congrArg (yoneda.map c ≫ ·) hq0mor).symm.trans (h2.trans hquVmor)⟩
    rw [neighborhoodToSource, ← Category.assoc]
    exact mono_comp_pullback_snd B S hS V.toSpace f.hom
      (yoneda.map (residueFieldMap B S hS V.scheme V.point V.residueField_contained))
      (yoneda.map (residueFieldMap B S hS V.scheme V.point V.residueField_contained) ≫
        V.toSpace) rfl
      (yoneda.map (residueFieldMap B S hS U.scheme U.point U.residueField_contained) ≫
        U.toSpace) (yoneda.map c) hc

/-- The chart of `AlgebraicGeometry.Space.neighborhoodOverSource` is the chart of the
neighborhood it was built from. -/
@[simp]
theorem neighborhoodOverSource_scheme (hfst) (hsnd) :
    (neighborhoodOverSource B S hS f V U hfst hsnd).scheme = U.scheme := rfl

/-- The distinguished point of `AlgebraicGeometry.Space.neighborhoodOverSource` is the
distinguished point of the neighborhood it was built from. -/
@[simp]
theorem neighborhoodOverSource_point (hfst) (hsnd) :
    (neighborhoodOverSource B S hS f V U hfst hsnd).point = U.point := rfl

/-! ### The square of henselian local rings -/

section Henselian

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
  (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y)
  (x : points B S hS X) (y : points B S hS Y)
  (U : ElementaryEtaleNeighborhood B S hS X hX x)
  (W : ElementaryEtaleNeighborhood B S hS Y hY y)

/-- Universal property of a henselization (Stacks 04GS): a local ring map from `R` to a henselian
local ring `C` factors uniquely through a henselization `H` of `R` by a local ring map. -/
private theorem existsUnique_isLocalHom_comp_algebraMap {R H C : Type*} [CommRing R]
    [IsLocalRing R] [CommRing H] [IsLocalRing H] [Algebra R H]
    [IsHenselization R (ResidueField R) H] [CommRing C] [HenselianLocalRing C] (θ : R →+* C)
    [IsLocalHom θ] :
    ∃! ψ : H →+* C, IsLocalHom ψ ∧ ψ.comp (algebraMap R H) = θ := by
  let := θ.toAlgebra
  have : IsLocalHom (algebraMap R H) := IsHenselization.isLocalHom (L := ResidueField R)
  obtain ⟨f, hf, hu⟩ := StacksDraft.existsUnique_isLocalHom_of_indEtale (A := R) (B := H) (C := C)
    (StacksDraft.indEtale_of_isHenselization (ResidueField R))
    (IsHenselization.residueField_map_bijective (R := R) (Rh := H)).2
  refine ⟨f.toRingHom, ⟨⟨hf.map_nonunit⟩, RingHom.ext f.commutes⟩, fun g ⟨hg, hgθ⟩ ↦ ?_⟩
  exact congrArg AlgHom.toRingHom
    (hu { g with commutes' := RingHom.congr_fun hgθ } ⟨hg.map_nonunit⟩)

/-- **Stacks 0EPL.** Let `(U, u)` be an elementary étale neighborhood of a point `x` of a decent
algebraic space `X`, let `(W, w)` be one of a point `y` of a decent algebraic space `Y` and let
`j : U ⟶ W` be a morphism of the chart schemes carrying `u` to `w`. Then there is a local
homomorphism `𝒪^h_{Y, y} ⟶ 𝒪^h_{X, x}` over the map `𝒪_{W, w} ⟶ 𝒪_{U, u}` of neighborhood
stalks. -/
@[stacks 0EPL "the square of henselian local rings"]
theorem exists_henselianLocalRingMap_of_neighborhood
    (j : U.scheme ⟶ W.scheme) (hj : j.left.1 U.point = W.point) :
    letI := isLocalRing_henselianLocalRing B S hS hX hXdec x
    letI := isLocalRing_henselianLocalRing B S hS hY hYdec y
    ∃ φ : (henselianLocalRing B S hS Y hY y hYdec : Type (u + 1)) →+*
        (henselianLocalRing B S hS X hX x hXdec : Type (u + 1)),
      IsLocalHom φ ∧
      φ.comp (stalkToHenselianLocalRing B S hS Y hY y hYdec W) =
        (stalkToHenselianLocalRing B S hS X hX x hXdec U).comp
          ((W.scheme.left.1.presheaf.stalkCongr (Inseparable.of_eq hj.symm)).hom ≫
            j.left.1.stalkMap U.point).hom := by
  let := henselianLocalRing_isLocalRing B S hS X hX x hXdec
  let := stalkAlgebra B S hS X hX x hXdec U
  let := henselianLocalRing_isHenselization B S hS X hX x hXdec U
  let : IsLocalHom (algebraMap (U.scheme.left.1.presheaf.stalk U.point)
      (henselianLocalRing B S hS X hX x hXdec : Type (u + 1))) :=
    IsLocalRing.IsHenselization.isLocalHom
      (R := U.scheme.left.1.presheaf.stalk U.point)
      (L := IsLocalRing.ResidueField (U.scheme.left.1.presheaf.stalk U.point))
  let : IsLocalHom
      ((W.scheme.left.1.presheaf.stalkCongr (Inseparable.of_eq hj.symm)).hom ≫
        j.left.1.stalkMap U.point).hom :=
    isLocalHom_stalkCongr_comp_stalkMap j.left.1 hj
  let : HenselianLocalRing (henselianLocalRing B S hS X hX x hXdec : Type (u + 1)) :=
    IsLocalRing.IsHenselization.henselian (U.scheme.left.1.presheaf.stalk U.point)
      (IsLocalRing.ResidueField (U.scheme.left.1.presheaf.stalk U.point))
  let := henselianLocalRing_isLocalRing B S hS Y hY y hYdec
  let := stalkAlgebra B S hS Y hY y hYdec W
  let := henselianLocalRing_isHenselization B S hS Y hY y hYdec W
  obtain ⟨ψ, ⟨hψ, hψc⟩, -⟩ := existsUnique_isLocalHom_comp_algebraMap
    (H := (henselianLocalRing B S hS Y hY y hYdec : Type (u + 1)))
    ((stalkToHenselianLocalRing B S hS X hX x hXdec U).comp
      ((W.scheme.left.1.presheaf.stalkCongr (Inseparable.of_eq hj.symm)).hom ≫
        j.left.1.stalkMap U.point).hom)
  exact ⟨ψ, hψ, hψc⟩

end Henselian


/-! ### The diagram of Remark 0EPL -/

section Diagram

variable {Xs Ys : AlgebraicSpaces B S hS} (g : Xs ⟶ Ys) {z : points B S hS Xs.1}
  (hXd : IsDecentSpace B S hS Xs.1) (hYd : IsDecentSpace B S hS Ys.1)
  (N : ElementaryEtaleNeighborhood B S hS Xs.1 Xs.property z)
  (M : ElementaryEtaleNeighborhood B S hS Ys.1 Ys.property
    (pointsMap B S hS Xs.1 g.hom z))
  (k : N.scheme ⟶ M.scheme) (hk : k.left.1 N.point = M.point)
  (zbar : GeometricPoint B S hS Xs.1) (wbar : GeometricPoint B S hS Ys.1)
  (κN : Type u) [Field κN]
  [Algebra (ResidueField (N.scheme.left.1.presheaf.stalk N.point : Type u)) κN]
  [IsSepClosure (ResidueField (N.scheme.left.1.presheaf.stalk N.point : Type u)) κN]
  (κM : Type u) [Field κM]
  [Algebra (ResidueField (M.scheme.left.1.presheaf.stalk M.point : Type u)) κM]
  [IsSepClosure (ResidueField (M.scheme.left.1.presheaf.stalk M.point : Type u)) κM]

/-- **Stacks 0EPL, the commutative diagram.** For a pointed morphism `k : (N, n) ⟶ (M, m)` of
elementary étale neighborhoods over `g : X ⟶ Y`, the rows

`𝒪_{M, m} ⟶ 𝒪^h_{Y, y} ⟶ 𝒪_{Y, w̄}`  and  `𝒪_{N, n} ⟶ 𝒪^h_{X, z} ⟶ 𝒪_{X, z̄}`

are joined by local homomorphisms making both squares commute, over the map `𝒪_{M, m} ⟶ 𝒪_{N, n}`
of neighborhood stalks; and the étale and henselian local rings of the two spaces are the strict
henselization and the henselization of the respective neighborhood stalks. -/
@[stacks 0EPL "the commutative diagram, as a diagram of ring homomorphisms"]
theorem exists_diagram_of_neighborhood (hzbar : zbar.LiesOver z)
    (hwbar : wbar.LiesOver (pointsMap B S hS Xs.1 g.hom z)) :
    letI := isLocalRing_henselianLocalRing B S hS Xs.property hXd z
    letI := isLocalRing_henselianLocalRing B S hS Ys.property hYd
      (pointsMap B S hS Xs.1 g.hom z)
    letI := isLocalRing_etaleLocalRing B S hS Xs.1 Xs.property zbar
    letI := isLocalRing_etaleLocalRing B S hS Ys.1 Ys.property wbar
    ∃ (algN : Algebra (N.scheme.left.1.presheaf.stalk N.point : Type u)
          (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)))
      (algM : Algebra (M.scheme.left.1.presheaf.stalk M.point : Type u)
          (etaleLocalRing B S hS Ys.1 wbar : Type (u + 1)))
      (algHX : Algebra (henselianLocalRing B S hS Xs.1 Xs.property z hXd : Type (u + 1))
          (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)))
      (algHY : Algebra (henselianLocalRing B S hS Ys.1 Ys.property
            (pointsMap B S hS Xs.1 g.hom z) hYd : Type (u + 1))
          (etaleLocalRing B S hS Ys.1 wbar : Type (u + 1)))
      (φ : (henselianLocalRing B S hS Ys.1 Ys.property
            (pointsMap B S hS Xs.1 g.hom z) hYd : Type (u + 1)) →+*
          (henselianLocalRing B S hS Xs.1 Xs.property z hXd : Type (u + 1)))
      (ψ : (etaleLocalRing B S hS Ys.1 wbar : Type (u + 1)) →+*
          (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1))),
      IsLocalHom φ ∧ IsLocalHom ψ ∧
      φ.comp (stalkToHenselianLocalRing B S hS Ys.1 Ys.property
            (pointsMap B S hS Xs.1 g.hom z) hYd M) =
          (stalkToHenselianLocalRing B S hS Xs.1 Xs.property z hXd N).comp
            ((M.scheme.left.1.presheaf.stalkCongr (Inseparable.of_eq hk.symm)).hom ≫
              k.left.1.stalkMap N.point).hom ∧
      (@algebraMap (henselianLocalRing B S hS Xs.1 Xs.property z hXd : Type (u + 1))
            (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)) _ _ algHX).comp
          (stalkToHenselianLocalRing B S hS Xs.1 Xs.property z hXd N) =
        @algebraMap (N.scheme.left.1.presheaf.stalk N.point : Type u)
          (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)) _ _ algN ∧
      (@algebraMap (henselianLocalRing B S hS Ys.1 Ys.property
              (pointsMap B S hS Xs.1 g.hom z) hYd : Type (u + 1))
            (etaleLocalRing B S hS Ys.1 wbar : Type (u + 1)) _ _ algHY).comp
          (stalkToHenselianLocalRing B S hS Ys.1 Ys.property
            (pointsMap B S hS Xs.1 g.hom z) hYd M) =
        @algebraMap (M.scheme.left.1.presheaf.stalk M.point : Type u)
          (etaleLocalRing B S hS Ys.1 wbar : Type (u + 1)) _ _ algM ∧
      ψ.comp (@algebraMap (henselianLocalRing B S hS Ys.1 Ys.property
              (pointsMap B S hS Xs.1 g.hom z) hYd : Type (u + 1))
            (etaleLocalRing B S hS Ys.1 wbar : Type (u + 1)) _ _ algHY) =
        (@algebraMap (henselianLocalRing B S hS Xs.1 Xs.property z hXd : Type (u + 1))
            (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)) _ _ algHX).comp φ ∧
      @IsHenselization (N.scheme.left.1.presheaf.stalk N.point : Type u) _ _ κN _ _
        (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)) _ _ algN ∧
      @IsHenselization (M.scheme.left.1.presheaf.stalk M.point : Type u) _ _ κM _ _
        (etaleLocalRing B S hS Ys.1 wbar : Type (u + 1)) _ _ algM := by
  let := isLocalRing_henselianLocalRing B S hS Xs.property hXd z
  let := isLocalRing_henselianLocalRing B S hS Ys.property hYd
    (pointsMap B S hS Xs.1 g.hom z)
  let := isLocalRing_etaleLocalRing B S hS Xs.1 Xs.property zbar
  let := isLocalRing_etaleLocalRing B S hS Ys.1 Ys.property wbar
  obtain ⟨algN, algHX, _algResX, htowerX, hSHN, hHX⟩ :=
    exists_isHenselization_etaleLocalRing B S hS Xs.1 Xs.property z hXd N zbar hzbar κN
  obtain ⟨algM, algHY, _algResY, htowerY, hSHM, hHY⟩ :=
    exists_isHenselization_etaleLocalRing B S hS Ys.1 Ys.property
      (pointsMap B S hS Xs.1 g.hom z) hYd M wbar hwbar κM
  obtain ⟨φ, hφloc, hφsq⟩ :=
    exists_henselianLocalRingMap_of_neighborhood B S hS Xs.property Ys.property hXd hYd z
      (pointsMap B S hS Xs.1 g.hom z) N M k hk
  let := algN
  let := algM
  let := algHX
  let := algHY
  let := hSHN
  let := hSHM
  let := hHX
  let := hHY
  set θ := ((M.scheme.left.1.presheaf.stalkCongr (Inseparable.of_eq hk.symm)).hom ≫
    k.left.1.stalkMap N.point).hom with hθ
  have : IsLocalHom θ := isLocalHom_stalkCongr_comp_stalkMap k.left.1 hk
  obtain ⟨ψ, hψloc, hψsq⟩ :=
    IsLocalRing.IsHenselization.exists_isLocalHom_comp_of_isSepClosure θ
      (κA := κM) (κA' := κN)
      (Ash := (etaleLocalRing B S hS Ys.1 wbar : Type (u + 1)))
      (A'sh := (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)))
  refine ⟨algN, algM, algHX, algHY, φ, ψ, hφloc, hψloc, hφsq, htowerX, htowerY, ?_,
    hSHN, hSHM⟩
  -- The remaining square is the uniqueness half of Stacks 04GS over the stalk of `M`.
  let := stalkAlgebra B S hS Ys.1 Ys.property (pointsMap B S hS Xs.1 g.hom z) hYd M
  let := henselianLocalRing_isHenselization B S hS Ys.1 Ys.property
    (pointsMap B S hS Xs.1 g.hom z) hYd M
  have : IsLocalHom (@algebraMap (N.scheme.left.1.presheaf.stalk N.point : Type u)
      (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)) _ _ algN) :=
    IsLocalRing.IsHenselization.isLocalHom
      (R := (N.scheme.left.1.presheaf.stalk N.point : Type u)) (L := κN)
  have : HenselianLocalRing (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)) :=
    IsLocalRing.IsHenselization.henselian
      (R := (N.scheme.left.1.presheaf.stalk N.point : Type u)) (L := κN)
  have : IsLocalHom (@algebraMap (henselianLocalRing B S hS Ys.1 Ys.property
      (pointsMap B S hS Xs.1 g.hom z) hYd : Type (u + 1))
      (etaleLocalRing B S hS Ys.1 wbar : Type (u + 1)) _ _ algHY) :=
    IsLocalRing.IsHenselization.isLocalHom
      (R := (henselianLocalRing B S hS Ys.1 Ys.property
        (pointsMap B S hS Xs.1 g.hom z) hYd : Type (u + 1))) (L := κM)
  have : IsLocalHom (@algebraMap (henselianLocalRing B S hS Xs.1 Xs.property z hXd :
      Type (u + 1)) (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)) _ _ algHX) :=
    IsLocalRing.IsHenselization.isLocalHom
      (R := (henselianLocalRing B S hS Xs.1 Xs.property z hXd : Type (u + 1))) (L := κN)
  have : IsLocalHom ((@algebraMap _ (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)) _ _
      algN).comp θ) := RingHom.isLocalHom_comp _ _
  have hleft : (ψ.comp (@algebraMap _ (etaleLocalRing B S hS Ys.1 wbar : Type (u + 1)) _ _
        algHY)).comp (stalkToHenselianLocalRing B S hS Ys.1 Ys.property
          (pointsMap B S hS Xs.1 g.hom z) hYd M) =
      (@algebraMap _ (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)) _ _ algN).comp θ :=
    RingHom.ext fun r ↦
      (congrArg ψ (RingHom.congr_fun htowerY r)).trans (RingHom.congr_fun hψsq r)
  have hright : ((@algebraMap _ (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)) _ _
        algHX).comp φ).comp (stalkToHenselianLocalRing B S hS Ys.1 Ys.property
          (pointsMap B S hS Xs.1 g.hom z) hYd M) =
      (@algebraMap _ (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)) _ _ algN).comp θ :=
    RingHom.ext fun r ↦ (congrArg _ (RingHom.congr_fun hφsq r)).trans
      (RingHom.congr_fun htowerX (θ r))
  exact ((existsUnique_isLocalHom_comp_algebraMap (H := (henselianLocalRing B S hS Ys.1
    Ys.property (pointsMap B S hS Xs.1 g.hom z) hYd : Type (u + 1)))
    ((@algebraMap _ (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)) _ _ algN).comp θ)).unique
    ⟨inferInstance, hleft⟩ ⟨inferInstance, hright⟩)

/-- **Stacks 0EPL.** Let `g : X ⟶ Y` be a morphism of decent algebraic spaces over `S`, let `z`
be a point of `X` with image `y` in `Y`, and let `z̄` and `w̄` be geometric points of `X` and of
`Y` lying over `z` and over `y`. Then there are an elementary étale neighborhood `(M, m)` of
`y`, an elementary étale neighborhood `(N, n)` of `z` and a morphism `k : N ⟶ M` of chart
schemes over `g` carrying `n` to `m`, for which the two rows

`𝒪_{M, m} ⟶ 𝒪^h_{Y, y} ⟶ 𝒪_{Y, w̄}`  and  `𝒪_{N, n} ⟶ 𝒪^h_{X, z} ⟶ 𝒪_{X, z̄}`

are joined by local homomorphisms making both squares commute, the étale local rings being
strict henselizations and the henselian local rings henselizations of the two neighborhood
stalks.

Both choices of the remark are made here: `(M, m)` by Stacks 0BBP, and `(N, n)` together with
`k` by base change of `(M, m)` along `g`, which runs through the fibre product `M ×_Y X` and
chooses an elementary étale neighborhood of the point of it above `m` and `z`. -/
@[stacks 0EPL "the remark, with both choices made"]
theorem exists_diagram (hzbar : zbar.LiesOver z)
    (hwbar : wbar.LiesOver (pointsMap B S hS Xs.1 g.hom z)) :
    letI := isLocalRing_henselianLocalRing B S hS Xs.property hXd z
    letI := isLocalRing_henselianLocalRing B S hS Ys.property hYd
      (pointsMap B S hS Xs.1 g.hom z)
    letI := isLocalRing_etaleLocalRing B S hS Xs.1 Xs.property zbar
    letI := isLocalRing_etaleLocalRing B S hS Ys.1 Ys.property wbar
    ∃ (M₀ : ElementaryEtaleNeighborhood B S hS Ys.1 Ys.property
          (pointsMap B S hS Xs.1 g.hom z))
      (N₀ : ElementaryEtaleNeighborhood B S hS Xs.1 Xs.property z)
      (k₀ : N₀.scheme ⟶ M₀.scheme) (hk₀ : k₀.left.1 N₀.point = M₀.point)
      (algN : Algebra (N₀.scheme.left.1.presheaf.stalk N₀.point : Type u)
          (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)))
      (algM : Algebra (M₀.scheme.left.1.presheaf.stalk M₀.point : Type u)
          (etaleLocalRing B S hS Ys.1 wbar : Type (u + 1)))
      (algHX : Algebra (henselianLocalRing B S hS Xs.1 Xs.property z hXd : Type (u + 1))
          (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)))
      (algHY : Algebra (henselianLocalRing B S hS Ys.1 Ys.property
            (pointsMap B S hS Xs.1 g.hom z) hYd : Type (u + 1))
          (etaleLocalRing B S hS Ys.1 wbar : Type (u + 1)))
      (φ : (henselianLocalRing B S hS Ys.1 Ys.property
            (pointsMap B S hS Xs.1 g.hom z) hYd : Type (u + 1)) →+*
          (henselianLocalRing B S hS Xs.1 Xs.property z hXd : Type (u + 1)))
      (ψ : (etaleLocalRing B S hS Ys.1 wbar : Type (u + 1)) →+*
          (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1))),
      yoneda.map k₀ ≫ M₀.toSpace = N₀.toSpace ≫ g.hom ∧
      IsLocalHom φ ∧ IsLocalHom ψ ∧
      φ.comp (stalkToHenselianLocalRing B S hS Ys.1 Ys.property
            (pointsMap B S hS Xs.1 g.hom z) hYd M₀) =
          (stalkToHenselianLocalRing B S hS Xs.1 Xs.property z hXd N₀).comp
            ((M₀.scheme.left.1.presheaf.stalkCongr (Inseparable.of_eq hk₀.symm)).hom ≫
              k₀.left.1.stalkMap N₀.point).hom ∧
      (@algebraMap (henselianLocalRing B S hS Xs.1 Xs.property z hXd : Type (u + 1))
            (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)) _ _ algHX).comp
          (stalkToHenselianLocalRing B S hS Xs.1 Xs.property z hXd N₀) =
        @algebraMap (N₀.scheme.left.1.presheaf.stalk N₀.point : Type u)
          (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)) _ _ algN ∧
      (@algebraMap (henselianLocalRing B S hS Ys.1 Ys.property
              (pointsMap B S hS Xs.1 g.hom z) hYd : Type (u + 1))
            (etaleLocalRing B S hS Ys.1 wbar : Type (u + 1)) _ _ algHY).comp
          (stalkToHenselianLocalRing B S hS Ys.1 Ys.property
            (pointsMap B S hS Xs.1 g.hom z) hYd M₀) =
        @algebraMap (M₀.scheme.left.1.presheaf.stalk M₀.point : Type u)
          (etaleLocalRing B S hS Ys.1 wbar : Type (u + 1)) _ _ algM ∧
      ψ.comp (@algebraMap (henselianLocalRing B S hS Ys.1 Ys.property
              (pointsMap B S hS Xs.1 g.hom z) hYd : Type (u + 1))
            (etaleLocalRing B S hS Ys.1 wbar : Type (u + 1)) _ _ algHY) =
        (@algebraMap (henselianLocalRing B S hS Xs.1 Xs.property z hXd : Type (u + 1))
            (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)) _ _ algHX).comp φ ∧
      @IsHenselization (N₀.scheme.left.1.presheaf.stalk N₀.point : Type u) _ _ (SeparableClosure
          (ResidueField (N₀.scheme.left.1.presheaf.stalk N₀.point : Type u))) _ _
        (etaleLocalRing B S hS Xs.1 zbar : Type (u + 1)) _ _ algN ∧
      @IsHenselization (M₀.scheme.left.1.presheaf.stalk M₀.point : Type u) _ _ (SeparableClosure
          (ResidueField (M₀.scheme.left.1.presheaf.stalk M₀.point : Type u))) _ _
        (etaleLocalRing B S hS Ys.1 wbar : Type (u + 1)) _ _ algM := by
  let := isLocalRing_henselianLocalRing B S hS Xs.property hXd z
  let := isLocalRing_henselianLocalRing B S hS Ys.property hYd
    (pointsMap B S hS Xs.1 g.hom z)
  let := isLocalRing_etaleLocalRing B S hS Xs.1 Xs.property zbar
  let := isLocalRing_etaleLocalRing B S hS Ys.1 Ys.property wbar
  obtain ⟨M₀, -⟩ := exists_affine_elementaryEtaleNeighborhood' B S hS Ys.property hYd
    (pointsMap B S hS Xs.1 g.hom z)
  obtain ⟨N₀, k₀, hk₀, hsq, -⟩ := exists_elementaryEtaleNeighborhood_pullback_isLocalHom
    B S hS Ys.property Xs.property hXd g.hom z M₀
  obtain ⟨algN, algM, algHX, algHY, φ, ψ, hφloc, hψloc, hφsq, htowerX, htowerY, hsquare,
    hSHN, hSHM⟩ := exists_diagram_of_neighborhood B S hS g hXd hYd N₀ M₀ k₀ hk₀ zbar wbar
      (SeparableClosure (ResidueField (N₀.scheme.left.1.presheaf.stalk N₀.point : Type u)))
      (SeparableClosure (ResidueField (M₀.scheme.left.1.presheaf.stalk M₀.point : Type u)))
      hzbar hwbar
  exact ⟨M₀, N₀, k₀, hk₀, algN, algM, algHX, algHY, φ, ψ, hsq, hφloc, hψloc, hφsq,
    htowerX, htowerY, hsquare, hSHN, hSHM⟩

end Diagram

end AlgebraicGeometry.Space

end
