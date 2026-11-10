module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Characterization
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.GeometricPointStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorAmplitudeBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.CompatibleEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.EtaleSiteOfFppfSite

/-!
# The étale local ring of a fibre product of algebraic spaces

Let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square of algebraic spaces over a scheme `S`, and let `x̄'` be a geometric point
of `X'` with images `x̄` in `X`, `ȳ'` in `Y'` and `ȳ` in `Y`.  The canonical homomorphisms of
étale local rings of Stacks 04NG make a commutative square

```
𝒪_{Y,ȳ} ---> 𝒪_{X,x̄}
   |            |
   v            v
𝒪_{Y',ȳ'} --> 𝒪_{X',x̄'}
```

and this file proves that `𝒪_{X',x̄'}` is **weakly étale**, in particular **flat**, over
`𝒪_{X,x̄} ⊗_{𝒪_{Y,ȳ}} 𝒪_{Y',ȳ'}` through the induced homomorphism.

The reason is that the four étale local rings are the strict henselizations of Stacks 03PS of
the four local rings of a *cartesian* square of pointed étale scheme charts, and the canonical
morphism from a strict henselization to its scheme is weakly étale by Stacks 0993.  Writing
`U ⟶ V`, `V' ⟶ V` for the lower two chart morphisms and `U ×_V V'` for their fibre product,
the morphism

`Spec (𝒪_{U,u}^{sh} ⊗_{𝒪_{V,v}^{sh}} 𝒪_{V',v'}^{sh}) ⟶ U ×_V V'`

is the base change of a weakly étale morphism along a weakly étale morphism, so the morphism
`Spec 𝒪_{X',x̄'} ⟶ Spec (𝒪_{X,x̄} ⊗_{𝒪_{Y,ȳ}} 𝒪_{Y',ȳ'})` is weakly étale by cancellation,
hence flat.

## Main results

* `AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_weaklyEtale`: for every cartesian square
  of algebraic spaces and every geometric point of its upper-left corner, the étale local ring
  upstairs is a weakly étale algebra over the tensor product of the two neighbouring étale local
  rings over the one of the base, through a homomorphism restricting on the two factors to the
  canonical homomorphisms of Stacks 04NG.
* `AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_flat`: for every cartesian square of
  algebraic spaces and every geometric point of its upper-left corner, the étale local ring
  upstairs is a flat algebra over the tensor product of the two neighbouring étale local rings
  over the one of the base, through a homomorphism restricting on the two factors to the
  canonical homomorphisms of Stacks 04NG.  This is
  `AlgebraicGeometry.Space.IsEtaleStalkTensorFlat`.

## Implementation notes

The étale local ring of an algebraic space (Stacks 04KG) is a colimit indexed by the small
étale neighbourhoods of the geometric point, so it lives in `CommRingCat.{u + 1}`, one universe
above the schemes; the étale local ring of a *scheme* at a geometric point (Stacks 03PS) lives
in `RingCat.{u}`, and `AlgebraicGeometry.Space.etaleLocalRingEquivChart` of Stacks 04KF
identifies the two across that universe gap.  Weak étaleness is therefore proved for the
scheme-side rings, where `Spec` is available, and transported back along those isomorphisms:
`AlgebraicGeometry.Space.tensorRingCongr` carries the tensor product itself, and
`AlgebraicGeometry.Space.weaklyEtale_of_comp_ringEquiv` says that weak étaleness of a
homomorphism is insensitive to composition with isomorphisms on either side.

The cartesian square of pointed charts is
`AlgebraicGeometry.Space.PointedChartSquare`, produced by
`AlgebraicGeometry.Space.exists_affine_pointedChartSquare`: the compatible étale charts of
Stacks 04KF for the square are first chosen with
`AlgebraicGeometry.Space.exists_compatible_etale_charts`, the geometric point is lifted to the
chart of `X'` since that chart is a surjective étale atlas, and the three lower charts are then
shrunk to affine Zariski opens through which the chosen lifts still factor.  Shrinking destroys
cartesianity of the square of chart schemes, but it keeps the comparison morphism
`U' ⟶ U ×_V V'` weakly étale, which is all the argument uses.

Affineness of the three lower charts is what makes
`AlgebraicGeometry.Space.spec_etaleLocalRingGerm_comp` available: a morphism of affine schemes
is determined by its action on global sections, and the canonical homomorphism of étale local
rings is characterised by its action on germs of global chart sections.

## References

* [Stacks Project, Tag 0DKD](https://stacks.math.columbia.edu/tag/0DKD)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 03PS](https://stacks.math.columbia.edu/tag/03PS)
* [Stacks Project, Tag 0993](https://stacks.math.columbia.edu/tag/0993)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

/-! ### Transport of a tensor product along isomorphisms of its three rings -/

/-- A tensor product of commutative rings is carried by isomorphisms of the base ring and of
the two factors, compatible with the two structure maps, to the tensor product of the
targets. -/
def tensorRingCongr {R₁ R₂ A₁ A₂ C₁ C₂ : Type*}
    [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂] [CommRing C₁] [CommRing C₂]
    [Algebra R₁ A₁] [Algebra R₁ C₁] [Algebra R₂ A₂] [Algebra R₂ C₂]
    (eR : R₁ ≃+* R₂) (eA : A₁ ≃+* A₂) (eC : C₁ ≃+* C₂)
    (hA : ∀ r, eA (algebraMap R₁ A₁ r) = algebraMap R₂ A₂ (eR r))
    (hC : ∀ r, eC (algebraMap R₁ C₁ r) = algebraMap R₂ C₂ (eR r)) :
    A₁ ⊗[R₁] C₁ ≃+* A₂ ⊗[R₂] C₂ := by
  have := RingHomInvPair.of_ringEquiv eR
  have := RingHomInvPair.of_ringEquiv_symm eR
  let fA : A₁ ≃ₛₗ[RingHomClass.toRingHom eR] A₂ :=
    { __ := eA.toAddEquiv
      map_smul' := fun r a => by
        change eA (r • a) = eR r • eA a
        simp only [Algebra.smul_def, map_mul, hA] }
  let fC : C₁ ≃ₛₗ[RingHomClass.toRingHom eR] C₂ :=
    { __ := eC.toAddEquiv
      map_smul' := fun r a => by
        change eC (r • a) = eR r • eC a
        simp only [Algebra.smul_def, map_mul, hC] }
  let e := TensorProduct.congr fA fC
  refine { __ := e.toAddEquiv, map_mul' := ?_ }
  intro z w
  change e (z * w) = e z * e w
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ h₁ h₂ => simp [add_mul, h₁, h₂]
  | tmul a c =>
    induction w using TensorProduct.inductionOn with
    | add w₁ w₂ h₁ h₂ => simp [mul_add, h₁, h₂]
    | tmul a' c' => simp [e, fA, fC, Algebra.TensorProduct.tmul_mul_tmul]

/-- The inverse of `AlgebraicGeometry.Space.tensorRingCongr` on a pure tensor. -/
theorem tensorRingCongr_symm_tmul {R₁ R₂ A₁ A₂ C₁ C₂ : Type*}
    [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂] [CommRing C₁] [CommRing C₂]
    [Algebra R₁ A₁] [Algebra R₁ C₁] [Algebra R₂ A₂] [Algebra R₂ C₂]
    (eR : R₁ ≃+* R₂) (eA : A₁ ≃+* A₂) (eC : C₁ ≃+* C₂)
    (hA : ∀ r, eA (algebraMap R₁ A₁ r) = algebraMap R₂ A₂ (eR r))
    (hC : ∀ r, eC (algebraMap R₁ C₁ r) = algebraMap R₂ C₂ (eR r)) (a : A₂) (c : C₂) :
    (tensorRingCongr eR eA eC hA hC).symm (a ⊗ₜ[R₂] c) = eA.symm a ⊗ₜ[R₁] eC.symm c := rfl

/-- Weak étaleness of a ring homomorphism may be read after composing with isomorphisms on
either side. -/
theorem weaklyEtale_of_comp_ringEquiv {A A' T T' : Type*} [CommRing A] [CommRing A']
    [CommRing T] [CommRing T'] (f : A →+* T) (eA : A' ≃+* A) (eT : T ≃+* T')
    (h : @Algebra.WeaklyEtale A' T' _ _ ((eT.toRingHom.comp f).comp eA.toRingHom).toAlgebra) :
    @Algebra.WeaklyEtale A T _ _ f.toAlgebra := by
  let g := (eT.toRingHom.comp f).comp eA.toRingHom
  let : Algebra A' T' := g.toAlgebra
  let : Algebra A A' := eA.symm.toRingHom.toAlgebra
  let : Algebra A T' := (eT.toRingHom.comp f).toAlgebra
  have : IsScalarTower A A' T' := IsScalarTower.of_algebraMap_eq fun a => by
    change eT (f a) = eT (f (eA (eA.symm a)))
    rw [eA.apply_symm_apply]
  have : Algebra.Etale A A' :=
    Algebra.Etale.of_equiv (R := A) (A := A)
      { eA.symm with commutes' := fun _ => rfl }
  have : Algebra.WeaklyEtale A T' := Algebra.WeaklyEtale.trans A A' T'
  let : Algebra A T := f.toAlgebra
  let : Algebra T' T := eT.symm.toRingHom.toAlgebra
  have : IsScalarTower A T' T := IsScalarTower.of_algebraMap_eq fun a => by
    change f a = eT.symm (eT (f a))
    rw [eT.symm_apply_apply]
  have : Algebra.Etale T' T :=
    Algebra.Etale.of_equiv (R := T') (A := T')
      { eT.symm with commutes' := fun _ => rfl }
  exact Algebra.WeaklyEtale.trans A T' T

/-! ### Weakly étale morphisms into a fibre product -/

/-- The morphism of fibre products induced by a weakly étale morphism of cospans is weakly
étale: it factors as the base change of the diagonal of the weakly étale map of the two
targets followed by the base change of the two weakly étale maps of the legs. -/
theorem weaklyEtale_pullbackMap {U V W X Y Z : Scheme.{u}}
    (p : U ⟶ W) (q : V ⟶ W) (f : X ⟶ Z) (g : Y ⟶ Z)
    (a : U ⟶ X) (b : V ⟶ Y) (c : W ⟶ Z)
    (ha : p ≫ c = a ≫ f) (hb : q ≫ c = b ≫ g)
    [WeaklyEtale a] [WeaklyEtale b] [WeaklyEtale c] :
    WeaklyEtale (pullback.map p q f g a b c ha hb) := by
  have hmul : MorphismProperty.IsStableUnderComposition (@WeaklyEtale.{u}) :=
    (inferInstance :
      MorphismProperty.IsMultiplicative (@WeaklyEtale.{u})).toIsStableUnderComposition
  let j := pullback.mapDesc p q c
  let k := pullback.map (p ≫ c) (q ≫ c) f g a b (𝟙 Z)
    (by simpa using ha) (by simpa using hb)
  have hj : WeaklyEtale j :=
    MorphismProperty.of_isPullback (P := @WeaklyEtale)
      (pullback_map_diagonal_isPullback p q c) inferInstance
  have hk : WeaklyEtale k :=
    MorphismProperty.pullbackMap (P := @WeaklyEtale)
      (inferInstance : WeaklyEtale a) (inferInstance : WeaklyEtale b) ha hb
  have heq : pullback.map p q f g a b c ha hb = j ≫ k := by
    apply pullback.hom_ext <;>
      simp [j, k, pullback.mapDesc, pullback.map, Category.assoc]
  rw [heq]
  have := hj
  have := hk
  infer_instance

/-- **Cancellation in a cartesian cube.** If the bottom face of a cube over a cartesian square
has all four vertical morphisms weakly étale, then so is the comparison morphism from the upper
corner of the bottom face to the fibre product of its two legs. -/
theorem weaklyEtale_pullbackLift_of_cartesian_cube
    {X Y Y' X' U V V' U' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (h : IsPullback g' f' f g)
    (p : U ⟶ V) (q : V' ⟶ V) (r : U' ⟶ U) (s : U' ⟶ V')
    (a : U ⟶ X) (b : V ⟶ Y) (c : V' ⟶ Y') (d : U' ⟶ X')
    (hp : p ≫ b = a ≫ f) (hq : q ≫ b = c ≫ g)
    (hr : r ≫ a = d ≫ g') (hs : s ≫ c = d ≫ f')
    (hrs : r ≫ p = s ≫ q)
    [WeaklyEtale a] [WeaklyEtale b] [WeaklyEtale c] [WeaklyEtale d] :
    WeaklyEtale (pullback.lift r s hrs) := by
  let j := pullback.map p q f g a c b hp hq ≫ h.isoPullback.inv
  have hj : WeaklyEtale j := by
    have := weaklyEtale_pullbackMap p q f g a c b hp hq
    change WeaklyEtale (pullback.map p q f g a c b hp hq ≫ h.isoPullback.inv)
    infer_instance
  have hcomp : pullback.lift r s hrs ≫ j = d := by
    apply h.hom_ext
    · simpa [j, pullback.map, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc] using hr
    · simpa [j, pullback.map, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc] using hs
  have hcj : WeaklyEtale (pullback.lift r s hrs ≫ j) := by
    rw [hcomp]
    infer_instance
  have := hj
  exact WeaklyEtale.of_comp _ j

/-- **Weak étaleness of a tensor product of rings over a cartesian cube.** Let a cartesian
square of schemes be covered by a square of affine schemes whose four comparison morphisms are
weakly étale, the lower face being the spectra of `R → A`, `R → B` and of a homomorphism
`φ : A ⊗[R] B → T` restricting to them.  Then `φ` is weakly étale.

Indeed `Spec T ⟶ Spec (A ⊗[R] B) = Spec A ×_{Spec R} Spec B` is the comparison morphism of the
cube, which `AlgebraicGeometry.Space.weaklyEtale_pullbackLift_of_cartesian_cube` makes weakly
étale. -/
theorem tensorProductMap_weaklyEtale_of_cartesian_cube
    (R A C T : Type u) [CommRing R] [CommRing A] [CommRing C] [CommRing T]
    [Algebra R A] [Algebra R C]
    {X Y Y' X' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (h : IsPullback g' f' f g)
    (a : Spec (.of A) ⟶ X) (b : Spec (.of R) ⟶ Y)
    (c : Spec (.of C) ⟶ Y') (d : Spec (.of T) ⟶ X')
    (hp : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b = a ≫ f)
    (hq : Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ b = c ≫ g)
    (φ : A ⊗[R] C →+* T)
    (hr : Spec.map (CommRingCat.ofHom
      (φ.comp Algebra.TensorProduct.includeLeftRingHom)) ≫ a = d ≫ g')
    (hs : Spec.map (CommRingCat.ofHom
      (φ.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ c = d ≫ f')
    [WeaklyEtale a] [WeaklyEtale b] [WeaklyEtale c] [WeaklyEtale d] :
    @Algebra.WeaklyEtale (A ⊗[R] C) T _ _ φ.toAlgebra := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let q := Spec.map (CommRingCat.ofHom (algebraMap R C))
  let e := pullbackSpecIso R A C
  let k := Spec.map (CommRingCat.ofHom φ) ≫ e.inv
  let r := Spec.map (CommRingCat.ofHom
    (φ.comp Algebra.TensorProduct.includeLeftRingHom))
  let s := Spec.map (CommRingCat.ofHom
    (φ.comp Algebra.TensorProduct.includeRight.toRingHom))
  have hk₁ : k ≫ pullback.fst p q = r := by
    change (Spec.map (CommRingCat.ofHom φ) ≫ e.inv) ≫ pullback.fst p q = r
    rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
    rfl
  have hk₂ : k ≫ pullback.snd p q = s := by
    change (Spec.map (CommRingCat.ofHom φ) ≫ e.inv) ≫ pullback.snd p q = s
    rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
    rfl
  have hrs : r ≫ p = s ≫ q := by
    calc
      r ≫ p = k ≫ (pullback.fst p q ≫ p) := by rw [← hk₁, Category.assoc]
      _ = k ≫ (pullback.snd p q ≫ q) := by rw [pullback.condition]
      _ = s ≫ q := by rw [← Category.assoc, hk₂]
  have hk : k = pullback.lift r s hrs := by
    apply pullback.hom_ext
    · rw [hk₁, pullback.lift_fst]
    · rw [hk₂, pullback.lift_snd]
  have hwk : WeaklyEtale k := by
    rw [hk]
    exact weaklyEtale_pullbackLift_of_cartesian_cube h p q r s a b c d hp hq hr hs hrs
  have heq : Spec.map (CommRingCat.ofHom φ) = k ≫ e.hom := by
    change Spec.map (CommRingCat.ofHom φ) =
      (Spec.map (CommRingCat.ofHom φ) ≫ e.inv) ≫ e.hom
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  refine (weaklyEtale_specMap_iff (CommRingCat.ofHom φ)).mp ?_
  rw [heq]
  have := hwk
  infer_instance

/-- **Flatness of a tensor product of rings over a cartesian cube.** In the situation of
`AlgebraicGeometry.Space.tensorProductMap_weaklyEtale_of_cartesian_cube` the homomorphism
`φ : A ⊗[R] B → T` is flat, a weakly étale homomorphism being flat. -/
theorem tensorProductMap_flat_of_cartesian_cube
    (R A C T : Type u) [CommRing R] [CommRing A] [CommRing C] [CommRing T]
    [Algebra R A] [Algebra R C]
    {X Y Y' X' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (h : IsPullback g' f' f g)
    (a : Spec (.of A) ⟶ X) (b : Spec (.of R) ⟶ Y)
    (c : Spec (.of C) ⟶ Y') (d : Spec (.of T) ⟶ X')
    (hp : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ b = a ≫ f)
    (hq : Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ b = c ≫ g)
    (φ : A ⊗[R] C →+* T)
    (hr : Spec.map (CommRingCat.ofHom
      (φ.comp Algebra.TensorProduct.includeLeftRingHom)) ≫ a = d ≫ g')
    (hs : Spec.map (CommRingCat.ofHom
      (φ.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ c = d ≫ f')
    [WeaklyEtale a] [WeaklyEtale b] [WeaklyEtale c] [WeaklyEtale d] :
    φ.Flat := by
  let : Algebra (A ⊗[R] C) T := φ.toAlgebra
  have hw : Algebra.WeaklyEtale (A ⊗[R] C) T :=
    tensorProductMap_weaklyEtale_of_cartesian_cube R A C T h a b c d hp hq φ hr hs
  exact RingHom.flat_algebraMap_iff.mpr hw.flat

/-! ### Pointed cartesian squares of étale charts -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of the big fppf site whose set-theoretic image lies in the range of an open
immersion of the site factors through that open immersion. -/
theorem exists_lift_of_range_subset {U V W : BigFppfOver B S hS} (j : V ⟶ U) (k : W ⟶ U)
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (hk : Set.range ((BigFppfOver.toScheme B S hS).map k) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map j)) :
    ∃ l : W ⟶ V, l ≫ j = k := by
  let H := BigFppfOver.toScheme B S hS
  let l := IsOpenImmersion.lift (H.map j) (H.map k) hk
  let a : W.left ⟶ V.left := B.inclusion.preimage l
  have ha : a ≫ j.left = k.left := by
    apply B.inclusion.map_injective
    change B.inclusion.map (B.inclusion.preimage l) ≫ H.map j = H.map k
    rw [Functor.map_preimage]
    exact IsOpenImmersion.lift_fac _ _ _
  exact ⟨Over.homMk a (by rw [← j.w, ← Category.assoc, ha, k.w]), Over.OverMorphism.ext ha⟩

/-- Every small étale neighbourhood of a geometric point is refined, inside any prescribed
Zariski open of its chart containing the selected point, by one whose chart is an affine
Zariski open of the given chart. -/
theorem exists_affine_refinement {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {x : GeometricPoint B S hS X} (V : SmallEtaleNeighborhood x)
    (O : (neighborhoodChartScheme V).Opens) (hx : chartPoint B S hS X V ∈ O) :
    ∃ (W : SmallEtaleNeighborhood x) (j : W.chart.obj.left ⟶ V.chart.obj.left),
      IsAffine (neighborhoodChartScheme W) ∧
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
      W.chart.obj.hom = yoneda.map j ≫ V.chart.obj.hom ∧
      W.point ≫ j = V.point ∧
      Set.range ((BigFppfOver.toScheme B S hS).map j) ⊆ O := by
  obtain ⟨W, hW, hxW, hWO⟩ := exists_isAffineOpen_mem_and_subset hx
  refine ⟨chartOpenNeighborhood B S hS V W hxW, chartOpenOverι B S hS V.chart W, hW,
    inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion W.ι), rfl,
    chartOpenNeighborhood_point_comp B S hS V W hxW, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact hWO z.property

/-- A square of pointed étale scheme charts over a commutative square of algebraic spaces: a
chart of each of the four corners, a morphism of charts over each of the four morphisms, each
carrying the chosen lift of the geometric point to the chosen lift, and commutativity of the
square of chart morphisms. -/
structure PointedChartSquare {X Y X' Y' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (x : GeometricPoint B S hS X'.1) where
  /-- The chart of `X`. -/
  U : SmallEtaleNeighborhood (geometricPointMap g'.hom x)
  /-- The chart of `Y`. -/
  V : SmallEtaleNeighborhood (geometricPointMap f.hom (geometricPointMap g'.hom x))
  /-- The chart of `X'`. -/
  U' : SmallEtaleNeighborhood x
  /-- The chart of `Y'`. -/
  V' : SmallEtaleNeighborhood (geometricPointMap f'.hom x)
  /-- The chart morphism over `f`. -/
  p : U.chart.obj.left ⟶ V.chart.obj.left
  /-- The chart morphism over `g`. -/
  q : V'.chart.obj.left ⟶ V.chart.obj.left
  /-- The chart morphism over `g'`. -/
  r : U'.chart.obj.left ⟶ U.chart.obj.left
  /-- The chart morphism over `f'`. -/
  s : U'.chart.obj.left ⟶ V'.chart.obj.left
  /-- The chart morphism `p` lies over `f`. -/
  hp : U.chart.obj.hom ≫ f.hom = yoneda.map p ≫ V.chart.obj.hom
  /-- The chart morphism `q` lies over `g`. -/
  hq : V'.chart.obj.hom ≫ g.hom = yoneda.map q ≫ V.chart.obj.hom
  /-- The chart morphism `r` lies over `g'`. -/
  hr : U'.chart.obj.hom ≫ g'.hom = yoneda.map r ≫ U.chart.obj.hom
  /-- The chart morphism `s` lies over `f'`. -/
  hs : U'.chart.obj.hom ≫ f'.hom = yoneda.map s ≫ V'.chart.obj.hom
  /-- The chart morphism `p` carries the chosen lift to the chosen lift. -/
  pp : U.point ≫ p = V.point
  /-- The chart morphism `q` carries the chosen lift to the chosen lift. -/
  pq : V'.point ≫ q = V.point
  /-- The chart morphism `r` carries the chosen lift to the chosen lift. -/
  pr : U'.point ≫ r = U.point
  /-- The chart morphism `s` carries the chosen lift to the chosen lift. -/
  ps : U'.point ≫ s = V'.point
  /-- The square of chart morphisms commutes. -/
  comm : r ≫ p = s ≫ q

set_option synthInstance.maxHeartbeats 400000 in
-- instance search through the pullback and chart categories on the big fppf site is slow
set_option maxHeartbeats 1000000 in
-- long proof building compatible étale charts and their pullback squares on the big fppf site
/-- **A cartesian square of algebraic spaces has a pointed cartesian square of étale charts.**
The compatible étale charts of the square are chosen first; the chart of the upper-left corner
is a surjective étale atlas, so the geometric point lifts to it, and the three images of that
lift are the chosen lifts in the other three charts. -/
theorem exists_pointedChartSquare {X Y X' Y' : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (h : IsPullback g' f' f g) (x : GeometricPoint B S hS X'.1) :
    ∃ C : PointedChartSquare B S hS f g g' f' x,
      IsPullback ((BigFppfOver.toScheme B S hS).map C.r)
        ((BigFppfOver.toScheme B S hS).map C.s)
        ((BigFppfOver.toScheme B S hS).map C.p)
        ((BigFppfOver.toScheme B S hS).map C.q) := by
  let H := BigFppfOver.toScheme B S hS
  let PE := MorphismProperty.inverseImage (@Etale.{u}) H
  let PS := MorphismProperty.inverseImage (@Surjective.{u}) H
  have hetmul : MorphismProperty.IsStableUnderComposition (@Etale.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative (@Etale.{u})).toIsStableUnderComposition
  have hPEbc : PE.IsStableUnderBaseChange := by
    constructor
    intro _ _ _ _ _ _ _ _ hsq hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Etale) (hsq.map H) hf
  have hPEcomp : PE.IsStableUnderComposition := .inverseImage H
  have hPEpre : PE.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange PE
  obtain ⟨U, V, U', V', p, q, r, s, v, a, b, c, hc, hap, hbq, hcr, hcs,
    hvS, hvE, haS, haE, hbS, hbE, hcS, hcE⟩ :=
    exists_compatible_etale_charts B S hS f g
  let hr := AlgebraicSpaces.isPullback_hom B S hS h
  let e := hr.isoPullback
  let a₀ := a ≫ pullback.snd v f.hom
  let b₀ := b ≫ pullback.snd v g.hom
  let c₀ := c ≫ e.inv
  have ha₀ : PE.presheaf a₀ := MorphismProperty.comp_mem _ _ _ haE
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback v f.hom) hvE)
  have hb₀ : PE.presheaf b₀ := MorphismProperty.comp_mem _ _ _ hbE
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback v g.hom) hvE)
  have hc₀ : PE.presheaf c₀ := MorphismProperty.RespectsIso.postcomp _ e.inv c hcE
  have hc₀S : PS.presheaf c₀ := MorphismProperty.RespectsIso.postcomp _ e.inv c hcS
  obtain ⟨l, hl'⟩ := exists_chartLift_of_isSurjective B S hS X'.1 X'.2
    ⟨CostructuredArrow.mk c₀, hc₀⟩ (isSurjective_of_presheafSurjective B S hS c₀ hc₀S) x
  have hl₀ : c₀.app (Opposite.op x.val.siteObject) l = x.val.value := hl'
  have hp : a₀ ≫ f.hom = yoneda.map p ≫ v := by
    change (a ≫ pullback.snd v f.hom) ≫ f.hom = yoneda.map p ≫ v
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hap]
  have hq : b₀ ≫ g.hom = yoneda.map q ≫ v := by
    change (b ≫ pullback.snd v g.hom) ≫ g.hom = yoneda.map q ≫ v
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hbq]
  have hr₀ : c₀ ≫ g'.hom = yoneda.map r ≫ a₀ := by
    change (c ≫ e.inv) ≫ g'.hom = yoneda.map r ≫ a ≫ pullback.snd v f.hom
    rw [Category.assoc, hr.isoPullback_inv_fst]
    exact hcr
  have hs₀ : c₀ ≫ f'.hom = yoneda.map s ≫ b₀ := by
    change (c ≫ e.inv) ≫ f'.hom = yoneda.map s ≫ b ≫ pullback.snd v g.hom
    rw [Category.assoc, hr.isoPullback_inv_snd]
    exact hcs
  have hcomm : r ≫ p = s ≫ q := by
    apply H.map_injective
    simpa only [Functor.map_comp] using hc.w
  have hlU : a₀.app (.op x.val.siteObject) (l ≫ r) =
      (geometricPointMap g'.hom x).val.value := by
    have hh := ConcreteCategory.congr_hom (NatTrans.congr_app hr₀ (.op x.val.siteObject)) l
    simpa [hl₀, geometricPointMap, FieldValuedPoint.map] using hh.symm
  have hlV' : b₀.app (.op x.val.siteObject) (l ≫ s) =
      (geometricPointMap f'.hom x).val.value := by
    have hh := ConcreteCategory.congr_hom (NatTrans.congr_app hs₀ (.op x.val.siteObject)) l
    simpa [hl₀, geometricPointMap, FieldValuedPoint.map] using hh.symm
  have hlV : v.app (.op x.val.siteObject) ((l ≫ r) ≫ p) =
      (geometricPointMap f.hom (geometricPointMap g'.hom x)).val.value := by
    have hh := congrArg (fun t : yoneda.obj U ⟶ Y.obj =>
      t.app (.op x.val.siteObject) (l ≫ r)) hp
    change f.hom.app _ (a₀.app _ (l ≫ r)) = v.app _ ((l ≫ r) ≫ p) at hh
    exact hh.symm.trans (congrArg (fun z => f.hom.app (.op x.val.siteObject) z) hlU)
  refine ⟨{ U := ⟨⟨CostructuredArrow.mk a₀, ha₀⟩, l ≫ r, hlU⟩
            V := ⟨⟨CostructuredArrow.mk v, hvE⟩, (l ≫ r) ≫ p, hlV⟩
            U' := ⟨⟨CostructuredArrow.mk c₀, hc₀⟩, l, hl₀⟩
            V' := ⟨⟨CostructuredArrow.mk b₀, hb₀⟩, l ≫ s, hlV'⟩
            p := p, q := q, r := r, s := s
            hp := hp, hq := hq, hr := hr₀, hs := hs₀
            pp := rfl
            pq := by
              change (l ≫ s) ≫ q = (l ≫ r) ≫ p
              rw [Category.assoc, ← hcomm, ← Category.assoc]
            pr := rfl, ps := rfl, comm := hcomm }, hc⟩

/-- If `a ≫ p = b ≫ j` with `j` sent to an open immersion, then every point in the image of `a`
lies in the preimage under `p` of the range of `j`. -/
private theorem map_apply_mem_preimage_opensRange {𝒞 : Type*} [Category 𝒞] (F : 𝒞 ⥤ Scheme.{u})
    {T A B C : 𝒞} (a : T ⟶ A) (b : T ⟶ B) (p : A ⟶ C) (j : B ⟶ C)
    [_root_.AlgebraicGeometry.IsOpenImmersion (F.map j)] (h : a ≫ p = b ≫ j) (z : F.obj T) :
    F.map a z ∈ F.map p ⁻¹ᵁ (F.map j).opensRange :=
  ⟨F.map b z, by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← F.map_comp, ← F.map_comp, h]⟩

/-- A morphism of refined charts lying over a morphism of the original charts carries a lift of
a point to a lift of its image, as soon as the target refinement is a monomorphism. -/
private theorem point_comp_of_refinement {𝒞 : Type*} [Category 𝒞] {T U V CU CV : 𝒞}
    {u : T ⟶ U} {v : T ⟶ V} {cu : T ⟶ CU} {cv : T ⟶ CV} {jU : U ⟶ CU} {jV : V ⟶ CV}
    {p : U ⟶ V} {cp : CU ⟶ CV} [Mono jV] (hp : p ≫ jV = jU ≫ cp) (hu : u ≫ jU = cu)
    (hv : v ≫ jV = cv) (hc : cu ≫ cp = cv) : u ≫ p = v := by
  apply (cancel_mono jV).mp
  rw [Category.assoc, hp, ← Category.assoc, hu, hc, hv]

/-- The structure morphisms of two refined charts are compatible with a morphism of refined charts
lying over a compatible morphism of the original charts. -/
private theorem hom_comp_of_refinement {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟)
    {U V CU CV : 𝒞} {A B : 𝒟} {uh : F.obj U ⟶ A} {vh : F.obj V ⟶ B} {cuh : F.obj CU ⟶ A}
    {cvh : F.obj CV ⟶ B} {f : A ⟶ B} {jU : U ⟶ CU} {jV : V ⟶ CV} {p : U ⟶ V} {cp : CU ⟶ CV}
    (hp : p ≫ jV = jU ≫ cp) (hu : uh = F.map jU ≫ cuh) (hv : vh = F.map jV ≫ cvh)
    (hc : cuh ≫ f = F.map cp ≫ cvh) : uh ≫ f = F.map p ≫ vh := by
  rw [hu, hv, Category.assoc, hc, ← Category.assoc, ← F.map_comp, ← hp, F.map_comp,
    Category.assoc]

/-- **A pointed square of étale charts can be taken affine on its three lower corners.**
Shrinking the three charts to affine Zariski opens through which the chosen lifts still factor
destroys cartesianity of the square of chart schemes, but keeps the comparison morphism from
the chart of the upper-left corner to the fibre product of the other two weakly étale. -/
theorem exists_affine_pointedChartSquare {X Y X' Y' : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (h : IsPullback g' f' f g) (x : GeometricPoint B S hS X'.1) :
    ∃ C : PointedChartSquare B S hS f g g' f' x,
      IsAffine (neighborhoodChartScheme C.U) ∧
      IsAffine (neighborhoodChartScheme C.V) ∧
      IsAffine (neighborhoodChartScheme C.V') ∧
      WeaklyEtale (pullback.lift (f := (BigFppfOver.toScheme B S hS).map C.p)
        (g := (BigFppfOver.toScheme B S hS).map C.q)
        ((BigFppfOver.toScheme B S hS).map C.r)
        ((BigFppfOver.toScheme B S hS).map C.s)
        (by simpa only [Functor.map_comp] using
          congrArg (BigFppfOver.toScheme B S hS).map C.comm)) := by
  obtain ⟨C, hC⟩ := exists_pointedChartSquare B S hS h x
  let H := BigFppfOver.toScheme B S hS
  obtain ⟨V, jV, hV, hjV, hjVc, hjVp, -⟩ := exists_affine_refinement B S hS C.V ⊤ trivial
  have := hjV
  have hmonoV : Mono jV := H.mono_of_mono_map inferInstance
  have hpV : chartPoint B S hS X.1 C.U ∈ (H.map C.p) ⁻¹ᵁ (H.map jV).opensRange :=
    map_apply_mem_preimage_opensRange H _ _ _ _ (C.pp.trans hjVp.symm) _
  obtain ⟨U, jU, hU, hjU, hjUc, hjUp, hrangeU⟩ :=
    exists_affine_refinement B S hS C.U _ hpV
  have := hjU
  have hmonoU : Mono jU := H.mono_of_mono_map inferInstance
  obtain ⟨p, hp⟩ := exists_lift_of_range_subset B S hS jV (jU ≫ C.p) (by
    rintro _ ⟨z, rfl⟩
    exact hrangeU ⟨z, rfl⟩)
  have hqV : chartPoint B S hS Y'.1 C.V' ∈ (H.map C.q) ⁻¹ᵁ (H.map jV).opensRange :=
    map_apply_mem_preimage_opensRange H _ _ _ _ (C.pq.trans hjVp.symm) _
  obtain ⟨V', jV', hV', hjV', hjV'c, hjV'p, hrangeV'⟩ :=
    exists_affine_refinement B S hS C.V' _ hqV
  have := hjV'
  have hmonoV' : Mono jV' := H.mono_of_mono_map inferInstance
  obtain ⟨q, hq⟩ := exists_lift_of_range_subset B S hS jV (jV' ≫ C.q) (by
    rintro _ ⟨z, rfl⟩
    exact hrangeV' ⟨z, rfl⟩)
  have hrU : chartPoint B S hS X'.1 C.U' ∈ (H.map C.r) ⁻¹ᵁ (H.map jU).opensRange :=
    map_apply_mem_preimage_opensRange H _ _ _ _ (C.pr.trans hjUp.symm) _
  have hsV' : chartPoint B S hS X'.1 C.U' ∈ (H.map C.s) ⁻¹ᵁ (H.map jV').opensRange :=
    map_apply_mem_preimage_opensRange H _ _ _ _ (C.ps.trans hjV'p.symm) _
  obtain ⟨U', jU', -, hjU', hjU'c, hjU'p, hrangeU'⟩ :=
    exists_affine_refinement B S hS C.U'
      ((H.map C.r) ⁻¹ᵁ (H.map jU).opensRange ⊓
        (H.map C.s) ⁻¹ᵁ (H.map jV').opensRange) ⟨hrU, hsV'⟩
  have := hjU'
  obtain ⟨r, hr⟩ := exists_lift_of_range_subset B S hS jU (jU' ≫ C.r) (by
    rintro _ ⟨z, rfl⟩
    exact (hrangeU' ⟨z, rfl⟩).1)
  obtain ⟨s, hs⟩ := exists_lift_of_range_subset B S hS jV' (jU' ≫ C.s) (by
    rintro _ ⟨z, rfl⟩
    exact (hrangeU' ⟨z, rfl⟩).2)
  have hcomm : r ≫ p = s ≫ q := by
    apply (cancel_mono jV).mp
    rw [Category.assoc, hp, Category.assoc, hq, ← Category.assoc, hr,
      ← Category.assoc, hs, Category.assoc, C.comm, ← Category.assoc]
  refine ⟨{ U := U, V := V, U' := U', V' := V'
            p := p, q := q, r := r, s := s
            hp := hom_comp_of_refinement yoneda hp hjUc hjVc C.hp
            hq := hom_comp_of_refinement yoneda hq hjV'c hjVc C.hq
            hr := hom_comp_of_refinement yoneda hr hjU'c hjUc C.hr
            hs := hom_comp_of_refinement yoneda hs hjU'c hjV'c C.hs
            pp := point_comp_of_refinement hp hjUp hjVp C.pp
            pq := point_comp_of_refinement hq hjV'p hjVp C.pq
            pr := point_comp_of_refinement hr hjU'p hjUp C.pr
            ps := point_comp_of_refinement hs hjU'p hjV'p C.ps
            comm := hcomm }, hU, hV, hV', ?_⟩
  exact weaklyEtale_pullbackLift_of_cartesian_cube hC
    (H.map p) (H.map q) (H.map r) (H.map s)
    (H.map jU) (H.map jV) (H.map jV') (H.map jU')
    (by simpa only [Functor.map_comp] using congrArg H.map hp)
    (by simpa only [Functor.map_comp] using congrArg H.map hq)
    (by simpa only [Functor.map_comp] using congrArg H.map hr)
    (by simpa only [Functor.map_comp] using congrArg H.map hs)
    (by simpa only [Functor.map_comp] using congrArg H.map hcomm)

/-! ### The canonical homomorphisms of étale local rings, read on spectra -/

/-- The canonical morphism from the strict henselization of a scheme at a geometric point acts
on global sections by the ordinary-to-étale germ map, read through the identification of the
global sections of a spectrum with the ring. -/
theorem strictHenselizationToBase_appTop (E : BigEtaleSite.{u}) (X : Scheme.{u})
    (hX : E.Contains X) (x : _root_.AlgebraicGeometry.GeometricPoint X) :
    (strictHenselizationToBase E X hX x).appTop ≫
        (Scheme.ΓSpecIso (.of ↥(_root_.AlgebraicGeometry.etaleLocalRing E X hX x))).hom =
      X.presheaf.germ ⊤ (x.hom (closedPoint x.residueField)) trivial ≫
        CommRingCat.ofHom (structureSheafStalkFromLocalRing E X hX x) := by
  simp only [strictHenselizationToBase, Scheme.Hom.comp_appTop,
    Scheme.fromSpecStalk_appTop, Category.assoc]
  simp only [homOfLE_refl, op_id, Scheme.ΓSpecIso_naturality]
  rw [(Spec (X.presheaf.stalk (x.hom (closedPoint x.residueField)))).presheaf.map_id]
  simp only [Category.id_comp]
  exact congrArg (X.presheaf.germ ⊤ (x.hom (closedPoint x.residueField)) trivial ≫ ·)
    ((Scheme.ΓSpecIso (X.presheaf.stalk
      (x.hom (closedPoint x.residueField)))).inv_hom_id_assoc
      (CommRingCat.ofHom (structureSheafStalkFromLocalRing E X hX x)))

/-- **A homomorphism of étale local rings compatible with chart germs is compatible with the
strict henselizations of the charts.** Let `U` and `V` be small étale neighbourhoods of
geometric points of two algebraic spaces, with `V` affine, let `k : U ⟶ V` be a morphism of
their charts, and let `ψ` be a homomorphism of the two étale local rings carrying the germ of
a global section of `V` to the germ of its pullback along `k`.  Then the spectrum of `ψ`, read
through the identification of Stacks 04KF of the two étale local rings with those of the chart
schemes, commutes with the canonical morphisms of Stacks 03PS and with `k`.

Affineness of `V` is what makes the two morphisms comparable: they agree on global sections
because `ψ` does on germs of global sections of `V`, and a morphism into an affine scheme is
determined by its action on global sections. -/
theorem spec_etaleLocalRingGerm_comp {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    {x : GeometricPoint B S hS F} {y : GeometricPoint B S hS G}
    (U : SmallEtaleNeighborhood x) (V : SmallEtaleNeighborhood y)
    (k : U.chart.obj.left ⟶ V.chart.obj.left)
    (ψ : etaleLocalRing B S hS G y →+* etaleLocalRing B S hS F x)
    (hψ : ∀ a, ψ (etaleLocalRingGerm B S hS G y (Opposite.op V) a) =
      etaleLocalRingGerm B S hS F x (Opposite.op U)
        (((BigFppfOver.toScheme B S hS).map k).appTop a))
    (E : BigEtaleSite.{u}) (hU : E.Contains (neighborhoodChartScheme U))
    (hV : E.Contains (neighborhoodChartScheme V))
    [IsAffine (neighborhoodChartScheme V)] :
    Spec.map (CommRingCat.ofHom ((etaleLocalRingEquivChart hF U E hU).1.toRingHom.comp
          (ψ.comp (etaleLocalRingEquivChart hG V E hV).1.symm.toRingHom))) ≫
        strictHenselizationToBase E (neighborhoodChartScheme V) hV (chartGeometricPoint V) =
      strictHenselizationToBase E (neighborhoodChartScheme U) hU (chartGeometricPoint U) ≫
        (BigFppfOver.toScheme B S hS).map k := by
  let eU := (etaleLocalRingEquivChart hF U E hU).1
  let eV := (etaleLocalRingEquivChart hG V E hV).1
  apply ext_of_isAffine
  apply (cancel_mono (Scheme.ΓSpecIso (.of ↥(_root_.AlgebraicGeometry.etaleLocalRing E
    (neighborhoodChartScheme U) hU (chartGeometricPoint U)))).hom).mp
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, ← Category.assoc, strictHenselizationToBase_appTop]
  simp only [Category.assoc]
  rw [strictHenselizationToBase_appTop]
  apply ConcreteCategory.hom_ext
  intro a
  have hu := (etaleLocalRingEquivChart hF U E hU).2.1
    (((BigFppfOver.toScheme B S hS).map k).appTop a)
  have hv := (etaleLocalRingEquivChart hG V E hV).2.1 a
  change eU (ψ (eV.symm ((structureSheafStalkFromLocalRing E
      (neighborhoodChartScheme V) hV (chartGeometricPoint V))
        ((neighborhoodChartScheme V).presheaf.germ ⊤
          ((chartGeometricPoint V).hom
            (closedPoint (chartGeometricPoint V).residueField))
          trivial a)))) =
    (structureSheafStalkFromLocalRing E
      (neighborhoodChartScheme U) hU (chartGeometricPoint U))
        ((neighborhoodChartScheme U).presheaf.germ ⊤
          ((chartGeometricPoint U).hom
            (closedPoint (chartGeometricPoint U).residueField))
          trivial (((BigFppfOver.toScheme B S hS).map k).appTop a))
  rw [← hv, ← hu]
  change eU (ψ (eV.symm (eV _))) = eU _
  rw [eV.symm_apply_apply]
  exact congrArg eU (hψ a)

/-- **The canonical homomorphism of étale local rings of Stacks 04NG, read on spectra.** For a
commuting diagram of pointed étale charts over a morphism `f` of algebraic spaces whose chart
of the target is affine, the spectrum of the canonical homomorphism of étale local rings — read
through the identification of Stacks 04KF with the étale local rings of the chart schemes —
commutes with the canonical morphisms from the strict henselizations of Stacks 03PS. -/
theorem spec_etaleLocalRingMap_comp {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (x : GeometricPoint B S hS F) (U : SmallEtaleNeighborhood x)
    (V : SmallEtaleNeighborhood (geometricPointMap f x))
    (k : U.chart.obj.left ⟶ V.chart.obj.left)
    (hk : U.chart.obj.hom ≫ f = yoneda.map k ≫ V.chart.obj.hom)
    (hx : U.point ≫ k = V.point)
    (E : BigEtaleSite.{u}) (hU : E.Contains (neighborhoodChartScheme U))
    (hV : E.Contains (neighborhoodChartScheme V))
    [IsAffine (neighborhoodChartScheme V)] :
    Spec.map (CommRingCat.ofHom ((etaleLocalRingEquivChart hF U E hU).1.toRingHom.comp
          ((etaleLocalRingMap hF f x).comp
            (etaleLocalRingEquivChart hG V E hV).1.symm.toRingHom))) ≫
        strictHenselizationToBase E (neighborhoodChartScheme V) hV (chartGeometricPoint V) =
      strictHenselizationToBase E (neighborhoodChartScheme U) hU (chartGeometricPoint U) ≫
        (BigFppfOver.toScheme B S hS).map k :=
  spec_etaleLocalRingGerm_comp B S hS hF hG U V k (etaleLocalRingMap hF f x)
    (fun a => (RingHom.congr_fun
      (etaleLocalRingMap_isEtaleLocalRingMap hF f x U V k hk hx) a).symm) E hU hV

/-- The canonical homomorphism of étale local rings of Stacks 04NG, transported along an
equality of the inducing morphisms. -/
theorem etaleLocalRingMap_eq_of_hom_eq {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {m m' : F ⟶ G} (hm : m = m')
    (x : GeometricPoint B S hS F) :
    etaleLocalRingMap hF m x =
      (etaleLocalRingMap hF m' x).comp
        (eqToHom (congrArg (fun t : F ⟶ G =>
          etaleLocalRing B S hS G (geometricPointMap t x)) hm)).hom := by
  subst hm
  simp

/-- The canonical homomorphism of étale local rings along the second factor of a factorisation,
transported along that factorisation, carries germs of global chart sections to germs of their
pullbacks, in any commuting diagram of pointed étale charts over the second factor. -/
theorem etaleLocalRingMap_comp_eqToHom_germ {X Y Z : AlgebraicSpaces B S hS}
    (a : X ⟶ Y) (b : X ⟶ Z) (c : Z ⟶ Y) (habc : a = b ≫ c)
    (x : GeometricPoint B S hS X.1)
    (U : SmallEtaleNeighborhood (geometricPointMap b.hom x))
    (V : SmallEtaleNeighborhood (geometricPointMap a.hom x))
    (k : U.chart.obj.left ⟶ V.chart.obj.left)
    (hk : U.chart.obj.hom ≫ c.hom = yoneda.map k ≫ V.chart.obj.hom)
    (hx : U.point ≫ k = V.point) (s : Γ(neighborhoodChartScheme V, ⊤)) :
    ((etaleLocalRingMap Z.2 c.hom (geometricPointMap b.hom x)).comp
        (eqToHom (congrArg (fun t : X ⟶ Y =>
          etaleLocalRing B S hS Y.1 (geometricPointMap t.hom x)) habc)).hom)
        (etaleLocalRingGerm B S hS Y.1 (geometricPointMap a.hom x) (Opposite.op V) s) =
      etaleLocalRingGerm B S hS Z.1 (geometricPointMap b.hom x) (Opposite.op U)
        (((BigFppfOver.toScheme B S hS).map k).appTop s) := by
  subst habc
  exact (RingHom.congr_fun (etaleLocalRingMap_isEtaleLocalRingMap Z.2 c.hom
    (geometricPointMap b.hom x) U V k hk hx) s).symm

/-! ### The étale local ring of the upper-left corner of a cartesian square -/

/-- **The étale local ring of the upper-left corner of a cartesian square of algebraic spaces
is weakly étale over the tensor product.** Let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square of algebraic spaces over `S` and let `x̄'` be a geometric point of `X'`,
with images `x̄` in `X`, `ȳ'` in `Y'` and `ȳ` in `Y`.  There is a homomorphism

`𝒪_{X,x̄} ⊗_{𝒪_{Y,ȳ}} 𝒪_{Y',ȳ'} ⟶ 𝒪_{X',x̄'}`

restricting on the two factors to the canonical homomorphisms of étale local rings of
Stacks 04NG, and it is weakly étale.

The homomorphism is the one induced by the two canonical homomorphisms out of `𝒪_{X,x̄}` and
`𝒪_{Y',ȳ'}`, which commute because the canonical homomorphisms of Stacks 04NG compose.

Weak étaleness is read on a square of pointed étale charts of the four corners whose three lower
charts are affine.  Over such a square the four étale local rings are the strict
henselizations of Stacks 03PS of the local rings of the charts, the four canonical morphisms
from those strict henselizations are weakly étale by Stacks 0993, and the comparison morphism
from the chart of `X'` to the fibre product of the charts of `X` and `Y'` over the chart of `Y`
is weakly étale as well.  Hence so is
`Spec 𝒪_{X',x̄'} ⟶ Spec (𝒪_{X,x̄} ⊗_{𝒪_{Y,ȳ}} 𝒪_{Y',ȳ'})`. -/
theorem cartesian_etaleStalk_tensor_weaklyEtale {X' X Y' Y : AlgebraicSpaces B S hS}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hpb : IsPullback g' f' f g) (x' : GeometricPoint B S hS X'.1) :
    let h : geometricPointMap f.hom (geometricPointMap g'.hom x') =
        geometricPointMap g.hom (geometricPointMap f'.hom x') :=
      congrArg (fun k : X' ⟶ Y => geometricPointMap k.hom x') hpb.w
    letI : Algebra
        ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
        ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) :=
      (etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x')).toAlgebra
    letI : Algebra
        ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
        ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) :=
      ((eqToHom (congrArg (etaleLocalRing B S hS Y.1) h) ≫
        CommRingCat.ofHom
          (etaleLocalRingMap Y'.2 g.hom (geometricPointMap f'.hom x'))).hom).toAlgebra
    ∃ φ : TensorProduct
        ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
        ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
        ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) →+*
        ↥(etaleLocalRing B S hS X'.1 x'),
      φ.comp Algebra.TensorProduct.includeLeftRingHom = etaleLocalRingMap X'.2 g'.hom x' ∧
        φ.comp Algebra.TensorProduct.includeRight.toRingHom =
          etaleLocalRingMap X'.2 f'.hom x' ∧
        @Algebra.WeaklyEtale _ _ _ _ φ.toAlgebra := by
  have hw : g'.hom ≫ f.hom = f'.hom ≫ g.hom := congrArg (fun k : X' ⟶ Y => k.hom) hpb.w
  have h : geometricPointMap f.hom (geometricPointMap g'.hom x') =
      geometricPointMap g.hom (geometricPointMap f'.hom x') :=
    congrArg (fun k : X' ⟶ Y => geometricPointMap k.hom x') hpb.w
  -- the four canonical homomorphisms of étale local rings of the square
  let α := etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x')
  let β := ((eqToHom (congrArg (etaleLocalRing B S hS Y.1) h) ≫
    CommRingCat.ofHom
      (etaleLocalRingMap Y'.2 g.hom (geometricPointMap f'.hom x'))).hom)
  let γ := etaleLocalRingMap X'.2 g'.hom x'
  let δ := etaleLocalRingMap X'.2 f'.hom x'
  let instA : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) := α.toAlgebra
  let instR' : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x')) := β.toAlgebra
  let instAA' : Algebra ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
      ↥(etaleLocalRing B S hS X'.1 x') := γ.toAlgebra
  let instR'A' : Algebra ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x'))
      ↥(etaleLocalRing B S hS X'.1 x') := δ.toAlgebra
  let instRA' : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X'.1 x') := (γ.comp α).toAlgebra
  -- the square of canonical homomorphisms commutes, because they compose
  have hsquare : ∀ z, γ (α z) = δ (β z) := by
    intro z
    refine (RingHom.congr_fun (etaleLocalRingMap_comp X'.2 X.2 g'.hom f.hom x') z).trans ?_
    refine (RingHom.congr_fun (etaleLocalRingMap_eq_of_hom_eq B S hS X'.2 hw x') z).trans ?_
    exact (RingHom.congr_fun
      (etaleLocalRingMap_comp X'.2 Y'.2 f'.hom g.hom x') _).symm
  have tower₁ : IsScalarTower
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
      ↥(etaleLocalRing B S hS X'.1 x') := IsScalarTower.of_algebraMap_eq' rfl
  have tower₂ : IsScalarTower
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x'))
      ↥(etaleLocalRing B S hS X'.1 x') :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext hsquare)
  -- the induced homomorphism out of the tensor product
  let τ := Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
      ↥(etaleLocalRing B S hS X'.1 x'))
    (IsScalarTower.toAlgHom
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x'))
      ↥(etaleLocalRing B S hS X'.1 x'))
    (fun _ _ => Commute.all _ _)
  have hleft : τ.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom = γ := by
    refine RingHom.ext fun a => ?_
    change γ a * δ 1 = γ a
    rw [map_one, mul_one]
  have hright : τ.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom = δ := by
    refine RingHom.ext fun c => ?_
    change γ 1 * δ c = δ c
    rw [map_one, one_mul]
  refine ⟨τ.toRingHom, hleft, hright, ?_⟩
  -- a pointed square of étale charts with affine lower corners
  obtain ⟨C, hUaff, hVaff, hV'aff, hC⟩ := exists_affine_pointedChartSquare B S hS hpb x'
  have := hUaff
  have := hVaff
  have := hV'aff
  let E := bigEtaleSiteOfFppfSite B
  have cU : E.Contains (neighborhoodChartScheme C.U) := C.U.chart.obj.left.left.property
  have cV : E.Contains (neighborhoodChartScheme C.V) := C.V.chart.obj.left.left.property
  have cV' : E.Contains (neighborhoodChartScheme C.V') := C.V'.chart.obj.left.left.property
  have cU' : E.Contains (neighborhoodChartScheme C.U') := C.U'.chart.obj.left.left.property
  -- the four étale local rings of the chart schemes, and the identifications of Stacks 04KF
  let eU := (etaleLocalRingEquivChart X.2 C.U E cU).1
  let eV := (etaleLocalRingEquivChart Y.2 C.V E cV).1
  let eV' := (etaleLocalRingEquivChart Y'.2 C.V' E cV').1
  let eU' := (etaleLocalRingEquivChart X'.2 C.U' E cU').1
  let αs := eU.toRingHom.comp (α.comp eV.symm.toRingHom)
  let βs := eV'.toRingHom.comp (β.comp eV.symm.toRingHom)
  let γs := eU'.toRingHom.comp (γ.comp eU.symm.toRingHom)
  let δs := eU'.toRingHom.comp (δ.comp eV'.symm.toRingHom)
  let instαs : Algebra
      ↥(_root_.AlgebraicGeometry.etaleLocalRing E (neighborhoodChartScheme C.V) cV
        (chartGeometricPoint C.V))
      ↥(_root_.AlgebraicGeometry.etaleLocalRing E (neighborhoodChartScheme C.U) cU
        (chartGeometricPoint C.U)) := αs.toAlgebra
  let instβs : Algebra
      ↥(_root_.AlgebraicGeometry.etaleLocalRing E (neighborhoodChartScheme C.V) cV
        (chartGeometricPoint C.V))
      ↥(_root_.AlgebraicGeometry.etaleLocalRing E (neighborhoodChartScheme C.V') cV'
        (chartGeometricPoint C.V')) := βs.toAlgebra
  have hαs : ∀ r, eU (algebraMap _ _ r) = algebraMap _ _ (eV r) := by
    intro r
    change eU (α r) = eU (α (eV.symm (eV r)))
    rw [eV.symm_apply_apply]
  have hβs : ∀ r, eV' (algebraMap _ _ r) = algebraMap _ _ (eV r) := by
    intro r
    change eV' (β r) = eV' (β (eV.symm (eV r)))
    rw [eV.symm_apply_apply]
  let eP := tensorRingCongr eV eU eV' hαs hβs
  let τs := eU'.toRingHom.comp (τ.toRingHom.comp eP.symm.toRingHom)
  have hτγ : τs.comp Algebra.TensorProduct.includeLeftRingHom = γs := by
    refine RingHom.ext fun w => ?_
    change eU' (τ (eP.symm (w ⊗ₜ 1))) = eU' (γ (eU.symm w))
    rw [tensorRingCongr_symm_tmul]
    simp only [map_one]
    change eU' (γ (eU.symm w) * δ 1) = _
    rw [map_one, mul_one]
  have hτδ : τs.comp Algebra.TensorProduct.includeRight.toRingHom = δs := by
    refine RingHom.ext fun w => ?_
    change eU' (τ (eP.symm (1 ⊗ₜ w))) = eU' (δ (eV'.symm w))
    rw [tensorRingCongr_symm_tmul]
    simp only [map_one]
    change eU' (γ 1 * δ (eV'.symm w)) = _
    rw [map_one, one_mul]
  -- the four weakly étale morphisms from the strict henselizations of the charts
  let sa := strictHenselizationToBase E (neighborhoodChartScheme C.U) cU
    (chartGeometricPoint C.U)
  let sb := strictHenselizationToBase E (neighborhoodChartScheme C.V) cV
    (chartGeometricPoint C.V)
  let sc := strictHenselizationToBase E (neighborhoodChartScheme C.V') cV'
    (chartGeometricPoint C.V')
  let sd := strictHenselizationToBase E (neighborhoodChartScheme C.U') cU'
    (chartGeometricPoint C.U')
  have wa : WeaklyEtale sa := weaklyEtale_strictHenselizationToBase E _ cU _
  have wb : WeaklyEtale sb := weaklyEtale_strictHenselizationToBase E _ cV _
  have wc : WeaklyEtale sc := weaklyEtale_strictHenselizationToBase E _ cV' _
  have wd : WeaklyEtale sd := weaklyEtale_strictHenselizationToBase E _ cU' _
  have hp : Spec.map (CommRingCat.ofHom αs) ≫ sb =
      sa ≫ (BigFppfOver.toScheme B S hS).map C.p :=
    spec_etaleLocalRingMap_comp B S hS X.2 Y.2 f.hom (geometricPointMap g'.hom x')
      C.U C.V C.p C.hp C.pp E cU cV
  have hq : Spec.map (CommRingCat.ofHom βs) ≫ sb =
      sc ≫ (BigFppfOver.toScheme B S hS).map C.q :=
    spec_etaleLocalRingGerm_comp B S hS Y'.2 Y.2 C.V' C.V C.q β
      (fun a => etaleLocalRingMap_comp_eqToHom_germ B S hS (g' ≫ f) f' g hpb.w x'
        C.V' C.V C.q C.hq C.pq a) E cV' cV
  have hr : Spec.map (CommRingCat.ofHom γs) ≫ sa =
      sd ≫ (BigFppfOver.toScheme B S hS).map C.r :=
    spec_etaleLocalRingMap_comp B S hS X'.2 X.2 g'.hom x' C.U' C.U C.r C.hr C.pr E cU' cU
  have hs : Spec.map (CommRingCat.ofHom δs) ≫ sc =
      sd ≫ (BigFppfOver.toScheme B S hS).map C.s :=
    spec_etaleLocalRingMap_comp B S hS X'.2 Y'.2 f'.hom x' C.U' C.V' C.s C.hs C.ps E cU' cV'
  -- the comparison morphism to the fibre product of the two lower charts
  let j := pullback.lift (f := (BigFppfOver.toScheme B S hS).map C.p)
    (g := (BigFppfOver.toScheme B S hS).map C.q)
    ((BigFppfOver.toScheme B S hS).map C.r) ((BigFppfOver.toScheme B S hS).map C.s)
    (by simpa only [Functor.map_comp] using
      congrArg (BigFppfOver.toScheme B S hS).map C.comm)
  have wj : WeaklyEtale j := hC
  have hj₁ : j ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map C.p)
      ((BigFppfOver.toScheme B S hS).map C.q) = (BigFppfOver.toScheme B S hS).map C.r :=
    pullback.lift_fst _ _ _
  have hj₂ : j ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map C.p)
      ((BigFppfOver.toScheme B S hS).map C.q) = (BigFppfOver.toScheme B S hS).map C.s :=
    pullback.lift_snd _ _ _
  have hwe : @Algebra.WeaklyEtale _ _ _ _ τs.toAlgebra :=
    tensorProductMap_weaklyEtale_of_cartesian_cube
    ↥(_root_.AlgebraicGeometry.etaleLocalRing E (neighborhoodChartScheme C.V) cV
      (chartGeometricPoint C.V))
    ↥(_root_.AlgebraicGeometry.etaleLocalRing E (neighborhoodChartScheme C.U) cU
      (chartGeometricPoint C.U))
    ↥(_root_.AlgebraicGeometry.etaleLocalRing E (neighborhoodChartScheme C.V') cV'
      (chartGeometricPoint C.V'))
    ↥(_root_.AlgebraicGeometry.etaleLocalRing E (neighborhoodChartScheme C.U') cU'
      (chartGeometricPoint C.U'))
    (IsPullback.of_hasPullback ((BigFppfOver.toScheme B S hS).map C.p)
      ((BigFppfOver.toScheme B S hS).map C.q))
    sa sb sc (sd ≫ j) hp hq τs
    (by rw [hτγ, hr, Category.assoc, hj₁]) (by rw [hτδ, hs, Category.assoc, hj₂])
  exact weaklyEtale_of_comp_ringEquiv τ.toRingHom eP.symm eU' hwe

/-- **The étale local ring of the upper-left corner of a cartesian square of algebraic spaces
is flat over the tensor product.** Let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square of algebraic spaces over `S` and let `x̄'` be a geometric point of `X'`,
with images `x̄` in `X`, `ȳ'` in `Y'` and `ȳ` in `Y`.  There is a homomorphism

`𝒪_{X,x̄} ⊗_{𝒪_{Y,ȳ}} 𝒪_{Y',ȳ'} ⟶ 𝒪_{X',x̄'}`

restricting on the two factors to the canonical homomorphisms of étale local rings of
Stacks 04NG, and it is flat.

This is the geometric input to Stacks 0DKD at a geometric point, and the algebraic-spaces
analogue of `AlgebraicGeometry.BaseChangeStalk.cartesian_stalk_tensor_flat`.  The homomorphism
is the one induced by the two canonical homomorphisms out of `𝒪_{X,x̄}` and `𝒪_{Y',ȳ'}`, which
commute because the canonical homomorphisms of Stacks 04NG compose.

Flatness is read on a square of pointed étale charts of the four corners whose three lower
charts are affine.  Over such a square the four étale local rings are the strict
henselizations of Stacks 03PS of the local rings of the charts, the four canonical morphisms
from those strict henselizations are weakly étale by Stacks 0993, and the comparison morphism
from the chart of `X'` to the fibre product of the charts of `X` and `Y'` over the chart of `Y`
is weakly étale as well.  Hence so is
`Spec 𝒪_{X',x̄'} ⟶ Spec (𝒪_{X,x̄} ⊗_{𝒪_{Y,ȳ}} 𝒪_{Y',ȳ'})`, and a weakly étale morphism is
flat. -/
theorem cartesian_etaleStalk_tensor_flat {X' X Y' Y : AlgebraicSpaces B S hS}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hpb : IsPullback g' f' f g) (x' : GeometricPoint B S hS X'.1) :
    IsEtaleStalkTensorFlat g' f' f g hpb x' := by
  obtain ⟨φ, hl, hr, hw⟩ := cartesian_etaleStalk_tensor_weaklyEtale B S hS g' f' f g hpb x'
  refine ⟨φ, hl, hr, ?_⟩
  let := φ.toAlgebra
  exact RingHom.flat_algebraMap_iff.mpr hw.flat

end AlgebraicGeometry.Space

end
