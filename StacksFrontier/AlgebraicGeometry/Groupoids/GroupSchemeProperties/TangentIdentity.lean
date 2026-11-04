module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.TangentProduct

/-!
# The differential of multiplication at the identity of a group scheme

For a group scheme over a base, the differential of the multiplication morphism at the pair of
identity points is addition of relative tangent vectors, through the canonical decomposition of
the tangent space of a fibre product as a product of tangent spaces.

## Main results

* `AlgebraicGeometry.tangentMap_mul_at_identity`: the tangent map of multiplication at the
  identity is addition.
* `AlgebraicGeometry.residueFieldMap_eq_residueFieldCongr_of_fixed`: at a fixed point of an
  endomorphism over the base, its residue-field map is the canonical identification.
* `AlgebraicGeometry.tangentMap_fixed_apply`, `AlgebraicGeometry.tangentMap_transport_apply`,
  `AlgebraicGeometry.tangentMap_transport_apply_eq`: the dual-number arrow underlying a
  derivative transported back along a point equality is the arrow composed with the morphism.

## Implementation notes

The identity point and the corresponding point of the fibre product come from the unit morphism
of the group object.  The statement carries with it the canonical point equalities and the
residue-field isomorphisms needed to type the two tangent maps and the product equivalence;
these are consequences of the group-object laws, not extra hypotheses.

The two summands are treated separately: on the first factor the second coordinate of the
lifted arrow is the constant arrow at the identity, so the multiplication morphism returns the
first coordinate, and symmetrically on the second factor.

## References

* [Stacks Project, Tag 0BF5](https://stacks.math.columbia.edu/tag/0BF5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

private theorem residueFieldMap_congr_after_common_map
    {P X S : Scheme.{u}} (i : X ⟶ S) (a b : P ⟶ X)
    (z : P) (y : X) (hab : a ≫ i = b ≫ i)
    (ha : a z = y) (hb : b z = y)
    [IsIso (i.residueFieldMap y)] :
    (X.residueFieldCongr ha).inv ≫ a.residueFieldMap z =
      (X.residueFieldCongr hb).inv ≫ b.residueFieldMap z := by
  let cA := X.residueFieldCongr ha
  let cB := X.residueFieldCongr hb
  let cSA := S.residueFieldCongr (congrArg i ha)
  let cSB := S.residueFieldCongr (congrArg i hb)
  have hGA : i.residueFieldMap (a z) = cSA.hom ≫ i.residueFieldMap y ≫ cA.inv := by
    calc
      i.residueFieldMap (a z) =
          (i.residueFieldMap (a z) ≫ cA.hom) ≫ cA.inv := by simp [Category.assoc]
      _ = (cSA.hom ≫ i.residueFieldMap y) ≫ cA.inv := by
        rw [Scheme.Hom.residueFieldMap_congr' (f := i) ha]
      _ = cSA.hom ≫ i.residueFieldMap y ≫ cA.inv := by simp
  have hGB : i.residueFieldMap (b z) = cSB.hom ≫ i.residueFieldMap y ≫ cB.inv := by
    calc
      i.residueFieldMap (b z) =
          (i.residueFieldMap (b z) ≫ cB.hom) ≫ cB.inv := by simp [Category.assoc]
      _ = (cSB.hom ≫ i.residueFieldMap y) ≫ cB.inv := by
        rw [Scheme.Hom.residueFieldMap_congr' (f := i) hb]
      _ = cSB.hom ≫ i.residueFieldMap y ≫ cB.inv := by simp
  have hbasez : (a ≫ i) z = (b ≫ i) z := by
    simpa using congrArg i (ha.trans hb.symm)
  have hpath : cSA.hom = (S.residueFieldCongr hbasez).hom ≫ cSB.hom :=
    (Scheme.residueFieldCongr_trans_hom S hbasez (congrArg i hb)).symm
  have hcomp : (a ≫ i).residueFieldMap z =
      (S.residueFieldCongr hbasez).hom ≫ (b ≫ i).residueFieldMap z := by
    simpa [hbasez] using Scheme.Hom.residueFieldMap_congr hab z
  rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp, hGA, hGB] at hcomp
  have hcomp' : i.residueFieldMap y ≫ cA.inv ≫ a.residueFieldMap z =
      i.residueFieldMap y ≫ cB.inv ≫ b.residueFieldMap z := by
    simpa [Category.assoc, hpath] using hcomp
  exact (cancel_epi (i.residueFieldMap y)).1 hcomp'

private theorem tangentArrow_cast_add {X S : Scheme.{u}} (f : X ⟶ S)
    {x y : X} (h : x = y) (v w : DottedTangentArrow f x) :
    h ▸ (v + w) = (h ▸ v) + (h ▸ w) := by
  cases h
  rfl

private theorem tangentArrow_cast_val {X S : Scheme.{u}} (f : X ⟶ S)
    {x y : X} (h : x = y) (v : DottedTangentArrow f x) :
    (h ▸ v).val =
      Spec.map (CommRingCat.ofHom (dualNumberCongr
        (X.residueFieldCongr h).commRingCatIsoToRingEquiv).toRingHom) ≫ v.val := by
  cases h
  have hring : (dualNumberCongr
      (X.residueFieldCongr (rfl : x = x)).commRingCatIsoToRingEquiv).toRingHom =
      RingHom.id _ :=
    RingHom.ext fun ⟨_, _⟩ => rfl
  show v.val = Spec.map (CommRingCat.ofHom
    (dualNumberCongr
      (X.residueFieldCongr (rfl : x = x)).commRingCatIsoToRingEquiv).toRingHom) ≫ v.val
  rw [hring]
  simp

/-- At a fixed point `x` of an endomorphism `f` of `X` over `S`, the residue-field map of `f` is
the canonical identification of `κ(f x)` with `κ(x)`, provided the structure morphism does not
change the residue field at `x`. -/
theorem residueFieldMap_eq_residueFieldCongr_of_fixed {X S : Scheme.{u}} (p : X ⟶ S)
    (f : X ⟶ X) (hbase : f ≫ p = p) (x : X) (hfix : f x = x) [IsIso (p.residueFieldMap x)] :
    f.residueFieldMap x = (X.residueFieldCongr hfix).hom := by
  have hcommon := residueFieldMap_congr_after_common_map p f (𝟙 X) x x
    (by simpa using hbase) hfix rfl
  simpa using congrArg (fun arrow => (X.residueFieldCongr hfix).hom ≫ arrow) hcommon

/-- The dual-number arrow underlying the derivative, at a fixed point, of an endomorphism over
the base: it is the arrow composed with the endomorphism. -/
theorem tangentMap_fixed_apply {X S : Scheme.{u}} (p : X ⟶ S) (f : X ⟶ X)
    (hbase : f ≫ p = p) (x : X) (hfix : f x = x) [IsIso (p.residueFieldMap x)]
    [IsIso (f.residueFieldMap x)] (θ : DottedTangentArrow p x) :
    (hfix ▸ tangentMap f p p hbase x θ).val = θ.val ≫ f := by
  have hmap := residueFieldMap_eq_residueFieldCongr_of_fixed p f hbase x hfix
  let α : DualNumber (X.residueField x) →+* DualNumber (X.residueField (f x)) :=
    (dualNumberCongr (X.residueFieldCongr hfix).commRingCatIsoToRingEquiv.symm).toRingHom
  have hα : inv (f.residueFieldMap x) = (X.residueFieldCongr hfix).inv := by
    apply (cancel_epi (f.residueFieldMap x)).mp
    simp [hmap]
  rw [tangentArrow_cast_val, tangentMap_apply f p p hbase x θ α
    (fun _ => by rw [hα]; rfl) (fun _ => by rw [hα]; rfl), ← Spec.map_comp_assoc]
  have hid : CommRingCat.ofHom α ≫ CommRingCat.ofHom
      (dualNumberCongr
        (X.residueFieldCongr hfix).commRingCatIsoToRingEquiv).toRingHom = 𝟙 _ := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun value => TrivSqZeroExt.ext ?_ ?_
    · exact (X.residueFieldCongr hfix).commRingCatIsoToRingEquiv.apply_symm_apply value.fst
    · exact (X.residueFieldCongr hfix).commRingCatIsoToRingEquiv.apply_symm_apply value.snd
  rw [hid]
  simp

/-- The dual-number arrow underlying a derivative transported along the equality of its base
point with a named point. -/
theorem tangentMap_transport_apply {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
    (hbase : f ≫ q = p) (x : X) (y : Y) (hxy : f x = y)
    [IsIso (f.residueFieldMap x)] (θ : DottedTangentArrow p x) :
    (hxy ▸ tangentMap f p q hbase x θ).val =
      Spec.map (CommRingCat.ofHom
        (dualNumberCongr
          (asIso ((Y.residueFieldCongr hxy).inv ≫
            f.residueFieldMap x)).commRingCatIsoToRingEquiv.symm).toRingHom) ≫
        θ.val ≫ f := by
  let α := (dualNumberCongr
    (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv.symm).toRingHom
  rw [tangentArrow_cast_val, tangentMap_apply f p q hbase x θ α (fun _ => rfl) (fun _ => rfl),
    ← Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro value
  have hinv : inv ((Y.residueFieldCongr hxy).inv ≫ f.residueFieldMap x) =
      inv (f.residueFieldMap x) ≫ (Y.residueFieldCongr hxy).hom := by simp
  apply TrivSqZeroExt.ext
  · show (Y.residueFieldCongr hxy).hom.hom ((inv (f.residueFieldMap x)).hom value.fst) =
      (inv ((Y.residueFieldCongr hxy).inv ≫ f.residueFieldMap x)).hom value.fst
    rw [hinv]
    rfl
  · show (Y.residueFieldCongr hxy).hom.hom ((inv (f.residueFieldMap x)).hom value.snd) =
      (inv ((Y.residueFieldCongr hxy).inv ≫ f.residueFieldMap x)).hom value.snd
    rw [hinv]
    rfl

/-- Two morphisms into `X` over `S` which agree at a point have derivatives there whose
transported dual-number arrows differ only in the morphism composed on the right. -/
theorem tangentMap_transport_apply_eq {P X S : Scheme.{u}} (i : X ⟶ S) (p : P ⟶ S) (a b : P ⟶ X)
    (haBase : a ≫ i = p) (hbBase : b ≫ i = p) (z : P) (y : X)
    (ha : a z = y) (hb : b z = y) [IsIso (i.residueFieldMap y)]
    [IsIso (a.residueFieldMap z)] [IsIso (b.residueFieldMap z)]
    (θ : DottedTangentArrow p z) :
    (ha ▸ tangentMap a p i haBase z θ).val =
      Spec.map (CommRingCat.ofHom
        (dualNumberCongr
          (asIso ((X.residueFieldCongr hb).inv ≫
            b.residueFieldMap z)).commRingCatIsoToRingEquiv.symm).toRingHom) ≫
        θ.val ≫ a := by
  rw [tangentMap_transport_apply a p i haBase z y ha θ]
  have hfields := residueFieldMap_congr_after_common_map i a b z y
    (haBase.trans hbBase.symm) ha hb
  congr 3
  have hinv : inv ((X.residueFieldCongr ha).inv ≫ a.residueFieldMap z) =
      inv ((X.residueFieldCongr hb).inv ≫ b.residueFieldMap z) := by
    apply (cancel_epi ((X.residueFieldCongr ha).inv ≫ a.residueFieldMap z)).mp
    calc
      ((X.residueFieldCongr ha).inv ≫ a.residueFieldMap z) ≫
          inv ((X.residueFieldCongr ha).inv ≫ a.residueFieldMap z) = 𝟙 _ := by simp
      _ = ((X.residueFieldCongr ha).inv ≫ a.residueFieldMap z) ≫
          inv ((X.residueFieldCongr hb).inv ≫ b.residueFieldMap z) := by
        rw [hfields]; simp
  apply RingHom.ext
  intro value
  apply TrivSqZeroExt.ext
  · show (inv ((X.residueFieldCongr ha).inv ≫ a.residueFieldMap z)).hom value.fst =
      (inv ((X.residueFieldCongr hb).inv ≫ b.residueFieldMap z)).hom value.fst
    rw [hinv]
  · show (inv ((X.residueFieldCongr ha).inv ≫ a.residueFieldMap z)).hom value.snd =
      (inv ((X.residueFieldCongr hb).inv ≫ b.residueFieldMap z)).hom value.snd
    rw [hinv]

private theorem groupMultiplication_lift_unit_right {S A : Scheme.{u}}
    (G : Over S) [GrpObj G] (q : A ⟶ S) (f : A ⟶ G.left)
    (hf : f ≫ G.hom = q) :
    pullback.lift f (q ≫ (η[G]).left)
        (by
          calc
            f ≫ G.hom = q := hf
            _ = q ≫ ((η[G]).left ≫ G.hom) := by rw [Over.Hom.w (η[G])]; simp
            _ = (q ≫ (η[G]).left) ≫ G.hom := by simp [Category.assoc]) ≫
      ((Over.tensorObj_left G G) ▸ (μ[G]).left) = f := by
  show ((pullback.lift f (q ≫ (η[G]).left) _) ≫
      ((Over.tensorObj_left G G) ▸ (μ[G]).left)) = f
  exact congrArg Over.Hom.left
    (MonObj.lift_comp_one_right (Over.homMk f hf : Over.mk q ⟶ G) (toUnit (Over.mk q)))

private theorem groupMultiplication_lift_unit_left {S A : Scheme.{u}}
    (G : Over S) [GrpObj G] (q : A ⟶ S) (f : A ⟶ G.left)
    (hf : f ≫ G.hom = q) :
    pullback.lift (q ≫ (η[G]).left) f
        (by
          calc
            (q ≫ (η[G]).left) ≫ G.hom = q ≫ ((η[G]).left ≫ G.hom) := by
              rw [Category.assoc]
            _ = q := by rw [Over.Hom.w (η[G])]; simp
            _ = f ≫ G.hom := hf.symm) ≫
      ((Over.tensorObj_left G G) ▸ (μ[G]).left) = f := by
  show ((pullback.lift (q ≫ (η[G]).left) f _) ≫
      ((Over.tensorObj_left G G) ▸ (μ[G]).left)) = f
  exact congrArg Over.Hom.left
    (MonObj.lift_comp_one_left (toUnit (Over.mk q)) (Over.homMk f hf : Over.mk q ⟶ G))

private theorem groupMultiplication_lift_second_unit {S A : Scheme.{u}}
    (G : Over S) [GrpObj G] (f g : A ⟶ G.left) (q : A ⟶ S)
    (hf : f ≫ G.hom = q) (hg : g = q ≫ (η[G]).left)
    (hfg : f ≫ G.hom = g ≫ G.hom) :
    (pullback.lift f g hfg) ≫
      ((Over.tensorObj_left G G) ▸ (μ[G]).left) = f := by
  cases hg
  exact groupMultiplication_lift_unit_right G q f hf

/-- A morphism `a` into a group scheme sending `z` to the identity point has the constant arrow
at `a z` equal to the constant arrow at the base point of `a ≫ G.hom` composed with the unit. -/
private theorem constantArrow_factor_unit {S P : Scheme.{u}}
    (G : Over S) [GrpObj G] (a : P ⟶ G.left) (z : P) (s : S)
    (h₁ : a z = (η[G]).left s) :
    dualNumberToBase (P.residueField z) ≫ Spec.map (a.residueFieldMap z) ≫
        G.left.fromSpecResidueField (a z) =
      dualNumberBasePoint (a ≫ G.hom) z ≫ (η[G]).left := by
  let e : G.left := (η[G]).left s
  let y : G.left := a z
  have hp : G.hom e = s := congrArg (fun k : S ⟶ S => k s) (Over.Hom.w (η[G]))
  let d := G.hom.residueFieldMap e
  let c := (η[G]).left.residueFieldMap s
  let hpIso := S.residueFieldCongr hp
  let k := G.left.residueFieldCongr h₁
  let dY := G.hom.residueFieldMap y
  let cY := k.hom ≫ c
  let baseCongr := S.residueFieldCongr (congrArg G.hom h₁)
  let totalCongr := S.residueFieldCongr ((congrArg G.hom h₁).trans hp)
  have : IsIso d := isIso_residueFieldMap_of_mem_range_section G.hom (η[G]).left
    (Over.Hom.w (η[G])) s
  have hcongr : ((η[G]).left ≫ G.hom).residueFieldMap s =
      hpIso.hom ≫ Scheme.Hom.residueFieldMap (𝟙 S) s := by
    simpa [hpIso] using
      (Scheme.Hom.residueFieldMap_congr (Over.Hom.w (η[G])) s)
  have hdc : d ≫ c = hpIso.hom := by
    rw [← Scheme.residueFieldMap_comp (f := (η[G]).left) G.hom s]
    simpa using hcongr
  have hmapD : dY ≫ k.hom = baseCongr.hom ≫ d := by
    simpa [dY, k, baseCongr] using
      (Scheme.Hom.residueFieldMap_congr' (f := G.hom) h₁)
  have : IsIso (dY ≫ k.hom) := by rw [hmapD]; infer_instance
  have : IsIso dY := IsIso.of_isIso_comp_right dY k.hom
  have hdcY : dY ≫ cY = totalCongr.hom := by
    calc
      dY ≫ cY = (dY ≫ k.hom) ≫ c := by simp [cY, Category.assoc]
      _ = (baseCongr.hom ≫ d) ≫ c := by rw [hmapD]
      _ = totalCongr.hom := by
        rw [Category.assoc, hdc]
        show (S.residueFieldCongr (congrArg G.hom h₁)).hom ≫
          (S.residueFieldCongr hp).hom =
          (S.residueFieldCongr ((congrArg G.hom h₁).trans hp)).hom
        exact S.residueFieldCongr_trans_hom (congrArg G.hom h₁) hp
  have : IsIso (dY ≫ cY) := by rw [hdcY]; infer_instance
  have : IsIso cY := IsIso.of_isIso_comp_left dY cY
  have hciY : inv cY = totalCongr.inv ≫ dY := by
    apply (cancel_mono cY).1
    simp [hdcY]
  have hfrom : Spec.map c ≫ G.left.fromSpecResidueField e =
      S.fromSpecResidueField s ≫ (η[G]).left :=
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField
      (f := (η[G]).left) s
  have hfromY : Spec.map cY ≫ G.left.fromSpecResidueField y =
      S.fromSpecResidueField s ≫ (η[G]).left := by
    dsimp [cY]
    rw [Spec.map_comp, Category.assoc,
      Scheme.residueFieldCongr_fromSpecResidueField h₁]
    exact hfrom
  have hfromY' : G.left.fromSpecResidueField y =
      Spec.map (inv cY) ≫ S.fromSpecResidueField s ≫ (η[G]).left := by
    calc
      G.left.fromSpecResidueField y = 𝟙 _ ≫ G.left.fromSpecResidueField y := by simp
      _ = (Spec.map (inv cY) ≫ Spec.map cY) ≫ G.left.fromSpecResidueField y := by simp
      _ = Spec.map (inv cY) ≫ (Spec.map cY ≫ G.left.fromSpecResidueField y) := by simp
      _ = Spec.map (inv cY) ≫ (S.fromSpecResidueField s ≫ (η[G]).left) := by rw [hfromY]
      _ = Spec.map (inv cY) ≫ S.fromSpecResidueField s ≫ (η[G]).left := by simp
  have hfromBase : Spec.map totalCongr.inv ≫ S.fromSpecResidueField s =
      S.fromSpecResidueField ((a ≫ G.hom) z) := by
    simp [totalCongr, Scheme.residueFieldCongr_fromSpecResidueField
      ((congrArg G.hom h₁).trans hp).symm]
  have hsource :
      Spec.map ((a).residueFieldMap z) ≫
        Spec.map (inv cY) ≫ S.fromSpecResidueField s =
      Spec.map ((a ≫ G.hom).residueFieldMap z) ≫
        S.fromSpecResidueField ((a ≫ G.hom) z) := by
    rw [hciY]
    rw [← Spec.map_comp_assoc]
    rw [Category.assoc]
    rw [← Scheme.residueFieldMap_comp]
    rw [AlgebraicGeometry.Spec.map_comp (f := totalCongr.inv)
      (g := (a ≫ G.hom).residueFieldMap z)]
    rw [Category.assoc]
    rw [hfromBase]
    simp [Category.assoc]
  dsimp only [dualNumberBasePoint, dualNumberToBase]
  rw [hfromY']
  simpa only [dualNumberToBase, Category.assoc] using
    congrArg (fun k =>
      dualNumberToBase (P.residueField z) ≫
        k ≫ (η[G]).left) hsource

/-- For two morphisms `a`, `m` over `S` taking `z` to `y`, with `κ(y)` unchanged over `S`, the
residue-field identifications of `κ(a z)`, `κ(m z)` with `κ(y)` induce, on dual numbers, the same
isomorphism between `κ(a z)[ε]` and `κ(m z)[ε]`. -/
private theorem dualNumberCongr_residueFieldCongr_chain {P X S : Scheme.{u}} (i : X ⟶ S)
    (a m : P ⟶ X) (z : P) (y : X) (hbase : m ≫ i = a ≫ i) (hm : m z = y) (ha : a z = y)
    [IsIso (i.residueFieldMap y)] [IsIso (m.residueFieldMap z)] [IsIso (a.residueFieldMap z)] :
    (((dualNumberCongr (X.residueFieldCongr ha.symm).commRingCatIsoToRingEquiv).trans
          (dualNumberCongr (asIso (a.residueFieldMap z)).commRingCatIsoToRingEquiv)).trans
          (dualNumberCongr (asIso (m.residueFieldMap z)).commRingCatIsoToRingEquiv.symm)).trans
          (dualNumberCongr (X.residueFieldCongr hm).commRingCatIsoToRingEquiv) =
      RingEquiv.refl (DualNumber (X.residueField y)) := by
  have hmf := congrArg CommRingCat.Hom.hom
    (residueFieldMap_congr_after_common_map i m a z y hbase hm ha)
  let rM := (X.residueFieldCongr hm).commRingCatIsoToRingEquiv
  let rA := (X.residueFieldCongr ha).commRingCatIsoToRingEquiv
  let qM := (asIso (m.residueFieldMap z)).commRingCatIsoToRingEquiv
  let qA := (asIso (a.residueFieldMap z)).commRingCatIsoToRingEquiv
  have hcast : (X.residueFieldCongr ha.symm).commRingCatIsoToRingEquiv = rA.symm :=
    congrArg (fun e => e.commRingCatIsoToRingEquiv) (Scheme.residueFieldCongr_symm ha)
  have hEquiv : rM.symm.trans qM = rA.symm.trans qA := RingEquiv.ext (RingHom.congr_fun hmf)
  have hdual : ((rA.symm.trans qA).trans qM.symm).trans rM = RingEquiv.refl _ := by
    rw [← hEquiv]
    ext x
    simp [RingEquiv.trans_apply]
  rw [hcast, ← dualNumberCongr_trans, ← dualNumberCongr_trans, ← dualNumberCongr_trans]
  exact congrArg dualNumberCongr hdual

/-- On the first summand of the tangent space of the fibre product at the identity, the
differential of multiplication returns the tangent vector of the first factor: the second
coordinate of the lifted arrow is the constant arrow at the identity. -/
private theorem tangentMap_firstFactor_eq {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S)
    (z : ↑(pullback G.hom G.hom))
    (h₁' : (pullback.fst G.hom G.hom) z = (η[G]).left s)
    (h₂' : (pullback.snd G.hom G.hom) z = (η[G]).left s)
    (hm' : ((Over.tensorObj_left G G) ▸ (μ[G]).left : pullback G.hom G.hom ⟶ G.left) z =
      (η[G]).left s)
    (hbase : ((Over.tensorObj_left G G) ▸ (μ[G]).left : pullback G.hom G.hom ⟶ G.left) ≫ G.hom =
      pullback.fst G.hom G.hom ≫ G.hom)
    (hmiso : IsIso (((Over.tensorObj_left G G) ▸ (μ[G]).left :
      pullback G.hom G.hom ⟶ G.left).residueFieldMap z))
    (E : TangentSpaceProductEquiv G.hom G.hom z)
    (v : DottedTangentArrow G.hom ((η[G]).left s)) :
    have := hmiso
    hm' ▸ tangentMap ((Over.tensorObj_left G G) ▸ (μ[G]).left)
        (pullback.fst G.hom G.hom ≫ G.hom) G.hom hbase z
        (E.toLinearEquiv.symm (h₁'.symm ▸ v, 0)) = v := by
  have := hmiso
  let e : G.left := (η[G]).left s
  let m : pullback G.hom G.hom ⟶ G.left := (Over.tensorObj_left G G) ▸ (μ[G]).left
  have hη : (η[G]).left ≫ G.hom = 𝟙 S := Over.Hom.w (η[G])
  let T := tangentMap m (pullback.fst G.hom G.hom ≫ G.hom) G.hom hbase z
  let a := h₁'.symm ▸ v
  let x₁ := E.toLinearEquiv.symm (a, 0)
  show hm' ▸ T x₁ = v
  apply Subtype.ext
  rw [tangentArrow_cast_val G.hom hm' (T x₁)]
  let em := (asIso (m.residueFieldMap z)).commRingCatIsoToRingEquiv
  let α := (dualNumberCongr em.symm).toRingHom
  rw [tangentMap_apply m (pullback.fst G.hom G.hom ≫ G.hom)
    G.hom hbase z x₁ α (fun _ => rfl) (fun _ => rfl), E.first_inclusion_apply a]
  have := E.fst_residueField_isIso
  have := E.snd_residueField_isIso
  have hcond := E.first_inclusion_condition a
  have hg : secondConstantArrow G.hom G.hom z = _ :=
    constantArrow_factor_unit G (pullback.snd G.hom G.hom) z s h₂'
  let f := firstFactorArrow G.hom G.hom z a
  let g := secondConstantArrow G.hom G.hom z
  let q := dualNumberBasePoint (pullback.snd G.hom G.hom ≫ G.hom) z
  have hf : f ≫ G.hom = q := by
    calc
      f ≫ G.hom = g ≫ G.hom := by simpa [f, g] using hcond
      _ = (q ≫ (η[G]).left) ≫ G.hom := by
        show secondConstantArrow G.hom G.hom z ≫ G.hom = _
        rw [hg]
      _ = q := by simp [Category.assoc, hη]
  have hmult := groupMultiplication_lift_second_unit G f g q hf
    (by simpa [g] using hg) (by simpa [f, g] using hcond)
  rw [hmult]
  have : IsIso (G.hom.residueFieldMap e) :=
    isIso_residueFieldMap_of_mem_range_section G.hom (η[G]).left hη s
  have hdualCast := dualNumberCongr_residueFieldCongr_chain G.hom (pullback.fst G.hom G.hom) m z e
    hbase hm' h₁'
  dsimp [f, firstFactorArrow, a]
  rw [tangentArrow_cast_val G.hom h₁'.symm v]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  rw [← Category.id_comp v.val]
  congr 1
  rw [← Spec.map_id]
  apply Spec.map_inj.mpr
  dsimp [f, firstFactorArrow, α, em]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro d
  exact congrArg (fun e => e d) hdualCast

/-- On the second summand of the tangent space of the fibre product at the identity, the
differential of multiplication returns the tangent vector of the second factor: the first
coordinate of the lifted arrow is the constant arrow at the identity. -/
private theorem tangentMap_secondFactor_eq {S : Scheme.{u}} (G : Over S) [GrpObj G] (s : S)
    (z : ↑(pullback G.hom G.hom))
    (h₁' : (pullback.fst G.hom G.hom) z = (η[G]).left s)
    (h₂' : (pullback.snd G.hom G.hom) z = (η[G]).left s)
    (hm' : ((Over.tensorObj_left G G) ▸ (μ[G]).left : pullback G.hom G.hom ⟶ G.left) z =
      (η[G]).left s)
    (hbase : ((Over.tensorObj_left G G) ▸ (μ[G]).left : pullback G.hom G.hom ⟶ G.left) ≫ G.hom =
      pullback.fst G.hom G.hom ≫ G.hom)
    (hmiso : IsIso (((Over.tensorObj_left G G) ▸ (μ[G]).left :
      pullback G.hom G.hom ⟶ G.left).residueFieldMap z))
    (E : TangentSpaceProductEquiv G.hom G.hom z)
    (w : DottedTangentArrow G.hom ((η[G]).left s)) :
    have := hmiso
    hm' ▸ tangentMap ((Over.tensorObj_left G G) ▸ (μ[G]).left)
        (pullback.fst G.hom G.hom ≫ G.hom) G.hom hbase z
        (E.toLinearEquiv.symm (0, h₂'.symm ▸ w)) = w := by
  have := hmiso
  let e : G.left := (η[G]).left s
  let m : pullback G.hom G.hom ⟶ G.left := (Over.tensorObj_left G G) ▸ (μ[G]).left
  have hη : (η[G]).left ≫ G.hom = 𝟙 S := Over.Hom.w (η[G])
  let T := tangentMap m (pullback.fst G.hom G.hom ≫ G.hom) G.hom hbase z
  let b := h₂'.symm ▸ w
  let x₂ := E.toLinearEquiv.symm (0, b)
  show hm' ▸ T x₂ = w
  apply Subtype.ext
  rw [tangentArrow_cast_val G.hom hm' (T x₂)]
  let em := (asIso (m.residueFieldMap z)).commRingCatIsoToRingEquiv
  let α := (dualNumberCongr em.symm).toRingHom
  rw [tangentMap_apply m (pullback.fst G.hom G.hom ≫ G.hom)
    G.hom hbase z x₂ α (fun _ => rfl) (fun _ => rfl), E.second_inclusion_apply b]
  have := E.fst_residueField_isIso
  have := E.snd_residueField_isIso
  have hcond := E.second_inclusion_condition b
  have hg : firstConstantArrow G.hom G.hom z = _ :=
    constantArrow_factor_unit G (pullback.fst G.hom G.hom) z s h₁'
  let f := secondFactorArrow G.hom G.hom z b
  let g := firstConstantArrow G.hom G.hom z
  let q := dualNumberBasePoint (pullback.fst G.hom G.hom ≫ G.hom) z
  have hf : f ≫ G.hom = q := by
    calc
      f ≫ G.hom = g ≫ G.hom := by simpa [f, g] using hcond.symm
      _ = (q ≫ (η[G]).left) ≫ G.hom := by
        show firstConstantArrow G.hom G.hom z ≫ G.hom = _
        rw [hg]
      _ = q := by simp [Category.assoc, hη]
  have hunit : (q ≫ (η[G]).left) ≫ G.hom = f ≫ G.hom := by simp [hη, hf]
  have hlift : pullback.lift g f hcond =
      pullback.lift (q ≫ (η[G]).left) f hunit := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, pullback.lift_fst]
      exact hg
    · rw [pullback.lift_snd, pullback.lift_snd]
  have hmult := groupMultiplication_lift_unit_left G q f hf
  rw [hlift, hmult]
  have : IsIso (G.hom.residueFieldMap e) :=
    isIso_residueFieldMap_of_mem_range_section G.hom (η[G]).left hη s
  have hdualCast := dualNumberCongr_residueFieldCongr_chain G.hom (pullback.snd G.hom G.hom) m z e
    (hbase.trans pullback.condition) hm' h₂'
  dsimp [f, secondFactorArrow, b]
  rw [tangentArrow_cast_val G.hom h₂'.symm w]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  rw [← Category.id_comp w.val]
  congr 1
  rw [← Spec.map_id]
  apply Spec.map_inj.mpr
  dsimp [f, secondFactorArrow, α, em]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro d
  exact congrArg (fun e => e d) hdualCast

/-- **Stacks Project, Tag 0BF5.** The differential of group-scheme multiplication at
the identity is addition of relative tangent vectors. -/
@[stacks 0BF5]
theorem tangentMap_mul_at_identity {S : Scheme.{u}} (G : Over S) [GrpObj G]
    (s : S) :
    let e : G.left := (η[G]).left s
    let m : pullback G.hom G.hom ⟶ G.left :=
      (Over.tensorObj_left G G) ▸ (μ[G]).left
    let z : ↑(pullback G.hom G.hom) :=
      (Over.tensorObj_left G G) ▸ ((lift (η[G]) (η[G])).left s)
    ∃ (h₁ : (pullback.fst G.hom G.hom) z = e)
      (h₂ : (pullback.snd G.hom G.hom) z = e)
      (hm : m z = e)
      (hbase : m ≫ G.hom = pullback.fst G.hom G.hom ≫ G.hom)
      (_ : IsIso (G.hom.residueFieldMap ((pullback.fst G.hom G.hom) z)))
      (_ : IsIso (G.hom.residueFieldMap ((pullback.snd G.hom G.hom) z)))
      (_ : IsIso (m.residueFieldMap z)),
      have : IsIso (G.hom.residueFieldMap ((pullback.fst G.hom G.hom) z)) :=
        ‹IsIso (G.hom.residueFieldMap ((pullback.fst G.hom G.hom) z))›
      have : IsIso (G.hom.residueFieldMap ((pullback.snd G.hom G.hom) z)) :=
        ‹IsIso (G.hom.residueFieldMap ((pullback.snd G.hom G.hom) z))›
      have : IsIso (m.residueFieldMap z) :=
        ‹IsIso (m.residueFieldMap z)›
      ∀ v w : DottedTangentArrow G.hom e,
        hm ▸ tangentMap m
          (pullback.fst G.hom G.hom ≫ G.hom) G.hom hbase z
          ((tangentSpaceProductEquiv G.hom G.hom z).toLinearEquiv.symm
            (h₁.symm ▸ v, h₂.symm ▸ w)) = v + w := by
  let e : G.left := (η[G]).left s
  let m : pullback G.hom G.hom ⟶ G.left :=
    (Over.tensorObj_left G G) ▸ (μ[G]).left
  let z : ↑(pullback G.hom G.hom) :=
    (Over.tensorObj_left G G) ▸ ((lift (η[G]) (η[G])).left s)
  have hη : (η[G]).left ≫ G.hom = 𝟙 S :=
    Over.Hom.w (η[G])
  have h₁ : pullback.fst G.hom G.hom z = e := by
    dsimp [z, e]
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  have h₂ : pullback.snd G.hom G.hom z = e := by
    dsimp [z, e]
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
  have hm : m z = e := by
    have hunitmulOver : lift (η[G]) (η[G]) ≫ μ[G] = η[G] := by
      simpa using (MonObj.lift_comp_one_left (𝟙 (𝟙_ (Over S))) (η[G]))
    have hunitmul : (lift (η[G]) (η[G])).left ≫ (μ[G]).left = (η[G]).left :=
      congrArg Over.Hom.left hunitmulOver
    dsimp [m, z, e]
    show ((lift (η[G]) (η[G])).left ≫ (μ[G]).left) s = _
    rw [hunitmul]
  have hbase : m ≫ G.hom = pullback.fst G.hom G.hom ≫ G.hom := by
    simp [m, Over.Hom.w (μ[G])]
  let ρ : G.left ⟶ pullback G.hom G.hom :=
    pullback.lift (𝟙 G.left) (G.hom ≫ (η[G]).left) (by simp [Category.assoc, hη])
  have hρm : ρ ≫ m = 𝟙 G.left := by
    show ((lift (𝟙 G) (toUnit G ≫ η[G])).left ≫ (μ[G]).left) = 𝟙 G.left
    exact congrArg Over.Hom.left
      (MonObj.lift_comp_one_right (𝟙 G) (toUnit G))
  let q : S ⟶ pullback G.hom G.hom :=
    pullback.lift (η[G]).left (η[G]).left (by simp [hη])
  have hρmap : (η[G]).left ≫ ρ = q := by
    apply pullback.hom_ext
    · calc
        ((η[G]).left ≫ ρ) ≫ pullback.fst G.hom G.hom =
            (η[G]).left ≫ (ρ ≫ pullback.fst G.hom G.hom) := by rw [Category.assoc]
        _ = (η[G]).left := by rw [pullback.lift_fst]; simp
        _ = q ≫ pullback.fst G.hom G.hom := by rw [pullback.lift_fst]
    · calc
        ((η[G]).left ≫ ρ) ≫ pullback.snd G.hom G.hom =
            (η[G]).left ≫ (ρ ≫ pullback.snd G.hom G.hom) := by rw [Category.assoc]
        _ = (η[G]).left ≫ (G.hom ≫ (η[G]).left) := by rw [pullback.lift_snd]
        _ = (η[G]).left := by rw [← Category.assoc, hη]; simp
        _ = q ≫ pullback.snd G.hom G.hom := by rw [pullback.lift_snd]
  have hρpoint : ρ e = z := by
    dsimp [ρ, e, z]
    exact congrArg (fun k : S ⟶ pullback G.hom G.hom => k s) hρmap
  have hfst : IsIso (G.hom.residueFieldMap (pullback.fst G.hom G.hom z)) := by
    rw [h₁]
    exact isIso_residueFieldMap_of_mem_range_section G.hom (η[G]).left hη s
  have hsnd : IsIso (G.hom.residueFieldMap (pullback.snd G.hom G.hom z)) := by
    rw [h₂]
    exact isIso_residueFieldMap_of_mem_range_section G.hom (η[G]).left hη s
  have hmiso : IsIso (m.residueFieldMap z) := by
    have h := isIso_residueFieldMap_of_mem_range_section m ρ hρm e
    rw [hρpoint] at h
    exact h
  refine ⟨h₁, h₂, hm, hbase, hfst, hsnd, hmiso, fun v w => ?_⟩
  · let E := tangentSpaceProductEquiv G.hom G.hom z
    let T := tangentMap m
      (pullback.fst G.hom G.hom ≫ G.hom) G.hom hbase z
    have h₁' : (pullback.fst G.hom G.hom) z = (η[G]).left s := by
      simpa [e] using h₁
    have h₂' : (pullback.snd G.hom G.hom) z = (η[G]).left s := by
      simpa [e] using h₂
    have hm' : m z = (η[G]).left s := by
      simpa [e] using hm
    let vFst := h₁'.symm ▸ v
    let wSnd := h₂'.symm ▸ w
    let u₁ := E.toLinearEquiv.symm (vFst, 0)
    let u₂ := E.toLinearEquiv.symm (0, wSnd)
    have hdecomp : E.toLinearEquiv.symm (vFst, wSnd) = u₁ + u₂ := by
      calc
        E.toLinearEquiv.symm (vFst, wSnd) =
            E.toLinearEquiv.symm ((vFst, 0) + (0, wSnd)) := by congr 1; ext <;> simp
        _ = u₁ + u₂ := E.toLinearEquiv.symm.map_add (vFst, 0) (0, wSnd)
    have hTdecomp : T (E.toLinearEquiv.symm (vFst, wSnd)) = T u₁ + T u₂ := by
      rw [hdecomp, T.map_add]
    have hfirst : hm' ▸ T u₁ = v :=
      tangentMap_firstFactor_eq G s z h₁' h₂' hm' hbase hmiso E v
    have hsecond : hm' ▸ T u₂ = w :=
      tangentMap_secondFactor_eq G s z h₁' h₂' hm' hbase hmiso E w
    show hm' ▸ T (E.toLinearEquiv.symm (vFst, wSnd)) = v + w
    calc
      hm' ▸ T (E.toLinearEquiv.symm (vFst, wSnd)) = hm' ▸ (T u₁ + T u₂) :=
        congrArg (fun q => hm' ▸ q) hTdecomp
      _ = (hm' ▸ T u₁) + (hm' ▸ T u₂) := tangentArrow_cast_add G.hom hm' (T u₁) (T u₂)
      _ = v + w := by rw [hfirst, hsecond]

end AlgebraicGeometry

end

