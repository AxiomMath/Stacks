module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowGroupsEnvelopes.FibreCycle
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.TangentFibre
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.TangentProduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tangent space of a fibre product, through the fibres

Let `X`, `Y` be schemes over `S` and let `x ∈ X`, `y ∈ Y` have the same image `s ∈ S`, with
`κ(s) = κ(x)` and `κ(s) = κ(y)`. Then `X ×_S Y` has exactly one point `(x, y)` over `x` and `y`,
and `T_{X ×_S Y/S, (x, y)} = T_{X/S, x} ⊕ T_{Y/S, y}`: from left to right by the tangent maps of
the two projections, from right to left by the maps `1 × y : X_s → X_s ×_s Y_s` and
`x × 1 : Y_s → X_s ×_s Y_s` through the identification of tangent spaces with tangent spaces of
fibres (Stacks, Tag 0BEA).

## Main definitions

* `AlgebraicGeometry.rationalFiberPoint`: a point `x` with `κ(f x) = κ(x)` as a rational point
  of the fibre `X_{f x}`.
* `AlgebraicGeometry.fiberProd`: the fibre product `X_s ×_s Y_s` of the two fibres.
* `AlgebraicGeometry.fiberProdInl`, `AlgebraicGeometry.fiberProdInr`: the morphisms
  `1 × y : X_s → X_s ×_s Y_s` and `x × 1 : Y_s → X_s ×_s Y_s`.
* `AlgebraicGeometry.fiberProdToPullback`: the canonical morphism `X_s ×_s Y_s → X ×_S Y`.
* `AlgebraicGeometry.TangentSpaceProductFiberEquiv`: the canonical decomposition together with
  the uniqueness of the point `(x, y)` and the description of the inverse through the fibres.

## Main results

* `AlgebraicGeometry.tangentSpaceProductFiberEquiv`: the canonical decomposition
  `T_{X ×_S Y/S, (x, y)} = T_{X/S, x} ⊕ T_{Y/S, y}` at the unique point `(x, y)` (Stacks, Tag 0BEB).

## References

* [Stacks Project, Tag 0BEB](https://stacks.math.columbia.edu/tag/0BEB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- The two images of a point of `X ×_S Y` have the same image in `S`. -/
lemma pullback_condition_apply (z : ↑(pullback f g)) :
    f (pullback.fst f g z) = g (pullback.snd f g z) := by
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]

section Fibers

/-- A point `x` with `κ(f x) = κ(x)`, as a `κ(f x)`-rational point of the fibre `X_{f x}`. -/
noncomputable def rationalFiberPoint (x : X) [IsIso (f.residueFieldMap x)] :
    Spec (S.residueField (f x)) ⟶ f.fiber (f x) :=
  Spec.map (inv (f.residueFieldMap x)) ≫ f.asFiberHom x

/-- The rational point `rationalFiberPoint f x` is a section of the structure morphism
`X_{f x} → Spec κ(f x)`. -/
@[reassoc]
lemma rationalFiberPoint_fiberToSpecResidueField (x : X) [IsIso (f.residueFieldMap x)] :
    rationalFiberPoint f x ≫ f.fiberToSpecResidueField (f x) = 𝟙 _ := by
  rw [rationalFiberPoint, Category.assoc, Scheme.Hom.asFiberHom_fiberToSpecResidueField,
    ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]

/-- The rational point `rationalFiberPoint f x` followed by the inclusion `X_{f x} → X` is the
canonical morphism `Spec κ(x) → X`, precomposed with `κ(x) ≅ κ(f x)`. -/
@[reassoc]
lemma rationalFiberPoint_fiberι (x : X) [IsIso (f.residueFieldMap x)] :
    rationalFiberPoint f x ≫ f.fiberι (f x) =
      Spec.map (inv (f.residueFieldMap x)) ≫ X.fromSpecResidueField x := by
  rw [rationalFiberPoint, Category.assoc, Scheme.Hom.asFiberHom_fiberι]

variable (x : X) (y : Y) (h : f x = g y)

/-- The fibre product `X_s ×_s Y_s` of the fibres of `X` and `Y` over the common image
`s = f x = g y`, the fibre `Y_{g y}` being regarded over `κ(f x)` through `κ(f x) = κ(g y)`. -/
noncomputable abbrev fiberProd : Scheme.{u} :=
  pullback (f.fiberToSpecResidueField (f x))
    (g.fiberToSpecResidueField (g y) ≫ Spec.map (S.residueFieldCongr h).hom)

/-- The two composites `X_s ×_s Y_s → X → S` and `X_s ×_s Y_s → Y → S` agree. -/
lemma fiberProd_condition :
    (pullback.fst (f.fiberToSpecResidueField (f x))
        (g.fiberToSpecResidueField (g y) ≫ Spec.map (S.residueFieldCongr h).hom) ≫
      f.fiberι (f x)) ≫ f =
    (pullback.snd (f.fiberToSpecResidueField (f x))
        (g.fiberToSpecResidueField (g y) ≫ Spec.map (S.residueFieldCongr h).hom) ≫
      g.fiberι (g y)) ≫ g := by
  simp only [Category.assoc, Scheme.Hom.fiber_fac]
  rw [pullback.condition_assoc, Category.assoc,
    Scheme.residueFieldCongr_fromSpecResidueField]

/-- The canonical morphism `X_s ×_s Y_s → X ×_S Y`. -/
noncomputable def fiberProdToPullback : fiberProd f g x y h ⟶ pullback f g :=
  pullback.lift (pullback.fst _ _ ≫ f.fiberι (f x)) (pullback.snd _ _ ≫ g.fiberι (g y))
    (fiberProd_condition f g x y h)

/-- The first projection of `X_s ×_s Y_s → X ×_S Y` is the first projection followed by the
inclusion `X_s → X`. -/
@[reassoc (attr := simp)]
lemma fiberProdToPullback_fst :
    fiberProdToPullback f g x y h ≫ pullback.fst f g = pullback.fst _ _ ≫ f.fiberι (f x) :=
  pullback.lift_fst _ _ _

/-- The second projection of `X_s ×_s Y_s → X ×_S Y` is the second projection followed by the
inclusion `Y_s → Y`. -/
@[reassoc (attr := simp)]
lemma fiberProdToPullback_snd :
    fiberProdToPullback f g x y h ≫ pullback.snd f g = pullback.snd _ _ ≫ g.fiberι (g y) :=
  pullback.lift_snd _ _ _

/-- The morphism `1 × y : X_s → X_s ×_s Y_s`, where `y` is regarded as a `κ(s)`-rational point
of `Y_s`. -/
noncomputable def fiberProdInl [IsIso (g.residueFieldMap y)] :
    f.fiber (f x) ⟶ fiberProd f g x y h :=
  pullback.lift (𝟙 _)
    (f.fiberToSpecResidueField (f x) ≫ Spec.map (S.residueFieldCongr h).inv ≫
      rationalFiberPoint g y) (by
    rw [Category.id_comp, Category.assoc, Category.assoc,
      rationalFiberPoint_fiberToSpecResidueField_assoc, ← Spec.map_comp, Iso.hom_inv_id,
      Spec.map_id, Category.comp_id])

/-- The morphism `x × 1 : Y_s → X_s ×_s Y_s`, where `x` is regarded as a `κ(s)`-rational point
of `X_s`. -/
noncomputable def fiberProdInr [IsIso (f.residueFieldMap x)] :
    g.fiber (g y) ⟶ fiberProd f g x y h :=
  pullback.lift
    (g.fiberToSpecResidueField (g y) ≫ Spec.map (S.residueFieldCongr h).hom ≫
      rationalFiberPoint f x) (𝟙 _) (by
    rw [Category.id_comp, Category.assoc, Category.assoc,
      rationalFiberPoint_fiberToSpecResidueField, Category.comp_id])

/-- The first component of `1 × y : X_s → X_s ×_s Y_s` is the identity. -/
@[reassoc (attr := simp)]
lemma fiberProdInl_fst [IsIso (g.residueFieldMap y)] :
    fiberProdInl f g x y h ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- The second component of `1 × y : X_s → X_s ×_s Y_s` is the constant morphism at the
rational point `y` of `Y_s`. -/
@[reassoc (attr := simp)]
lemma fiberProdInl_snd [IsIso (g.residueFieldMap y)] :
    fiberProdInl f g x y h ≫ pullback.snd _ _ =
      f.fiberToSpecResidueField (f x) ≫ Spec.map (S.residueFieldCongr h).inv ≫
        rationalFiberPoint g y :=
  pullback.lift_snd _ _ _

/-- The first component of `x × 1 : Y_s → X_s ×_s Y_s` is the constant morphism at the
rational point `x` of `X_s`. -/
@[reassoc (attr := simp)]
lemma fiberProdInr_fst [IsIso (f.residueFieldMap x)] :
    fiberProdInr f g x y h ≫ pullback.fst _ _ =
      g.fiberToSpecResidueField (g y) ≫ Spec.map (S.residueFieldCongr h).hom ≫
        rationalFiberPoint f x :=
  pullback.lift_fst _ _ _

/-- The second component of `x × 1 : Y_s → X_s ×_s Y_s` is the identity. -/
@[reassoc (attr := simp)]
lemma fiberProdInr_snd [IsIso (f.residueFieldMap x)] :
    fiberProdInr f g x y h ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The tangent vector of the fibre `X_{f x}` attached to a tangent vector of `X/S` at `x` by
the identification of Stacks, Tag 0BEA lies over the base point of `Spec κ(f x)`. -/
lemma tangentSpaceEquivFiber_val_fiberToSpecResidueField (v : DottedTangentArrow f x) :
    Spec.map (CommRingCat.ofHom
        (dualNumberCongr (tangentSpaceEquivFiber f x).residueFieldEquiv).toRingHom) ≫
      ((tangentSpaceEquivFiber f x).toAddEquiv v).val ≫ f.fiberToSpecResidueField (f x) =
        dualNumberToBase (X.residueField x) ≫ Spec.map (f.residueFieldMap x) := by
  let E := tangentSpaceEquivFiber f x
  let p := f.fiberToSpecResidueField (f x)
  let x' := f.asFiber x
  have hw : (E.toAddEquiv v).val ≫ p =
      dualNumberToBase _ ≫ (f.fiber (f x)).fromSpecResidueField x' ≫ p :=
    (E.toAddEquiv v).property.2.trans
      (congrArg (fun k => Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ k)
        (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField p x'))
  calc Spec.map (CommRingCat.ofHom (dualNumberCongr E.residueFieldEquiv).toRingHom) ≫
        (E.toAddEquiv v).val ≫ p
      = Spec.map (CommRingCat.ofHom (dualNumberCongr E.residueFieldEquiv).toRingHom) ≫
          dualNumberToBase _ ≫ (f.fiber (f x)).fromSpecResidueField x' ≫ p :=
        congrArg (fun k => _ ≫ k) hw
    _ = (dualNumberToBase (X.residueField x) ≫
          Spec.map (CommRingCat.ofHom E.residueFieldEquiv.toRingHom)) ≫
          (f.fiber (f x)).fromSpecResidueField x' ≫ p :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ (f.fiber (f x)).fromSpecResidueField x' ≫ p)
            (dualNumberToBase_natural E.residueFieldEquiv))
    _ = dualNumberToBase (X.residueField x) ≫
          (Spec.map (CommRingCat.ofHom E.residueFieldEquiv.toRingHom) ≫
            (f.fiber (f x)).fromSpecResidueField x') ≫ p := by
        simp only [Category.assoc]
    _ = dualNumberToBase (X.residueField x) ≫ f.asFiberHom x ≫ p :=
        congrArg (fun k => dualNumberToBase (X.residueField x) ≫ k ≫ p)
          E.residueFieldEquiv_spec
    _ = dualNumberToBase (X.residueField x) ≫ Spec.map (f.residueFieldMap x) :=
        congrArg (fun k => dualNumberToBase (X.residueField x) ≫ k)
          (Scheme.Hom.asFiberHom_fiberToSpecResidueField f x)

/-- Precomposing the tangent vector of the fibre attached to `v` with a further change of
residue field `ψ : κ(x) ≃ L` gives the base point of `Spec κ(f x)` through `L`. -/
private lemma specMap_dualNumberCongr_tangentSpaceEquivFiber_val {L : Type u} [CommRing L]
    (ψ : X.residueField x ≃+* L) (v : DottedTangentArrow f x) :
    Spec.map (CommRingCat.ofHom (dualNumberCongr ψ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (dualNumberCongr (tangentSpaceEquivFiber f x).residueFieldEquiv).toRingHom) ≫
        ((tangentSpaceEquivFiber f x).toAddEquiv v).val ≫ f.fiberToSpecResidueField (f x) =
      dualNumberToBase L ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫
        Spec.map (f.residueFieldMap x) :=
  calc _ = Spec.map (CommRingCat.ofHom (dualNumberCongr ψ).toRingHom) ≫
        dualNumberToBase (X.residueField x) ≫ Spec.map (f.residueFieldMap x) :=
        congrArg (fun k => _ ≫ k) (tangentSpaceEquivFiber_val_fiberToSpecResidueField f x v)
    _ = (dualNumberToBase _ ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom)) ≫
        Spec.map (f.residueFieldMap x) :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ Spec.map (f.residueFieldMap x)) (dualNumberToBase_natural ψ))
    _ = _ := Category.assoc _ _ _

end Fibers

section Product

variable (z : ↑(pullback f g))

/-- The residue fields of `x`, `y` and `(x, y)` over `κ(s)`: the two composites
`κ(s) → κ(x) → κ(z)` and `κ(s) → κ(y) → κ(z)` agree. -/
lemma residueFieldMap_fst_eq_snd :
    f.residueFieldMap (pullback.fst f g z) ≫ (pullback.fst f g).residueFieldMap z =
      (S.residueFieldCongr (pullback_condition_apply f g z)).hom ≫
        g.residueFieldMap (pullback.snd f g z) ≫ (pullback.snd f g).residueFieldMap z := by
  have hc := Scheme.Hom.residueFieldMap_congr (pullback.condition (f := f) (g := g)) z
  rwa [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp] at hc

/-- Splitting the dual-number isomorphism attached to a composite of ring isomorphisms. -/
lemma specMap_dualNumberCongr_trans {R K L : Type u} [CommRing R] [CommRing K] [CommRing L]
    (e : R ≃+* K) (e' : K ≃+* L) :
    Spec.map (CommRingCat.ofHom (dualNumberCongr (e.trans e')).toRingHom) =
      Spec.map (CommRingCat.ofHom (dualNumberCongr e').toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom) := by
  rw [← Spec.map_comp]
  rfl

/-- Transporting a relation between residue field maps along `Spec`, for the constant arrows. -/
private lemma comp_eq_of_ring_comp_eq {Z X Sx Sg Y' : CommRingCat} {V W : Scheme.{u}}
    (D : V ⟶ Spec Z) (u : V ⟶ Spec Sx) (ι : Spec Y' ⟶ W) (a : Y' ⟶ Sg) (b : Sg ⟶ Sx)
    (α : Sx ⟶ X) (β : X ⟶ Z) (δ : Y' ⟶ Z) (hR : a ≫ b ≫ α ≫ β = δ)
    (claim : u = D ≫ Spec.map β ≫ Spec.map α) :
    D ≫ Spec.map δ ≫ ι = u ≫ Spec.map b ≫ Spec.map a ≫ ι := by
  subst hR claim
  simp only [Spec.map_comp, Category.assoc]

/-- The tangent arrow of `X ×_S Y` with components a tangent arrow of `X` and the constant
arrow at `y` is the image of the corresponding tangent vector of the fibre `X_s` under
`1 × y : X_s → X_s ×_s Y_s` followed by `X_s ×_s Y_s → X ×_S Y`. -/
lemma lift_firstFactorArrow_eq_fiberProdInl
    [IsIso (g.residueFieldMap (pullback.snd f g z))]
    [IsIso ((pullback.fst f g).residueFieldMap z)]
    (v : DottedTangentArrow f (pullback.fst f g z))
    (hc : firstFactorArrow f g z v ≫ f = secondConstantArrow f g z ≫ g) :
    pullback.lift (firstFactorArrow f g z v) (secondConstantArrow f g z) hc =
      Spec.map (CommRingCat.ofHom (dualNumberCongr
          ((tangentSpaceEquivFiber f (pullback.fst f g z)).residueFieldEquiv.trans
            (asIso ((pullback.fst f g).residueFieldMap z)).commRingCatIsoToRingEquiv)).toRingHom) ≫
        ((tangentSpaceEquivFiber f (pullback.fst f g z)).toAddEquiv v).val ≫
          fiberProdInl f g _ _ (pullback_condition_apply f g z) ≫
            fiberProdToPullback f g _ _ (pullback_condition_apply f g z) := by
  let E := tangentSpaceEquivFiber f (pullback.fst f g z)
  let w := E.toAddEquiv v
  let ψ := (asIso ((pullback.fst f g).residueFieldMap z)).commRingCatIsoToRingEquiv
  have claim : Spec.map (CommRingCat.ofHom (dualNumberCongr ψ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (dualNumberCongr E.residueFieldEquiv).toRingHom) ≫
        w.val ≫ f.fiberToSpecResidueField (f (pullback.fst f g z)) =
      dualNumberToBase ((pullback f g).residueField z) ≫
        Spec.map ((pullback.fst f g).residueFieldMap z) ≫
          Spec.map (f.residueFieldMap (pullback.fst f g z)) :=
    specMap_dualNumberCongr_tangentSpaceEquivFiber_val f _ ψ v
  have hR : inv (g.residueFieldMap (pullback.snd f g z)) ≫
      (S.residueFieldCongr (pullback_condition_apply f g z)).inv ≫
        f.residueFieldMap (pullback.fst f g z) ≫ (pullback.fst f g).residueFieldMap z =
      (pullback.snd f g).residueFieldMap z := by
    rw [residueFieldMap_fst_eq_snd f g z, Iso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc]
  rw [specMap_dualNumberCongr_trans]
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    simp only [Category.assoc, fiberProdToPullback_fst, fiberProdInl_fst_assoc]
    rw [(tangentSpaceEquivFiber f (pullback.fst f g z)).toAddEquiv_fiberι]
    rfl
  · rw [pullback.lift_snd]
    simp only [Category.assoc, fiberProdToPullback_snd, fiberProdInl_snd_assoc,
      rationalFiberPoint_fiberι]
    exact (comp_eq_of_ring_comp_eq _ _ _ _ _ _ _ _ hR claim).trans (by simp [E, w, ψ])

/-- The tangent arrow of `X ×_S Y` with components the constant arrow at `x` and a tangent arrow
of `Y` is the image of the corresponding tangent vector of the fibre `Y_s` under
`x × 1 : Y_s → X_s ×_s Y_s` followed by `X_s ×_s Y_s → X ×_S Y`. -/
lemma lift_secondFactorArrow_eq_fiberProdInr
    [IsIso (f.residueFieldMap (pullback.fst f g z))]
    [IsIso ((pullback.snd f g).residueFieldMap z)]
    (v : DottedTangentArrow g (pullback.snd f g z))
    (hc : firstConstantArrow f g z ≫ f = secondFactorArrow f g z v ≫ g) :
    pullback.lift (firstConstantArrow f g z) (secondFactorArrow f g z v) hc =
      Spec.map (CommRingCat.ofHom (dualNumberCongr
          ((tangentSpaceEquivFiber g (pullback.snd f g z)).residueFieldEquiv.trans
            (asIso ((pullback.snd f g).residueFieldMap z)).commRingCatIsoToRingEquiv)).toRingHom) ≫
        ((tangentSpaceEquivFiber g (pullback.snd f g z)).toAddEquiv v).val ≫
          fiberProdInr f g _ _ (pullback_condition_apply f g z) ≫
            fiberProdToPullback f g _ _ (pullback_condition_apply f g z) := by
  let E := tangentSpaceEquivFiber g (pullback.snd f g z)
  let w := E.toAddEquiv v
  let ψ := (asIso ((pullback.snd f g).residueFieldMap z)).commRingCatIsoToRingEquiv
  have claim : Spec.map (CommRingCat.ofHom (dualNumberCongr ψ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (dualNumberCongr E.residueFieldEquiv).toRingHom) ≫
        w.val ≫ g.fiberToSpecResidueField (g (pullback.snd f g z)) =
      dualNumberToBase ((pullback f g).residueField z) ≫
        Spec.map ((pullback.snd f g).residueFieldMap z) ≫
          Spec.map (g.residueFieldMap (pullback.snd f g z)) :=
    specMap_dualNumberCongr_tangentSpaceEquivFiber_val g _ ψ v
  have hR : inv (f.residueFieldMap (pullback.fst f g z)) ≫
      (S.residueFieldCongr (pullback_condition_apply f g z)).hom ≫
        g.residueFieldMap (pullback.snd f g z) ≫ (pullback.snd f g).residueFieldMap z =
      (pullback.fst f g).residueFieldMap z := by
    rw [← residueFieldMap_fst_eq_snd f g z, IsIso.inv_hom_id_assoc]
  rw [specMap_dualNumberCongr_trans]
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    simp only [Category.assoc, fiberProdToPullback_fst, fiberProdInr_fst_assoc,
      rationalFiberPoint_fiberι]
    exact (comp_eq_of_ring_comp_eq _ _ _ _ _ _ _ _ hR claim).trans (by simp [E, w, ψ])
  · rw [pullback.lift_snd]
    simp only [Category.assoc, fiberProdToPullback_snd, fiberProdInr_snd_assoc]
    rw [(tangentSpaceEquivFiber g (pullback.snd f g z)).toAddEquiv_fiberι]
    rfl

end Product

/-- The canonical decomposition `T_{X ×_S Y/S, (x, y)} = T_{X/S, x} ⊕ T_{Y/S, y}` at a point
`z = (x, y)` of `X ×_S Y` with `κ(s) = κ(x)` and `κ(s) = κ(y)`, as described in Stacks,
Tag 0BEB: `z` is the only point of `X ×_S Y` over `x` and `y`; the map from left to right is
given by the tangent maps of the two projections (inherited from
`AlgebraicGeometry.TangentSpaceProductEquiv`); the map from right to left sends a tangent
vector of `X/S` at `x` to the image, under `1 × y : X_s → X_s ×_s Y_s` followed by
`X_s ×_s Y_s → X ×_S Y`, of the tangent vector of the fibre `X_s` corresponding to it by the
identification of Stacks, Tag 0BEA, and symmetrically for `x × 1 : Y_s → X_s ×_s Y_s`. -/
structure TangentSpaceProductFiberEquiv {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (z : ↑(pullback f g)) [IsIso (f.residueFieldMap (pullback.fst f g z))]
    [IsIso (g.residueFieldMap (pullback.snd f g z))] extends TangentSpaceProductEquiv f g z where
  /-- `z` is the point `(x, y)`: the only point of `X ×_S Y` lying over `x` and `y`. -/
  eq_of_fst_eq_of_snd_eq (z' : ↑(pullback f g)) :
    pullback.fst f g z' = pullback.fst f g z → pullback.snd f g z' = pullback.snd f g z →
      z' = z
  /-- On the first summand the map from right to left is induced by `1 × y : X_s → X_s ×_s Y_s`
  through the identification of tangent spaces with tangent spaces of fibres. -/
  fiberProdInl_apply (v : DottedTangentArrow f (pullback.fst f g z)) :
    letI := fst_residueField_isIso
    letI := snd_residueField_isIso
    letI : Module ((pullback f g).residueField z)
        (DottedTangentArrow f (pullback.fst f g z)) :=
      Module.compHom _ (inv ((pullback.fst f g).residueFieldMap z)).hom
    letI : Module ((pullback f g).residueField z)
        (DottedTangentArrow g (pullback.snd f g z)) :=
      Module.compHom _ (inv ((pullback.snd f g).residueFieldMap z)).hom
    (toLinearEquiv.symm (v, 0)).val =
      Spec.map (CommRingCat.ofHom (dualNumberCongr
          ((tangentSpaceEquivFiber f (pullback.fst f g z)).residueFieldEquiv.trans
            (asIso ((pullback.fst f g).residueFieldMap z)).commRingCatIsoToRingEquiv)).toRingHom) ≫
        ((tangentSpaceEquivFiber f (pullback.fst f g z)).toAddEquiv v).val ≫
          fiberProdInl f g _ _ (pullback_condition_apply f g z) ≫
            fiberProdToPullback f g _ _ (pullback_condition_apply f g z)
  /-- On the second summand the map from right to left is induced by
  `x × 1 : Y_s → X_s ×_s Y_s` through the identification of tangent spaces with tangent spaces
  of fibres. -/
  fiberProdInr_apply (v : DottedTangentArrow g (pullback.snd f g z)) :
    letI := fst_residueField_isIso
    letI := snd_residueField_isIso
    letI : Module ((pullback f g).residueField z)
        (DottedTangentArrow f (pullback.fst f g z)) :=
      Module.compHom _ (inv ((pullback.fst f g).residueFieldMap z)).hom
    letI : Module ((pullback f g).residueField z)
        (DottedTangentArrow g (pullback.snd f g z)) :=
      Module.compHom _ (inv ((pullback.snd f g).residueFieldMap z)).hom
    (toLinearEquiv.symm (0, v)).val =
      Spec.map (CommRingCat.ofHom (dualNumberCongr
          ((tangentSpaceEquivFiber g (pullback.snd f g z)).residueFieldEquiv.trans
            (asIso ((pullback.snd f g).residueFieldMap z)).commRingCatIsoToRingEquiv)).toRingHom) ≫
        ((tangentSpaceEquivFiber g (pullback.snd f g z)).toAddEquiv v).val ≫
          fiberProdInr f g _ _ (pullback_condition_apply f g z) ≫
            fiberProdToPullback f g _ _ (pullback_condition_apply f g z)

/-- **Stacks Project, Tag 0BEB.** Let `X`, `Y` be schemes over `S` and let `z = (x, y)` be a point
of `X ×_S Y` whose projections `x ∈ X`, `y ∈ Y` have residue fields `κ(x) = κ(s) = κ(y)`, where
`s` is their common image in `S` (every such pair `x`, `y` comes from a point `z`, by
`AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`). Then `z` is the only point over
`x` and `y`, and `T_{X ×_S Y/S, (x, y)} = T_{X/S, x} ⊕ T_{Y/S, y}` canonically: from left to
right by the tangent maps of the projections, from right to left by `1 × y : X_s → X_s ×_s Y_s`
and `x × 1 : Y_s → X_s ×_s Y_s` via the identification of tangent spaces with tangent spaces of
fibres (Stacks, Tag 0BEA). -/
@[stacks 0BEB "T_{X ×_S Y/S,(x,y)} = T_{X/S,x} ⊕ T_{Y/S,y} at the unique point (x,y): left to \
right by the projections, right to left by 1 × y and x × 1 on the fibres via 0BEA",
  sga "3 V 4.1.2" "more general"]
noncomputable def tangentSpaceProductFiberEquiv {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g))
    [IsIso (f.residueFieldMap (pullback.fst f g z))]
    [IsIso (g.residueFieldMap (pullback.snd f g z))] :
    TangentSpaceProductFiberEquiv f g z where
  toTangentSpaceProductEquiv := tangentSpaceProductEquiv f g z
  eq_of_fst_eq_of_snd_eq z' hx hy :=
    Stacks.Chow.pullbackPoint_eq_of_proj_eq_of_residueFieldMap_isIso f g z' z hx hy
      (hx ▸ inferInstance)
  fiberProdInl_apply v :=
    letI := (tangentSpaceProductEquiv f g z).fst_residueField_isIso
    ((tangentSpaceProductEquiv f g z).first_inclusion_apply v).trans
      (lift_firstFactorArrow_eq_fiberProdInl f g z v _)
  fiberProdInr_apply v :=
    letI := (tangentSpaceProductEquiv f g z).snd_residueField_isIso
    ((tangentSpaceProductEquiv f g z).second_inclusion_apply v).trans
      (lift_secondFactorArrow_eq_fiberProdInr f g z v _)

end AlgebraicGeometry

end
