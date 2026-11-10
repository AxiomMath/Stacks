module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import StacksCore.Tactic.StacksAttribute

/-!
# The multiplicative group scheme

The multiplicative group over the integers is the spectrum of the Laurent polynomial ring
`ℤ[T, T⁻¹]`, with multiplication induced by `T ↦ T ⊗ T` on coordinate rings. It represents the
functor sending a scheme to the units in its ring of global sections, and over an arbitrary base
scheme it is obtained from the integral model by base change.

## Main definitions

* `AlgebraicGeometry.multiplicativeGroup` is the scheme `Spec (ℤ[T, T⁻¹])`, and
  `AlgebraicGeometry.multiplicativeGroupULift` its universe-polymorphic copy.
* `AlgebraicGeometry.multiplicativeGroupMultiplicationRingHom` is the homomorphism
  `ℤ[T, T⁻¹] → ℤ[T, T⁻¹] ⊗_ℤ ℤ[T, T⁻¹]` sending `T` to `T ⊗ T`, and
  `AlgebraicGeometry.multiplicativeGroupMultiplication` the morphism it induces from the fibre
  square of the multiplicative group to itself.
* `AlgebraicGeometry.multiplicativeGroupBaseChange` is the multiplicative group over a
  scheme `S`.
* `AlgebraicGeometry.globalUnits` is the group-valued functor taking an `S`-scheme to the units
  in its ring of global sections.
* `AlgebraicGeometry.multiplicativeCoordinate` is the Laurent coordinate, regarded as a global
  unit on the integral model.

## Main results

* `AlgebraicGeometry.unitsOfGlobalSections_representableBy_multiplicativeGroup` identifies the
  multiplicative group scheme as a representing object for the units-of-global-sections functor.
* `AlgebraicGeometry.multiplicativeGroupGrpObj_mul` identifies the multiplication of the
  group-object structure over `Spec ℤ` with the multiplication morphism.
* `AlgebraicGeometry.multiplicativeGroupBaseChangeGrpObj` equips the base change with its
  group-scheme structure, and
  `AlgebraicGeometry.baseChangePointsIsoMultiplicativeGroupPoints` and
  `AlgebraicGeometry.baseChangePointsIsoGlobalUnits` compute its functor of points.

## Implementation notes

A group scheme over a scheme `S` is a group object in the category of schemes over `S`;
Mathlib's `LaurentPolynomial.instHopfAlgebra` and
`AlgebraicGeometry.instGrpObjSpecAsOverSpec` supply this structure over `Spec ℤ`, and the
separate equation `multiplicativeGroupGrpObj_mul` records that its multiplication is the
morphism induced by `T ↦ T ⊗ T`. The tensor product of the two Laurent polynomial rings is
identified with the coordinate ring of the fibre product by
`AlgebraicGeometry.pullbackSpecIso`.

A universe-polymorphic copy of the integral model is used when base-changing to schemes in
other universes; both structure morphisms are induced by `LaurentPolynomial.C`. The base change
is the fibre product of that copy with `S` over the terminal scheme `Spec ℤ`. The pointwise
identifications of its functor of points are stated as natural isomorphisms of functors, and
their characterizing lemmas say that the first one is composition with the first pullback
projection and that the second sends a point to the pullback of the Laurent coordinate `T`. In
particular these specifications rule out twisting either isomorphism by inversion. The
group-object structure is definitionally the one induced by this specified representation of the
global-units functor, so its multiplication is the canonical multiplication of units.

## References

* [Stacks Project, Tag 022U](https://stacks.math.columbia.edu/tag/022U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 022U.** The underlying scheme of the multiplicative group over the
integers is the spectrum of the Laurent polynomial ring `ℤ[T, T⁻¹]`. -/
@[stacks 022U "multiplicative_group_scheme_underlying_scheme", sga "3 I 4.3.2"]
noncomputable abbrev multiplicativeGroup := Spec (.of (LaurentPolynomial ℤ))

/-- The canonical structure morphism from the multiplicative group scheme to `Spec ℤ`. -/
@[stacks 022U "multiplicative_group_scheme_underlying_scheme"]
noncomputable instance multiplicativeGroupCanonicallyOver :
    multiplicativeGroup.CanonicallyOver (Spec (.of ℤ)) where
  hom := Spec.map (CommRingCat.ofHom LaurentPolynomial.C)

/-- A universe-polymorphic copy of the integral multiplicative group, used for base change. -/
noncomputable abbrev multiplicativeGroupULift : Scheme.{u} :=
  Spec (.of (LaurentPolynomial (ULift.{u} ℤ)))

/-- The structure morphism of the lifted copy of the integral multiplicative group. -/
noncomputable instance multiplicativeGroupULiftCanonicallyOver :
    multiplicativeGroupULift.CanonicallyOver (Spec (.of (ULift.{u} ℤ))) where
  hom := Spec.map (CommRingCat.ofHom LaurentPolynomial.C)

/-- The homomorphism on coordinate rings which sends the Laurent variable to the product of its
images in the two tensor factors, that is, to `T ⊗ T`. -/
noncomputable def multiplicativeGroupMultiplicationRingHom :
    LaurentPolynomial ℤ →+*
      TensorProduct ℤ (LaurentPolynomial ℤ) (LaurentPolynomial ℤ) :=
  @LaurentPolynomial.eval₂ ℤ _
    (TensorProduct ℤ (LaurentPolynomial ℤ) (LaurentPolynomial ℤ)) _
    (algebraMap ℤ (TensorProduct ℤ (LaurentPolynomial ℤ) (LaurentPolynomial ℤ)))
    (((LaurentPolynomial.isUnit_T (R := ℤ) 1).unit.map
        (Algebra.TensorProduct.includeLeftRingHom :
          LaurentPolynomial ℤ →+*
            TensorProduct ℤ (LaurentPolynomial ℤ) (LaurentPolynomial ℤ))) *
      ((LaurentPolynomial.isUnit_T (R := ℤ) 1).unit.map
        (Algebra.TensorProduct.includeRight.toRingHom :
          LaurentPolynomial ℤ →+*
            TensorProduct ℤ (LaurentPolynomial ℤ) (LaurentPolynomial ℤ))))

/-- **Stacks Project, Tag 022U.** Multiplication on the multiplicative group is the scheme
morphism induced by `T ↦ T ⊗ T` on coordinate rings, after the canonical identification of the
fibre product with the spectrum of the tensor product. -/
@[stacks 022U "multiplication"]
noncomputable def multiplicativeGroupMultiplication :
    pullback (multiplicativeGroup ↘ Spec (.of ℤ))
      (multiplicativeGroup ↘ Spec (.of ℤ)) ⟶ multiplicativeGroup :=
  (pullbackSpecIso ℤ (LaurentPolynomial ℤ) (LaurentPolynomial ℤ)).hom ≫
    Spec.map (CommRingCat.ofHom multiplicativeGroupMultiplicationRingHom)

/-- Homomorphisms from the universe-lifted infinite cyclic group into a commutative group are
its elements. -/
noncomputable def unitsHomEquiv (H : Type u) [CommGroup H] :
    (Multiplicative (ULift.{u} ℤ) →* H) ≃ H :=
  let e : Multiplicative (ULift.{u} ℤ) ≃* Multiplicative ℤ :=
    ⟨Equiv.ulift, fun _ _ => rfl⟩
  let p : (Multiplicative (ULift.{u} ℤ) →* H) ≃ (Multiplicative ℤ →* H) :=
    { toFun := fun f => f.comp e.symm
      invFun := fun f => f.comp e
      left_inv := fun _ => by ext; simp [e]
      right_inv := fun _ => by ext; simp [e] }
  p.trans (zpowersMulHom H).symm

/-- The canonical datum exhibiting the integral multiplicative group as a representing object
for the functor of units in global sections. -/
@[ega "IV 20.2.8" "The bijection"]
noncomputable def unitsOfGlobalSectionsCanonicalRepresentation :
    (Scheme.Γ ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
      forget CommGrpCat).RepresentableBy multiplicativeGroupULift := by
  let R : CommRingCat.{u} := CommRingCat.of (ULift.{u} ℤ)
  let G : CommGrpCat.{u} := CommGrpCat.of (Multiplicative (ULift.{u} ℤ))
  let A := Adjunction.comp CommGrpCat.forget₂CommMonAdj
    (CommRingCat.forget₂Adj (R := R) CommRingCat.isInitial)
  let B : CommRingCat.{u} :=
    (Under.forget R).obj (R.monoidAlgebra.obj
      ((forget₂ CommGrpCat CommMonCat).obj G))
  let E := ((MonoidAlgebra.toAdditiveAlgEquiv (ULift.{u} ℤ) (ULift.{u} ℤ)
      (Multiplicative (ULift.{u} ℤ))).trans
    (AddMonoidAlgebra.domCongr (ULift.{u} ℤ) (ULift.{u} ℤ)
      ({ toFun := fun x => x.toMul.down
         invFun := fun n => Additive.ofMul (Multiplicative.ofAdd (ULift.up n))
         left_inv := by intro x; cases x; rfl
         right_inv := fun _ => rfl
         map_add' := by
           intro x y
           rw [toMul_add]
           exact congrArg (fun z : Additive (Multiplicative (ULift.{u} ℤ)) =>
             z.toMul.toAdd.down) (ofMul_mul x.toMul y.toMul) } :
        Additive (Multiplicative (ULift.{u} ℤ)) ≃+ ℤ))).toRingEquiv
  let base : ((Scheme.Γ ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
      forget CommGrpCat).RepresentableBy (Scheme.Spec.obj (Opposite.op B))) := by
    refine { homEquiv := ?_, homEquiv_comp := ?_ }
    · intro X
      let S := (Scheme.Γ.rightOp.obj X).unop
      let H : Type u :=
        (CommMonCat.units.obj ((forget₂ CommRingCat CommMonCat).obj S) : Type u)
      let e := _root_.AlgebraicGeometry.ΓSpec.adjunction.homEquiv X (Opposite.op B)
      let eA : (B ⟶ S) ≃ (G ⟶ CommMonCat.units.obj
          ((forget₂ CommRingCat CommMonCat).obj S)) := A.homEquiv G S
      change (X ⟶ Scheme.Spec.obj (Opposite.op B)) ≃ H
      exact
        { toFun := fun f =>
            let h := (e.symm f).unop
            unitsHomEquiv H (eA h).hom
          invFun := fun x => e (eA.symm
            (CommGrpCat.ofHom ((unitsHomEquiv H).symm x) : G ⟶ _)).op
          left_inv := by
            intro f
            let h := (e.symm f).unop
            change e ((eA.symm (CommGrpCat.ofHom
              ((unitsHomEquiv H).symm
                (unitsHomEquiv H (eA h).hom)) : G ⟶ _)).op) = f
            rw [← e.apply_symm_apply f]
            congr 1
            apply Quiver.Hom.unop_inj
            calc
              eA.symm (CommGrpCat.ofHom
                  ((unitsHomEquiv H).symm (unitsHomEquiv H (eA h).hom)) : G ⟶ _) =
                eA.symm (eA h) := by
                  congr 1
                  ext z
                  exact congrArg (fun g => g z) ((unitsHomEquiv H).symm_apply_apply (eA h).hom)
              _ = h := eA.symm_apply_apply h
          right_inv := by
            intro x
            dsimp
            let g : G ⟶ CommMonCat.units.obj ((forget₂ CommRingCat CommMonCat).obj S) :=
              CommGrpCat.ofHom ((unitsHomEquiv H).symm x)
            change unitsHomEquiv H
              (CommGrpCat.Hom.hom (eA ((e.symm (e (eA.symm g).op)).unop))) = x
            rw [e.symm_apply_apply, Quiver.Hom.unop_op, eA.apply_symm_apply]
            exact (unitsHomEquiv H).apply_symm_apply x }
    · intro X Y f g
      rfl
  exact base.equivOfIsoObj (Scheme.Spec.mapIso (E.toCommRingCatIso.op))

/-- **Stacks Project, Tag 022U.** The functor assigning to a scheme the units in its ring of
global sections is represented by the multiplicative group scheme `Spec (ℤ[T, T⁻¹])`. -/
@[stacks 022U "represents_units", ega "IV 20.2.8" "Morphisms V → Spec Z[T", sga "3 I 4.3.2"]
theorem unitsOfGlobalSections_representableBy_multiplicativeGroup :
    Nonempty
      ((Scheme.Γ ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
          forget CommGrpCat).RepresentableBy (multiplicativeGroupULift : Scheme.{u})) :=
  ⟨unitsOfGlobalSectionsCanonicalRepresentation⟩

add_to_stacks 022U "group_scheme" LaurentPolynomial.instHopfAlgebra
add_to_sga "3 I 4.3.2" "special case" LaurentPolynomial.instHopfAlgebra
add_to_sga "3 VIIA 3.3" "special case" LaurentPolynomial.instHopfAlgebra
add_to_ega "II 8.3.9" "partial, special case" LaurentPolynomial.instHopfAlgebra
add_to_stacks 022U "group_scheme" AlgebraicGeometry.instGrpObjSpecAsOverSpec
add_to_sga "3 I 4.2" "partial" AlgebraicGeometry.instGrpObjSpecAsOverSpec
add_to_sga "3 VIIA 3.3" "partial" AlgebraicGeometry.instGrpObjSpecAsOverSpec
add_to_sga "3 VIIA 3.3.0" "partial" AlgebraicGeometry.instGrpObjSpecAsOverSpec
add_to_sga "3 VIIB 2.1" "(i), special case" AlgebraicGeometry.instGrpObjSpecAsOverSpec
add_to_sga "3 VIIB 2.2.1" "partial" AlgebraicGeometry.instGrpObjSpecAsOverSpec

private theorem multiplicativeGroupComul_eq_multiplicationRingHom :
    (Bialgebra.comulAlgHom ℤ (LaurentPolynomial ℤ)).toRingHom =
      multiplicativeGroupMultiplicationRingHom := by
  apply RingHom.ext
  intro p
  let f := (Bialgebra.comulAlgHom ℤ (LaurentPolynomial ℤ)).toRingHom
  let g := multiplicativeGroupMultiplicationRingHom
  change f p = g p
  have hT1 : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1) := by
    simp [f, g, multiplicativeGroupMultiplicationRingHom,
      Algebra.TensorProduct.tmul_mul_tmul]
  have hT (n : ℤ) : f (LaurentPolynomial.T n) = g (LaurentPolynomial.T n) := by
    induction n using Int.induction_on with
    | zero => simp
    | succ i ih => rw [LaurentPolynomial.T_add, map_mul, map_mul, ih, hT1]
    | pred i ih =>
      refine ((LaurentPolynomial.isUnit_T (R := ℤ) 1).map g).mul_left_inj.1 ?_
      rw [← map_mul g, ← LaurentPolynomial.T_add, sub_add_cancel, ← ih, ← hT1, ← map_mul,
        ← LaurentPolynomial.T_add, sub_add_cancel]
  refine p.induction_on' (fun p q hp hq => ?_) (fun n a => ?_)
  · simpa only [map_add] using congrArg₂ (· + ·) hp hq
  · rw [map_mul, map_mul, hT]
    simp [f, g, multiplicativeGroupMultiplicationRingHom]

/-- **Stacks Project, Tag 022U.** Multiplication in the multiplicative group scheme is the
morphism induced by `T ↦ T ⊗ T` on Laurent polynomial coordinate rings. -/
@[stacks 022U "group_scheme"]
theorem multiplicativeGroupGrpObj_mul :
    μ[multiplicativeGroup.asOver (Spec (.of ℤ))].left =
      multiplicativeGroupMultiplication := by
  rw [AlgebraicGeometry.mul_spec_asOver_spec_left, multiplicativeGroupMultiplication]
  congr 1
  exact congrArg (fun f : LaurentPolynomial ℤ →+* _ => Spec.map (CommRingCat.ofHom f))
    multiplicativeGroupComul_eq_multiplicationRingHom

/-- **Stacks Project, Tag 022U.** The multiplicative group over `S` is the base change of
`Spec (ℤ[T, T⁻¹])` along the unique morphism from `S` to `Spec ℤ`. -/
@[stacks 022U "base_change"]
noncomputable abbrev multiplicativeGroupBaseChange (S : Scheme.{u}) : Scheme.{u} :=
  pullback (multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ)))
    (specULiftZIsTerminal.from S)

/-- The group-valued functor on `S`-schemes whose value is the group of units in the ring of
global sections of the underlying scheme. -/
@[sga "3 I 4.3.2"]
noncomputable def globalUnits (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  (Over.forget S).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
    forget₂ CommGrpCat GrpCat

/-- The Laurent coordinate `T`, regarded as an invertible global section of the integral
multiplicative group. -/
noncomputable def multiplicativeCoordinate :
    (Scheme.Γ.obj (Opposite.op (multiplicativeGroupULift : Scheme.{u})))ˣ :=
  ((LaurentPolynomial.isUnit_T (R := ULift.{u} ℤ) 1).map
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ)))).inv.hom).unit

/-- The unit obtained by pulling the Laurent coordinate back along a point of the integral
multiplicative group. -/
noncomputable def multiplicativeGroupPointUnit {T : Scheme.{u}}
    (g : T ⟶ multiplicativeGroupULift) : (Scheme.Γ.obj (Opposite.op T))ˣ :=
  Units.map (Scheme.Γ.map g.op).hom multiplicativeCoordinate

@[sga "3 I 4.3.2" "partial"]
private theorem canonicalRepresentation_homEquiv_eq_coordinate {T : Scheme.{u}}
    (g : T ⟶ multiplicativeGroupULift) :
    unitsOfGlobalSectionsCanonicalRepresentation.homEquiv g =
      multiplicativeGroupPointUnit g := by
  let F := Scheme.Γ ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙ forget CommGrpCat
  let h : F.RepresentableBy multiplicativeGroupULift :=
    unitsOfGlobalSectionsCanonicalRepresentation
  let coord : F.obj (Opposite.op multiplicativeGroupULift) := multiplicativeCoordinate
  have hid : h.homEquiv (𝟙 multiplicativeGroupULift) = coord := by
    let R : CommRingCat.{u} := CommRingCat.of (ULift.{u} ℤ)
    let G : CommGrpCat.{u} := CommGrpCat.of (Multiplicative (ULift.{u} ℤ))
    let A := Adjunction.comp CommGrpCat.forget₂CommMonAdj
      (CommRingCat.forget₂Adj (R := R) CommRingCat.isInitial)
    let B : CommRingCat.{u} := CommRingCat.of
      (MonoidAlgebra (ULift.{u} ℤ) (Multiplicative (ULift.{u} ℤ)))
    let d : Additive (Multiplicative (ULift.{u} ℤ)) ≃+ ℤ :=
      { toFun := fun x => x.toMul.down
        invFun := fun n => Additive.ofMul (Multiplicative.ofAdd (ULift.up n))
        left_inv := by intro x; cases x; rfl
        right_inv := fun _ => rfl
        map_add' := by
          intro x y
          rw [toMul_add]
          exact congrArg (fun z : Additive (Multiplicative (ULift.{u} ℤ)) =>
            z.toMul.toAdd.down) (ofMul_mul x.toMul y.toMul) }
    let E := ((MonoidAlgebra.toAdditiveAlgEquiv (ULift.{u} ℤ) (ULift.{u} ℤ)
        (Multiplicative (ULift.{u} ℤ))).trans
      (AddMonoidAlgebra.domCongr (ULift.{u} ℤ) (ULift.{u} ℤ) d)).toRingEquiv
    let iso := Scheme.Spec.mapIso (E.toCommRingCatIso.op)
    let X : Scheme.{u} := Scheme.Spec.obj
      (Opposite.op (CommRingCat.of (AddMonoidAlgebra (ULift.{u} ℤ) ℤ)))
    let S := (Scheme.Γ.rightOp.obj X).unop
    let H : Type u := (CommMonCat.units.obj ((forget₂ CommRingCat CommMonCat).obj S) : Type u)
    let e := AlgebraicGeometry.ΓSpec.adjunction.homEquiv X (Opposite.op B)
    let eA : (B ⟶ S) ≃ (G ⟶ CommMonCat.units.obj
        ((forget₂ CommRingCat CommMonCat).obj S)) := A.homEquiv G S
    let φ : B ⟶ S := (e.symm iso.hom).unop
    have hphi : (e.symm iso.hom).unop =
        E.toCommRingCatIso.hom ≫ (Scheme.ΓSpecIso
          (CommRingCat.of (AddMonoidAlgebra (ULift.{u} ℤ) ℤ))).inv := by
      apply Quiver.Hom.op_inj
      apply e.injective
      change e (e.symm iso.hom) = _
      calc
        e (e.symm iso.hom) = iso.hom := e.apply_symm_apply _
        _ = e ((E.toCommRingCatIso.hom ≫ (Scheme.ΓSpecIso
            (CommRingCat.of (AddMonoidAlgebra (ULift.{u} ℤ) ℤ))).inv).op) := by
          change Spec.map E.toCommRingCatIso.hom =
            (Spec (CommRingCat.of (AddMonoidAlgebra (ULift.{u} ℤ) ℤ))).toSpecΓ ≫
              Spec.map (E.toCommRingCatIso.hom ≫
              (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra (ULift.{u} ℤ) ℤ))).inv)
          have hspec := (AlgebraicGeometry.SpecMap_ΓSpecIso_hom
            (CommRingCat.of (AddMonoidAlgebra (ULift.{u} ℤ) ℤ))).symm
          rw [hspec, ← Spec.map_comp]
          simp [Category.assoc]
    let gen : Multiplicative (ULift.{u} ℤ) := Multiplicative.ofAdd (ULift.up 1)
    have hgen (φ : B ⟶ S) :
        ((A.homEquiv G S φ).hom gen).val =
          (CommRingCat.Hom.hom φ) (MonoidAlgebra.single gen 1) := by
      change ((CommGrpCat.Hom.hom
          (A.unit.app G ≫ CommMonCat.units.map ((forget₂ CommRingCat CommMonCat).map φ)))
          gen).val = (CommRingCat.Hom.hom φ) (MonoidAlgebra.single gen 1)
      rw [Adjunction.comp_unit_app]
      change (CommRingCat.Hom.hom φ)
        (MonoidAlgebra.of (ULift.{u} ℤ) (Multiplicative (ULift.{u} ℤ)) gen) = _
      rfl
    have hunit (f : G ⟶ CommMonCat.units.obj
        ((forget₂ CommRingCat CommMonCat).obj S)) :
        (unitsHomEquiv H (CommGrpCat.Hom.hom f)).val = ((CommGrpCat.Hom.hom f) gen).val := by
      simp [unitsHomEquiv, gen]
      rfl
    have hE : E (MonoidAlgebra.single gen (1 : ULift.{u} ℤ)) = LaurentPolynomial.T 1 := by
      change AddMonoidAlgebra.domCongr (ULift.{u} ℤ) (ULift.{u} ℤ) d
        (MonoidAlgebra.toAdditiveAlgEquiv (ULift.{u} ℤ) (ULift.{u} ℤ)
          (Multiplicative (ULift.{u} ℤ)) (MonoidAlgebra.single gen 1)) = _
      rw [MonoidAlgebra.toAdditiveAlgEquiv_single, AddMonoidAlgebra.domCongr_single]
      rfl
    apply Units.ext
    change (unitsHomEquiv H (eA φ).hom).val =
      (Scheme.ΓSpecIso
        (CommRingCat.of (AddMonoidAlgebra (ULift.{u} ℤ) ℤ))).inv.hom
          (AddMonoidAlgebra.single (1 : ℤ) (1 : ULift.{u} ℤ))
    rw [hunit]
    change ((CommGrpCat.Hom.hom ((A.homEquiv G S) ((e.symm iso.hom).unop))) gen).val = _
    rw [hgen ((e.symm iso.hom).unop)]
    change (CommRingCat.Hom.hom ((e.symm iso.hom).unop))
      (MonoidAlgebra.single gen (1 : ULift.{u} ℤ)) = _
    rw [hphi]
    change (Scheme.ΓSpecIso
      (CommRingCat.of (AddMonoidAlgebra (ULift.{u} ℤ) ℤ))).inv.hom
        (E (MonoidAlgebra.single gen (1 : ULift.{u} ℤ))) =
      (Scheme.ΓSpecIso
      (CommRingCat.of (AddMonoidAlgebra (ULift.{u} ℤ) ℤ))).inv.hom
        (AddMonoidAlgebra.single (1 : ℤ) (1 : ULift.{u} ℤ))
    rw [hE]
    rfl
  rw [h.homEquiv_eq g, hid]
  dsimp [F, coord, multiplicativeGroupPointUnit]
  rfl

/-- The base-changed multiplicative group represents the functor of global units. This datum is
used to give it its canonical group-object structure; its canonical orientation is specified by
`AlgebraicGeometry.baseChangePointsIsoGlobalUnits_hom_app`. -/
@[ega "IV 20.2.8" "partial"]
noncomputable def multiplicativeGroupBaseChangeRepresentsGlobalUnits (S : Scheme.{u}) :
    (globalUnits S ⋙ forget GrpCat).RepresentableBy
      (Scheme.asOver (multiplicativeGroupBaseChange S) S) := by
  let h := unitsOfGlobalSectionsCanonicalRepresentation
  refine ⟨?_, ?_⟩
  · intro X
    refine
      { toFun := fun f => h.homEquiv (f.left ≫ pullback.fst
          (multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ)))
          (specULiftZIsTerminal.from S))
        invFun := fun x => Over.homMk
          (pullback.lift (h.homEquiv.symm x) X.hom (by
            apply specULiftZIsTerminal.hom_ext))
          (by
            change pullback.lift (h.homEquiv.symm x) X.hom _ ≫ pullback.snd _ _ = X.hom
            exact pullback.lift_snd _ _ _)
        left_inv := fun f => by
          apply Over.OverMorphism.ext
          change pullback.lift
            (h.homEquiv.symm (h.homEquiv
              (f.left ≫ pullback.fst (multiplicativeGroupULift ↘
                Spec (.of (ULift.{u} ℤ))) (specULiftZIsTerminal.from S)))) X.hom _ = f.left
          apply pullback.hom_ext
          · rw [pullback.lift_fst, Equiv.symm_apply_apply]
            rfl
          · rw [pullback.lift_snd]
            exact (Over.w f).symm
        right_inv := fun x => by
          change (Scheme.Γ ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
            forget CommGrpCat).obj (Opposite.op X.left) at x
          change h.homEquiv
            (pullback.lift (h.homEquiv.symm x) X.hom _ ≫ pullback.fst _ _) = x
          rw [pullback.lift_fst, Equiv.apply_symm_apply] }
  · intro X Y f g
    change h.homEquiv (f.left ≫ g.left ≫ pullback.fst _ _) =
      ((Scheme.Γ ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
        forget CommGrpCat).map f.left.op) (h.homEquiv (g.left ≫ pullback.fst _ _))
    rw [h.homEquiv_comp]

/-- **Stacks Project, Tag 022U.** The base change of the multiplicative group to any scheme `S`
is a group scheme over `S`. Its structure is induced by the specified representation of the
group-valued global-units functor, and hence is not an arbitrary transported group law. -/
@[stacks 022U "base_change", sga "3 I 4.3.2"]
noncomputable instance multiplicativeGroupBaseChangeGrpObj (S : Scheme.{u}) :
    GrpObj (Scheme.asOver (multiplicativeGroupBaseChange S) S) :=
  GrpObj.ofRepresentableBy _ (globalUnits S)
    (multiplicativeGroupBaseChangeRepresentsGlobalUnits S)

/-- **Stacks Project, Tag 022U.** For every `S`-scheme `T`, the universal property of base change
canonically identifies `S`-morphisms from `T` to the multiplicative group over `S` with scheme
morphisms from `T` to the integral multiplicative group. The natural isomorphism records
compatibility with every morphism of `S`-schemes. -/
@[stacks 022U "base_change"]
noncomputable def baseChangePointsIsoMultiplicativeGroupPoints (S : Scheme.{u}) :
    yoneda.obj (Scheme.asOver (multiplicativeGroupBaseChange S) S) ≅
      (Over.forget S).op ⋙ yoneda.obj multiplicativeGroupULift := by
  refine NatIso.ofComponents (fun T => Equiv.toIso ?_) ?_
  · exact
      { toFun := fun f => f.left ≫ pullback.fst
          (multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ)))
          (specULiftZIsTerminal.from S)
        invFun := fun g => Over.homMk
          (pullback.lift g T.unop.hom (by apply specULiftZIsTerminal.hom_ext))
          (by
            change pullback.lift g T.unop.hom _ ≫ pullback.snd _ _ = T.unop.hom
            exact pullback.lift_snd _ _ _)
        left_inv := fun f => by
          apply Over.OverMorphism.ext
          change pullback.lift
            (f.left ≫ pullback.fst (multiplicativeGroupULift ↘
              Spec (.of (ULift.{u} ℤ))) (specULiftZIsTerminal.from S)) T.unop.hom _ = f.left
          apply pullback.hom_ext
          · rw [pullback.lift_fst]
            rfl
          · rw [pullback.lift_snd]
            exact (Over.w f).symm
        right_inv := fun g => by
          change pullback.lift g T.unop.hom _ ≫ pullback.fst _ _ = g
          rw [pullback.lift_fst] }
  · intro X Y f
    ext g
    rfl

/-- The forward map in `AlgebraicGeometry.baseChangePointsIsoMultiplicativeGroupPoints` is
composition with the first pullback projection. This characterizes the isomorphism and its
canonical orientation. -/
@[stacks 022U "base_change"]
theorem baseChangePointsIsoMultiplicativeGroupPoints_hom_app
    (S : Scheme.{u}) (T : (Over S)ᵒᵖ)
    (f : T.unop ⟶ Scheme.asOver (multiplicativeGroupBaseChange S) S) :
    (baseChangePointsIsoMultiplicativeGroupPoints S).hom.app T f =
      f.left ≫ pullback.fst
        (multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ)))
        (specULiftZIsTerminal.from S) :=
  rfl

/-- **Stacks Project, Tag 022U.** The group of `T`-points of the multiplicative group over `S` is
canonically the unit group `Γ(T, 𝒪_T)ˣ`, naturally in the `S`-scheme `T`. -/
@[stacks 022U "base_change", sga "3 I 4.3.2" "G_{m,S}(T)=Γ(T,O_T)^*"]
noncomputable def baseChangePointsIsoGlobalUnits (S : Scheme.{u}) :
    yonedaGrpObj (Scheme.asOver (multiplicativeGroupBaseChange S) S) ≅ globalUnits S :=
  yonedaGrpObjIsoOfRepresentableBy _ _
    (multiplicativeGroupBaseChangeRepresentsGlobalUnits S)

/-- The forward map in `AlgebraicGeometry.baseChangePointsIsoGlobalUnits` sends a point to the
pullback of the Laurent coordinate along its composite with the first pullback projection.
Besides characterizing the natural isomorphism, this pins down the multiplication on the group
scheme as multiplication of global units. -/
@[stacks 022U "base_change"]
theorem baseChangePointsIsoGlobalUnits_hom_app
    (S : Scheme.{u}) (T : (Over S)ᵒᵖ)
    (f : T.unop ⟶ Scheme.asOver (multiplicativeGroupBaseChange S) S) :
    (baseChangePointsIsoGlobalUnits S).hom.app T f =
    multiplicativeGroupPointUnit
        (f.left ≫ pullback.fst
          (multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ)))
          (specULiftZIsTerminal.from S)) := by
  change (multiplicativeGroupBaseChangeRepresentsGlobalUnits S).homEquiv f = _
  dsimp [multiplicativeGroupBaseChangeRepresentsGlobalUnits]
  exact canonicalRepresentation_homEquiv_eq_coordinate _

end AlgebraicGeometry
