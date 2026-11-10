module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.RepresentedBy
public import StacksCore.Tactic.StacksAttribute

/-!
# The additive group scheme

The additive group over the integers is the affine line `Spec (ℤ[X])`, with addition induced on
coordinate rings by `X ↦ X ⊗ 1 + 1 ⊗ X`. It is a group scheme over the integers, its base change
to an arbitrary scheme `S` is a group scheme over `S`, and the functor of points of that base
change is the additive group of global sections.

## Main definitions

* `AlgebraicGeometry.additiveGroup` is the scheme `Spec (ℤ[X])`.
* `AlgebraicGeometry.additionRingHom` is the map on coordinate rings defining addition, and
  `AlgebraicGeometry.additionMorphism` the resulting morphism from the fibre product of two
  copies of the additive group.
* `AlgebraicGeometry.additiveGroupBaseChange` is the additive group scheme over an arbitrary
  base scheme.
* `AlgebraicGeometry.globalSectionsAdditive` is the group-valued functor of global sections,
  with addition as its group operation, and `AlgebraicGeometry.additiveCoordinate` is the
  universal polynomial coordinate as a global section of the integral model.

## Main results

* `AlgebraicGeometry.additionMorphism_pullbackSpecIso` identifies the addition morphism, under
  the canonical affine fibre-product isomorphism, with the stated map on coordinate rings.
* `AlgebraicGeometry.additiveGroupGrpObj` is the group-object structure on the affine line over
  the integers, and `AlgebraicGeometry.additiveGroupGrpObj_mul` identifies its multiplication
  with the addition morphism.
* `AlgebraicGeometry.additiveGroupBaseChangeGrpObj` equips the base change with the canonical
  pullback group-scheme structure, and
  `AlgebraicGeometry.additiveGroupBaseChange_mul_fst` identifies multiplication of points after
  projection with the integral addition morphism.
* `AlgebraicGeometry.additiveGroupBaseChangePointsIsoGlobalSections` naturally identifies points
  of the additive group over `S` with global sections, and
  `AlgebraicGeometry.additiveGroupBaseChangePointsIsoGlobalSections_hom_app` specifies that
  identification by pullback of the universal coordinate.
* `AlgebraicGeometry.globalSections_representableBy_additiveGroup` records representability of
  the global-sections functor on the category of schemes.

## Implementation notes

At universe `u` the base ring is represented by `ULift.{u} ℤ`, the standard universe-polymorphic
copy of the integers, so the construction can be base-changed to an arbitrary `Scheme.{u}`; its
canonical morphism to the spectrum of that copy of `ℤ` is induced contravariantly by
`Polynomial.C`. The canonical isomorphism between the fibre product and the spectrum of the
tensor product is `AlgebraicGeometry.pullbackSpecIso`. The base change is expressed as a fibre
product over the terminal scheme `Spec ℤ`, and its group structure is defined using
`AlgebraicGeometry.Scheme.GrpObjAsOverPullback`, so all operations are induced by the integral
additive group structure.

The additive group of a ring is converted from additive to multiplicative notation in order to
compare it with Mathlib's group-valued Yoneda functor. The component formula fixes the canonical
orientation of the natural isomorphism and, together with its target category, records that the
group law is addition of sections.

## References

* [Stacks Project, Tag 022V](https://stacks.math.columbia.edu/tag/022V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
  CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 022V.** The underlying scheme of the additive group over the integers
is the spectrum of the polynomial ring `ℤ[X]`. -/
@[stacks 022V "additive_group_underlying_scheme", sga "3 I 4.3.1" "the scheme G_a"]
noncomputable abbrev additiveGroup : Scheme.{u} := Spec (.of (Polynomial (ULift.{u} ℤ)))

/-- The canonical structure morphism from the additive group scheme to the spectrum of the
universe-polymorphic copy of `ℤ`, induced by the inclusion of constant polynomials. -/
@[stacks 022V "additive_group_underlying_scheme"]
noncomputable instance additiveGroupCanonicallyOver :
    additiveGroup.CanonicallyOver (Spec (.of (ULift.{u} ℤ))) where
  hom := Spec.map (CommRingCat.ofHom Polynomial.C)

/-- The map on coordinate rings defining addition on the additive group: it sends `X` to
`X ⊗ 1 + 1 ⊗ X`. -/
noncomputable def additionRingHom :
    Polynomial (ULift.{u} ℤ) →+*
      TensorProduct (ULift.{u} ℤ) (Polynomial (ULift.{u} ℤ)) (Polynomial (ULift.{u} ℤ)) :=
  (Polynomial.aeval ((Algebra.TensorProduct.includeLeft :
    Polynomial (ULift.{u} ℤ) →ₐ[ULift.{u} ℤ]
      TensorProduct (ULift.{u} ℤ) (Polynomial (ULift.{u} ℤ))
        (Polynomial (ULift.{u} ℤ))) Polynomial.X +
    (Algebra.TensorProduct.includeRight :
      Polynomial (ULift.{u} ℤ) →ₐ[ULift.{u} ℤ]
        TensorProduct (ULift.{u} ℤ) (Polynomial (ULift.{u} ℤ))
          (Polynomial (ULift.{u} ℤ))) Polynomial.X)).toRingHom

/-- The addition morphism on the additive group scheme over the integers. -/
noncomputable def additionMorphism :
    pullback (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
        (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) ⟶ additiveGroup :=
  (pullbackSpecIso (ULift.{u} ℤ) (Polynomial (ULift.{u} ℤ))
    (Polynomial (ULift.{u} ℤ))).hom ≫ Spec.map (CommRingCat.ofHom additionRingHom)

/-- **Stacks Project, Tag 022V.** Under the canonical identification of the fibre product
with `Spec (R[X] ⊗[R] R[X])`, addition is induced by the ring map sending
`X` to `X ⊗ 1 + 1 ⊗ X`. -/
@[stacks 022V "addition_morphism", sga "3 I 4.3.1" "Δ(T)=T⊗1+1⊗T"]
lemma additionMorphism_pullbackSpecIso :
    (pullbackSpecIso (ULift.{u} ℤ) (Polynomial (ULift.{u} ℤ))
      (Polynomial (ULift.{u} ℤ))).inv ≫ additionMorphism =
      Spec.map (CommRingCat.ofHom additionRingHom) := by
  simp [additionMorphism]

/-- The group-object structure on the affine line over the integers. -/
@[stacks 022V "additive_group_scheme"]
noncomputable instance additiveGroupGrpObj :
    GrpObj (Over.mk (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))) := by
  let comul : Polynomial (ULift.{u} ℤ) →ₐ[ULift.{u} ℤ]
      TensorProduct (ULift.{u} ℤ) (Polynomial (ULift.{u} ℤ)) (Polynomial (ULift.{u} ℤ)) :=
    Polynomial.aeval ((Algebra.TensorProduct.includeLeft :
      Polynomial (ULift.{u} ℤ) →ₐ[ULift.{u} ℤ] _) Polynomial.X +
      (Algebra.TensorProduct.includeRight :
        Polynomial (ULift.{u} ℤ) →ₐ[ULift.{u} ℤ] _) Polynomial.X)
  let counit : Polynomial (ULift.{u} ℤ) →ₐ[ULift.{u} ℤ] ULift.{u} ℤ := Polynomial.aeval 0
  letI : Bialgebra (ULift.{u} ℤ) (Polynomial (ULift.{u} ℤ)) :=
    Bialgebra.ofAlgHom comul counit
      (by ext; simp [comul, Algebra.TensorProduct.one_def, TensorProduct.add_tmul,
        TensorProduct.tmul_add]; abel)
      (by ext; simp [comul, counit]) (by ext; simp [comul, counit])
  letI : HopfAlgebra (ULift.{u} ℤ) (Polynomial (ULift.{u} ℤ)) :=
    HopfAlgebra.ofAlgHom (Polynomial.aeval (-Polynomial.X))
      (by apply Polynomial.algHom_ext
          change (Algebra.TensorProduct.lift (Polynomial.aeval (-Polynomial.X))
            (AlgHom.id _ _) (fun _ _ ↦ Commute.all _ _)) (comul Polynomial.X) =
            Polynomial.C (counit Polynomial.X)
          simp [comul, counit])
      (by apply Polynomial.algHom_ext
          change (Algebra.TensorProduct.lift (AlgHom.id _ _)
            (Polynomial.aeval (-Polynomial.X)) (fun _ _ ↦ Commute.all _ _))
              (comul Polynomial.X) = Polynomial.C (counit Polynomial.X)
          simp [comul, counit])
  exact AlgebraicGeometry.instGrpObjSpecAsOverSpec

/-- **Stacks Project, Tag 022V.** Multiplication in the additive group scheme is the usual
addition morphism. -/
@[stacks 022V "additive_group_scheme"]
theorem additiveGroupGrpObj_mul :
    μ[Over.mk (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))].left = additionMorphism := rfl

/-- The additive group scheme over `S`, obtained by base change from the affine line over the
integers. -/
noncomputable abbrev additiveGroupBaseChange (S : Scheme.{u}) : Scheme.{u} :=
  pullback (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) (specULiftZIsTerminal.from S)

/-- **Stacks Project, Tag 022V.** The base change of the additive group scheme to every scheme
`S` is a group scheme over `S`, with the canonical pullbacks of the integral group operations. -/
@[stacks 022V "base_change_group_scheme", sga "3 I 4.3.1" "G_{a,S} group over S"]
noncomputable instance additiveGroupBaseChangeGrpObj (S : Scheme.{u}) :
    GrpObj (Scheme.asOver (additiveGroupBaseChange S) S) := by
  letI : GrpObj (Scheme.asOver additiveGroup (Spec (.of (ULift.{u} ℤ)))) := additiveGroupGrpObj
  exact Scheme.GrpObjAsOverPullback

/-- Projecting the product structure map of two points of the base change to the integral
additive group gives the pair of projected points. -/
private theorem additiveGroupBaseChange_lift_μ_left_fst (S : Scheme.{u}) {T : Over S}
    (f g : T ⟶ Scheme.asOver (additiveGroupBaseChange S) S) :
    (pullback.lift
        (f := pullback.snd (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
          (specULiftZIsTerminal.from S))
        (g := pullback.snd (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
          (specULiftZIsTerminal.from S))
        f.left g.left (f.w.trans g.w.symm) ≫
      (Functor.LaxMonoidal.μ (Over.pullback (specULiftZIsTerminal.from S))
        (Over.mk (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))))
        (Over.mk (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))))).left) ≫
      pullback.fst
        (pullback.fst (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
          (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) ≫
          (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))))
        (specULiftZIsTerminal.from S) =
    pullback.lift
      (f.left ≫ pullback.fst
        (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) (specULiftZIsTerminal.from S))
      (g.left ≫ pullback.fst
        (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) (specULiftZIsTerminal.from S))
      (specULiftZIsTerminal.hom_ext _ _) := by
  have hff :
      (Functor.LaxMonoidal.μ (Over.pullback (specULiftZIsTerminal.from S))
          (Over.mk (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))))
          (Over.mk (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))))).left ≫
        pullback.fst
            (pullback.fst (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
              (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) ≫
              (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))))
            (specULiftZIsTerminal.from S) ≫
          pullback.fst (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
            (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) =
      pullback.fst
          (pullback.snd (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
            (specULiftZIsTerminal.from S))
          (pullback.snd (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
            (specULiftZIsTerminal.from S)) ≫
        pullback.fst (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
          (specULiftZIsTerminal.from S) :=
    Over.μ_pullback_left_fst_fst' _ _
  have hfs :
      (Functor.LaxMonoidal.μ (Over.pullback (specULiftZIsTerminal.from S))
          (Over.mk (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))))
          (Over.mk (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))))).left ≫
        pullback.fst
            (pullback.fst (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
              (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) ≫
              (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))))
            (specULiftZIsTerminal.from S) ≫
          pullback.snd (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
            (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) =
      pullback.snd
          (pullback.snd (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
            (specULiftZIsTerminal.from S))
          (pullback.snd (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
            (specULiftZIsTerminal.from S)) ≫
        pullback.fst (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
          (specULiftZIsTerminal.from S) :=
    Over.μ_pullback_left_fst_snd' _ _
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, hff]
    exact (pullback.lift_fst_assoc _ _ _ _).trans (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, Category.assoc, hfs]
    exact (pullback.lift_snd_assoc _ _ _ _).trans (pullback.lift_snd _ _ _).symm

/-- Projecting a product of points of the base change to the integral additive group gives
its addition morphism applied to the two projected points. -/
theorem additiveGroupBaseChange_mul_fst (S : Scheme.{u}) {T : Over S}
    (f g : T ⟶ Scheme.asOver (additiveGroupBaseChange S) S) :
    (f * g).left ≫ pullback.fst
        (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) (specULiftZIsTerminal.from S) =
      pullback.lift
        (f.left ≫ pullback.fst
          (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) (specULiftZIsTerminal.from S))
        (g.left ≫ pullback.fst
          (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) (specULiftZIsTerminal.from S))
        (specULiftZIsTerminal.hom_ext _ _) ≫ additionMorphism := by
  have hexp : (f * g).left ≫ pullback.fst
      (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) (specULiftZIsTerminal.from S) =
      pullback.lift
          (f := pullback.snd (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
            (specULiftZIsTerminal.from S))
          (g := pullback.snd (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
            (specULiftZIsTerminal.from S))
          f.left g.left (f.w.trans g.w.symm) ≫
        (Functor.LaxMonoidal.μ (Over.pullback (specULiftZIsTerminal.from S))
          (Over.mk (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))))
          (Over.mk (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))))).left ≫
        ((Over.pullback (specULiftZIsTerminal.from S)).map
          μ[Over.mk (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))]).left ≫
        pullback.fst (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
          (specULiftZIsTerminal.from S) := rfl
  have hmap :
      ((Over.pullback (specULiftZIsTerminal.from S)).map
        μ[Over.mk (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))]).left ≫
          pullback.fst (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
            (specULiftZIsTerminal.from S) =
      pullback.fst
          (pullback.fst (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
            (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) ≫
            (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))))
          (specULiftZIsTerminal.from S) ≫
        μ[Over.mk (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))].left :=
    pullback.lift_fst _ _ _
  rw [hexp, hmap, additiveGroupGrpObj_mul]
  simp only [← Category.assoc]
  rw [additiveGroupBaseChange_lift_μ_left_fst S f g]

/-- The group-valued functor on `S`-schemes which assigns to `T` the additive group of
`Γ(T, 𝒪_T)`, written multiplicatively. -/
@[sga "3 I 4.3.1"]
noncomputable abbrev globalSectionsAdditive (S : Scheme.{u}) : Functor (Over S)ᵒᵖ GrpCat.{u} :=
  (Over.forget S).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat ⋙
    forget₂ RingCat AddCommGrpCat ⋙ forget₂ AddCommGrpCat AddGrpCat ⋙ AddGrpCat.toGrp

/-- The polynomial variable, regarded as the universal global section on the integral additive
group. -/
noncomputable def additiveCoordinate :
    Scheme.Γ.obj (Opposite.op (additiveGroup : Scheme.{u})) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Polynomial (ULift.{u} ℤ)))).inv.hom Polynomial.X

/-- The global section obtained by pulling the universal additive coordinate back along a point
of the integral additive group. -/
noncomputable def additiveGroupPointSection {T : Scheme.{u}} (g : T ⟶ additiveGroup) :
    Scheme.Γ.obj (Opposite.op T) :=
  (Scheme.Γ.map g.op).hom additiveCoordinate

/-- Ring maps out of `ℤ[X]` (with universe-lifted integer coefficients) are determined by the
image of `X`. -/
private noncomputable def polynomialULiftIntRingHomEquiv (A : Type*) [CommRing A] :
    (Polynomial (ULift.{u} ℤ) →+* A) ≃ A where
  toFun φ := φ Polynomial.X
  invFun a :=
    (Polynomial.aeval a).toRingHom.comp (Polynomial.mapRingHom ULift.ringEquiv.toRingHom)
  left_inv φ := by
    apply Polynomial.ringHom_ext
    · intro a
      cases a with
      | up z =>
          change ((Polynomial.aeval (φ Polynomial.X)).toRingHom.comp
            (Polynomial.mapRingHom ULift.ringEquiv.toRingHom))
              (Polynomial.C (z : ULift.{u} ℤ)) =
            φ (Polynomial.C (z : ULift.{u} ℤ))
          rw [Polynomial.C_eq_intCast (R := ULift.{u} ℤ) z]
          calc
            _ = (z : A) := by simp
            _ = φ (z : Polynomial (ULift.{u} ℤ)) := (map_intCast φ z).symm
    · simp
  right_inv a := by simp [Polynomial.mapRingHom]

/-- The universal polynomial coordinate represents the global-sections functor. -/
theorem globalSectionsIsRepresentedBy :
    (Scheme.Γ.{u} ⋙ forget CommRingCat).IsRepresentedBy
      (X := additiveGroup) additiveCoordinate := by
  let R := Polynomial (ULift.{u} ℤ)
  rw [Functor.isRepresentedBy_iff]
  intro T
  let A := Scheme.Γ.obj (Opposite.op T)
  let eAdj : (T ⟶ Spec (.of R)) ≃ (R →+* A) :=
    (ΓSpec.adjunction.homEquiv T (Opposite.op (CommRingCat.of R))).symm.trans
      { toFun := fun φ => φ.unop.hom
        invFun := fun φ => (CommRingCat.ofHom φ).op
        left_inv := by
          intro φ
          cases φ
          rfl
        right_inv _ := rfl }
  have he : (fun f : T ⟶ Spec (.of R) => additiveGroupPointSection f) =
      eAdj.trans (polynomialULiftIntRingHomEquiv A) := by
    funext f
    have hφ := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
      (φ := CommRingCat.ofHom (eAdj f))
    have hAdj :
        (ΓSpec.adjunction.homEquiv T (Opposite.op (CommRingCat.of R)))
          (CommRingCat.ofHom (eAdj f)).op = f :=
      eAdj.symm_apply_apply f
    have hAdj' :
        (ΓSpec.adjunction.homEquiv (Opposite.unop (Opposite.op T))
          (Opposite.op (CommRingCat.of R)))
          (CommRingCat.ofHom (eAdj f)).op = f := by
      simpa using hAdj
    have hApp := congrArg Scheme.Hom.appTop hAdj'
    have hApp' :
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
          Scheme.Hom.appTop
            ((ΓSpec.adjunction.homEquiv T (Opposite.op (CommRingCat.of R)))
              (CommRingCat.ofHom (eAdj f)).op)).hom Polynomial.X =
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom Polynomial.X :=
      congrArg (fun ψ : CommRingCat.Hom _ _ =>
        (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ ψ).hom Polynomial.X)) hApp
    have hcoord := congrArg (fun ψ : CommRingCat.Hom _ _ => ψ.hom Polynomial.X) hφ
    exact hApp'.symm.trans hcoord
  change Function.Bijective (fun f : T ⟶ Spec (.of R) => additiveGroupPointSection f)
  rw [he]
  exact (eAdj.trans (polynomialULiftIntRingHomEquiv A)).bijective

/-- The integral additive group, as a representing object for the global-sections functor. -/
@[sga "3 I 4.3.1" "partial"]
noncomputable def globalSectionsRepresentableBy :
    (Scheme.Γ.{u} ⋙ forget CommRingCat).RepresentableBy (additiveGroup : Scheme.{u}) :=
  globalSectionsIsRepresentedBy.representableBy

/-- **Stacks Project, Tag 022V.** The set-valued global-sections functor on schemes is
represented by the additive group scheme `Spec (ℤ[X])`. -/
@[stacks 022V "representability", sga "3 I 4.3.1" "partial"]
theorem globalSections_representableBy_additiveGroup :
    Nonempty ((Scheme.Γ ⋙ forget CommRingCat).RepresentableBy (additiveGroup : Scheme.{u})) :=
  ⟨globalSectionsRepresentableBy⟩

/-- Pulling back a point pulls back its associated global section. -/
theorem additiveGroupPointSection_comp {T U : Scheme.{u}}
    (f : T ⟶ U) (g : U ⟶ additiveGroup) :
    additiveGroupPointSection (f ≫ g) = f.appTop.hom (additiveGroupPointSection g) := by
  change (f ≫ g).appTop.hom _ = _
  rw [Scheme.Hom.comp_appTop]
  rfl

private lemma additiveGroupPointSection_specMap {R : CommRingCat.{u}}
    (φ : CommRingCat.of (Polynomial (ULift.{u} ℤ)) ⟶ R) :
    additiveGroupPointSection (Spec.map φ) =
      (Scheme.ΓSpecIso R).inv.hom (φ.hom Polynomial.X) := by
  change ((Scheme.ΓSpecIso _).inv ≫ (Spec.map φ).appTop).hom Polynomial.X = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The integral addition morphism sends the universal coordinate to the sum of the
coordinates of the two factors. -/
theorem additiveGroupPointSection_addition {T : Scheme.{u}}
    (h : T ⟶ pullback (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
      (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))) :
    additiveGroupPointSection (h ≫ additionMorphism) =
      additiveGroupPointSection (h ≫ pullback.fst _ _) +
        additiveGroupPointSection (h ≫ pullback.snd _ _) := by
  have hfst :
      (pullbackSpecIso (ULift.{u} ℤ) (Polynomial (ULift.{u} ℤ))
        (Polynomial (ULift.{u} ℤ))).hom ≫
          Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) =
        pullback.fst (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
          (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) :=
    pullbackSpecIso_hom_fst _ _ _
  have hsnd :
      (pullbackSpecIso (ULift.{u} ℤ) (Polynomial (ULift.{u} ℤ))
        (Polynomial (ULift.{u} ℤ))).hom ≫
          Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) =
        pullback.snd (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
          (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) :=
    pullbackSpecIso_hom_snd _ _ _
  have e0 : h ≫ additionMorphism =
      (h ≫ (pullbackSpecIso (ULift.{u} ℤ) (Polynomial (ULift.{u} ℤ))
        (Polynomial (ULift.{u} ℤ))).hom) ≫
        Spec.map (CommRingCat.ofHom additionRingHom) :=
    (Category.assoc _ _ _).symm
  have e1 : h ≫ pullback.fst (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
        (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) =
      (h ≫ (pullbackSpecIso (ULift.{u} ℤ) (Polynomial (ULift.{u} ℤ))
        (Polynomial (ULift.{u} ℤ))).hom) ≫
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) :=
    (congrArg (fun z => h ≫ z) hfst.symm).trans (Category.assoc _ _ _).symm
  have e2 : h ≫ pullback.snd (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
        (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) =
      (h ≫ (pullbackSpecIso (ULift.{u} ℤ) (Polynomial (ULift.{u} ℤ))
        (Polynomial (ULift.{u} ℤ))).hom) ≫
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) :=
    (congrArg (fun z => h ≫ z) hsnd.symm).trans (Category.assoc _ _ _).symm
  rw [e0, e1, e2, additiveGroupPointSection_comp, additiveGroupPointSection_comp,
    additiveGroupPointSection_comp, additiveGroupPointSection_specMap,
    additiveGroupPointSection_specMap, additiveGroupPointSection_specMap]
  simp only [additionRingHom, AlgHom.toRingHom_eq_coe, CommRingCat.hom_ofHom,
    RingHom.coe_coe, Polynomial.aeval_X, map_add]
  rfl

/-- The section associated to a product of points of the base-changed additive group is the
sum of their associated sections. -/
theorem additiveGroupBaseChangePointSection_mul (S : Scheme.{u}) {T : Over S}
    (f g : T ⟶ Scheme.asOver (additiveGroupBaseChange S) S) :
    additiveGroupPointSection
        ((f * g).left ≫ pullback.fst
          (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) (specULiftZIsTerminal.from S)) =
      additiveGroupPointSection
        (f.left ≫ pullback.fst
          (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) (specULiftZIsTerminal.from S)) +
      additiveGroupPointSection
        (g.left ≫ pullback.fst
          (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) (specULiftZIsTerminal.from S)) := by
  rw [additiveGroupBaseChange_mul_fst, additiveGroupPointSection_addition]
  simp only [pullback.lift_fst, pullback.lift_snd]

/-- The base-changed additive group, as a representing object for the functor of global
sections on `S`-schemes. -/
@[sga "3 I 4.3.1" "more general"]
noncomputable def additiveGroupBaseChangeRepresentableBy (S : Scheme.{u}) :
    (globalSectionsAdditive S ⋙ forget GrpCat).RepresentableBy
      (Scheme.asOver (additiveGroupBaseChange S) S) := by
  let h := globalSectionsRepresentableBy
  refine ⟨?_, ?_⟩
  · intro X
    refine
      { toFun := fun f => h.homEquiv (f.left ≫ pullback.fst
          (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) (specULiftZIsTerminal.from S))
        invFun := fun x => Over.homMk
          (pullback.lift (h.homEquiv.symm x) X.hom (specULiftZIsTerminal.hom_ext _ _))
          (by
            change pullback.lift (h.homEquiv.symm x) X.hom _ ≫ pullback.snd _ _ = X.hom
            exact pullback.lift_snd _ _ _)
        left_inv := fun f => by
          apply Over.OverMorphism.ext
          dsimp
          apply pullback.hom_ext
          · change pullback.lift
              (h.homEquiv.symm
                (h.homEquiv (f.left ≫ pullback.fst _ _))) X.hom _ ≫ pullback.fst _ _ = _
            rw [pullback.lift_fst, Equiv.symm_apply_apply]
            rfl
          · change pullback.lift _ X.hom _ ≫ pullback.snd _ _ = _
            rw [pullback.lift_snd]
            exact (Over.w f).symm
        right_inv := fun x => by
          change h.homEquiv
            (pullback.lift (h.homEquiv.symm x) X.hom _ ≫ pullback.fst _ _) = x
          rw [pullback.lift_fst]
          exact Equiv.apply_symm_apply _ _ }
  · intro X Y f g
    change h.homEquiv (f.left ≫ g.left ≫ pullback.fst _ _) =
      ((Scheme.Γ ⋙ forget CommRingCat).map f.left.op)
        (h.homEquiv (g.left ≫ pullback.fst _ _))
    rw [h.homEquiv_comp]

/-- The representing bijection sends an `S`-point of the base-changed additive group to the global
section associated with its projection to the integral additive group. -/
lemma additiveGroupBaseChangeRepresentableBy_apply (S : Scheme.{u}) {T : Over S}
    (f : T ⟶ Scheme.asOver (additiveGroupBaseChange S) S) :
    (additiveGroupBaseChangeRepresentableBy S).homEquiv f =
      additiveGroupPointSection
        (f.left ≫ pullback.fst
          (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) (specULiftZIsTerminal.from S)) := by
  change globalSectionsRepresentableBy.homEquiv
      (f.left ≫ pullback.fst
        (additiveGroup ↘ Spec (.of (ULift.{u} ℤ))) (specULiftZIsTerminal.from S)) = _
  rw [globalSectionsRepresentableBy, Functor.IsRepresentedBy.representableBy_homEquiv_apply]
  rfl

/-- Points of the base-changed additive group form the additive group of global sections. -/
noncomputable def additiveGroupBaseChangePointMulEquiv (S : Scheme.{u}) (T : (Over S)ᵒᵖ) :
    (T.unop ⟶ Scheme.asOver (additiveGroupBaseChange S) S) ≃*
      (globalSectionsAdditive S).obj T where
  toFun := (additiveGroupBaseChangeRepresentableBy S).homEquiv
  invFun := (additiveGroupBaseChangeRepresentableBy S).homEquiv.symm
  left_inv := (additiveGroupBaseChangeRepresentableBy S).homEquiv.left_inv
  right_inv := (additiveGroupBaseChangeRepresentableBy S).homEquiv.right_inv
  map_mul' f g := by
    rw [additiveGroupBaseChangeRepresentableBy_apply,
      additiveGroupBaseChangeRepresentableBy_apply,
      additiveGroupBaseChangeRepresentableBy_apply,
      additiveGroupBaseChangePointSection_mul]
    rfl

/-- **Stacks Project, Tag 022V.** For every scheme `S`, the group-valued functor of points of
the additive group scheme over `S` is naturally isomorphic to the additive group of global
sections of the varying `S`-scheme. -/
@[stacks 022V "relative_functor_of_points", sga "3 I 4.3.1" "more general"]
noncomputable def additiveGroupBaseChangePointsIsoGlobalSections (S : Scheme.{u}) :
    yonedaGrpObj (Scheme.asOver (additiveGroupBaseChange S) S) ≅ globalSectionsAdditive S :=
  NatIso.ofComponents
    (fun T => (additiveGroupBaseChangePointMulEquiv S T).toGrpIso)
    (by
      intro X Y f
      ext g
      change (additiveGroupBaseChangeRepresentableBy S).homEquiv (f.unop ≫ g) =
        (globalSectionsAdditive S).map f
          ((additiveGroupBaseChangeRepresentableBy S).homEquiv g)
      exact (additiveGroupBaseChangeRepresentableBy S).homEquiv_comp f.unop g)

/-- Under the canonical identification of additive-group points with global sections, a point is
sent to the pullback of the universal polynomial coordinate along its projection to the integral
additive group. This characterizes the natural isomorphism. -/
@[stacks 022V "relative_functor_of_points"]
theorem additiveGroupBaseChangePointsIsoGlobalSections_hom_app
    (S : Scheme.{u}) (T : (Over S)ᵒᵖ)
    (f : T.unop ⟶ Scheme.asOver (additiveGroupBaseChange S) S) :
    (additiveGroupBaseChangePointsIsoGlobalSections S).hom.app T f =
      additiveGroupPointSection
        (f.left ≫ pullback.fst
          (additiveGroup ↘ Spec (.of (ULift.{u} ℤ)))
          (specULiftZIsTerminal.from S)) := by
  unfold additiveGroupBaseChangePointsIsoGlobalSections
  change (additiveGroupBaseChangeRepresentableBy S).homEquiv f = _
  exact additiveGroupBaseChangeRepresentableBy_apply S f

end AlgebraicGeometry
