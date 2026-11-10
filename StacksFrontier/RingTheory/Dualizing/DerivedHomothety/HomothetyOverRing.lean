module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.Homothety
public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom

/-!
# The derived homothety of the adjunction over a ring

The biduality criterion `Dualizing.isIso_dualizingBidualityMor` of [stacks 0A7C] is stated for
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, the derived-Hom adjunction in which the
ring universe and the module universe are independent. Its first hypothesis is invertibility of
the derived homothety `A ⟶ RHom_A(ω, ω)` there, and
`Dualizing.isIso_derivedHomothety_overRing` reduces that to the same statement for the
model-level adjunction over `ULift A`, at the image of `ω` under the inverse of the scalar
equivalence — because `derivedHomAdjunctionOverRing` is by construction the transport of the
model-level adjunction along that equivalence.

`Dualizing.isIso_derivedHomothety_of_isDualizingComplex` settles the model-level statement from a
dualizing hypothesis, but over `ULift A` rather than over `A`. This file closes the gap by moving
the dualizing data itself: the inverse of the scalar equivalence is restriction of scalars along
the ring isomorphism `ULift A ≃+* A`, so it carries a bounded complex of injective `A`-modules to
a bounded complex of injective `ULift A`-modules with the same terms, and it carries the scalar
homothety to the scalar homothety. The only thing to check is that the resulting square commutes:
restriction of scalars acts on cochains by applying the functor termwise
(`Dualizing.endomorphismComplexRestrictScalarsMap`, an isomorphism because restriction along a
ring isomorphism is an equivalence and hence bijective on cochains), the degree-zero sources are
identified by the additive isomorphism induced by the ring isomorphism, and both composites send
a scalar `a` to the cochain `a • 𝟙`.

## Main definitions

* `Dualizing.endomorphismComplexRestrictScalarsMap` — the comparison of lifted endomorphism
  complexes induced by restriction of scalars along a ring homomorphism.
* `Dualizing.liftedRingIsoHom` — the induced isomorphism of the degree-zero sources.

## Main results

* `Dualizing.homothety_restrictScalars` — restriction of scalars along a ring isomorphism carries
  the scalar homothety to the scalar homothety.
* `Dualizing.quasiIso_homothety_restrictScalars` — hence the two scalar homotheties are
  quasi-isomorphisms together.
* `Dualizing.isIso_derivedHomothety_overRing_of_isDualizingComplex` — the derived homothety of
  the adjunction of [stacks 0A63] at a dualizing complex is invertible. This is the first
  hypothesis of the biduality criterion of [stacks 0A7C].
* `Dualizing.isIso_evaluation_self_overRing_of_isDualizingComplex` — the evaluation morphism of
  that adjunction at `(ω, ω)` is an isomorphism for a dualizing complex `ω`.

## References

* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

universe w x u v

namespace Dualizing

/-! ### Restriction of scalars along a ring isomorphism -/

section RestrictScalars

variable {R : Type w} {S : Type x} [CommRing R] [CommRing S] (e : S ≃+* R)

/-- Restriction of scalars along a ring homomorphism acts on cochains termwise, and so induces a
map of lifted endomorphism complexes. -/
def endomorphismComplexRestrictScalarsMap (I : CochainComplex (ModuleCat.{max w x} R) ℤ) :
    liftedEndomorphismComplex I ⟶
      liftedEndomorphismComplex
        (((ModuleCat.restrictScalars.{max w x} e.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) := by
  refine { f := ?_, comm' := ?_ }
  · intro n
    exact AddCommGrpCat.ofHom
      { toFun := fun z ↦
          ULift.up (z.down.map (ModuleCat.restrictScalars.{max w x} e.toRingHom))
        map_zero' := ULift.ext (CochainComplex.HomComplex.Cochain.map_zero I I n
          (ModuleCat.restrictScalars.{max w x} e.toRingHom))
        map_add' := fun z z' ↦ ULift.ext (CochainComplex.HomComplex.Cochain.map_add
          z.down z'.down (ModuleCat.restrictScalars.{max w x} e.toRingHom)) }
  · intro n m _
    ext z
    exact ULift.ext (CochainComplex.HomComplex.δ_map n m z.down
      (ModuleCat.restrictScalars.{max w x} e.toRingHom))

/-- Restriction of scalars along a ring *isomorphism* is an equivalence, hence bijective on
cochains, so `Dualizing.endomorphismComplexRestrictScalarsMap` is an isomorphism. -/
instance isIso_endomorphismComplexRestrictScalarsMap
    (I : CochainComplex (ModuleCat.{max w x} R) ℤ) :
    IsIso (endomorphismComplexRestrictScalarsMap e I) := by
  have : (ModuleCat.restrictScalars.{max w x} e.toRingHom).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
  have h (n : ℤ) : IsIso ((endomorphismComplexRestrictScalarsMap e I).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr <|
      (Equiv.ulift.symm.bijective.comp
        (cochainAddEquivOfFullyFaithful
          (ModuleCat.restrictScalars.{max w x} e.toRingHom) I I n).bijective).comp
        Equiv.ulift.bijective
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The isomorphism of the degree-zero sources of the two scalar homotheties, induced by the ring
isomorphism. -/
def liftedRingIsoHom :
    AddCommGrpCat.of (ULift.{max w x} R) ⟶ AddCommGrpCat.of (ULift.{max w x} S) :=
  AddCommGrpCat.ofHom
    { toFun := fun a ↦ ULift.up (e.symm a.down)
      map_zero' := by ext; simp
      map_add' := fun _ _ ↦ by ext; simp }

/-- The map `Dualizing.liftedRingIsoHom e`, induced by the ring isomorphism `e`, is an
isomorphism. -/
instance isIso_liftedRingIsoHom : IsIso (liftedRingIsoHom e) := by
  apply (ConcreteCategory.isIso_iff_bijective (liftedRingIsoHom e)).mpr
  refine ⟨fun a b hab ↦ ?_, fun b ↦ ⟨ULift.up (e b.down), ?_⟩⟩
  · exact ULift.ext (e.symm.injective (congrArg ULift.down hab))
  · exact ULift.ext (e.symm_apply_apply b.down)

/-- Restriction of scalars along a ring isomorphism carries the scalar homothety to the scalar
homothety: both composites send a scalar `a` to the cochain `a • 𝟙`, the two scalar actions
agreeing through the ring isomorphism. -/
theorem homothety_restrictScalars (I : CochainComplex (ModuleCat.{max w x} R) ℤ) :
    homothety I ≫ endomorphismComplexRestrictScalarsMap e I =
      ((CochainComplex.singleFunctor AddCommGrpCat 0).map (liftedRingIsoHom e)) ≫
        homothety
          (((ModuleCat.restrictScalars.{max w x} e.toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I) := by
  apply HomologicalComplex.from_single_hom_ext
  ext a
  apply ULift.ext
  apply CochainComplex.HomComplex.Cochain.ext₀
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  simp only [HomologicalComplex.comp_f, AddCommGrpCat.comp_apply]
  rw [homothety_f_zero_apply_source I a, homothety_f_zero_apply_source _]
  change (((a.down • CochainComplex.HomComplex.Cochain.ofHom (𝟙 I)).map
      (ModuleCat.restrictScalars.{max w x} e.toRingHom)).v n n (add_zero n)).hom y =
    (((e.symm a.down) • CochainComplex.HomComplex.Cochain.ofHom
      (𝟙 (((ModuleCat.restrictScalars.{max w x} e.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I))).v n n (add_zero n)).hom y
  rw [CochainComplex.HomComplex.Cochain.map_v, CochainComplex.HomComplex.Cochain.smul_v,
    CochainComplex.HomComplex.Cochain.smul_v, CochainComplex.HomComplex.Cochain.ofHom_v,
    CochainComplex.HomComplex.Cochain.ofHom_v]
  let yR : I.X n := y
  change a.down • yR = e (e.symm a.down) • yR
  rw [e.apply_symm_apply]

/-- The scalar homothety of a complex and the scalar homothety of its restriction along a ring
isomorphism are quasi-isomorphisms together: the two differ by isomorphisms on both sides. -/
theorem quasiIso_homothety_restrictScalars (I : CochainComplex (ModuleCat.{max w x} R) ℤ)
    (hI : QuasiIso (homothety I)) :
    QuasiIso (homothety
      (((ModuleCat.restrictScalars.{max w x} e.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)) := by
  have hcomp : QuasiIso (homothety I ≫ endomorphismComplexRestrictScalarsMap e I) :=
    inferInstance
  rw [homothety_restrictScalars e I] at hcomp
  exact quasiIso_of_comp_left
    ((CochainComplex.singleFunctor AddCommGrpCat 0).map (liftedRingIsoHom e)) _

end RestrictScalars

/-! ### The derived homothety at a dualizing complex -/

section Transport

/-- If `ω` is a dualizing complex over `R` and `e : S ≃+* R`, then the derived homothety of any
model-level derived-Hom adjunction over `S` is invertible at the image of `ω` under restriction
of scalars along `e`. -/
theorem isIso_derivedHomothety_of_restrictScalars_isDualizingComplex
    {R : Type w} {S : Type (max w x)} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (e : S ≃+* R) (d : StacksDraft.DerivedHom.DerivedHomData S)
    (ω : DerivedCategory (ModuleCat.{max w x} R)) (hω : IsDualizingComplex ω) :
    IsIso (derivedHomothety d.toDerivedHomAdjunction
      (DerivedCategory.Q.obj (𝟙_ (StacksDraft.DerivedHom.Model.Complex S))) d.tensorUnitLeft
      ((ModuleCat.restrictScalars.{max w x} e.toRingHom).mapDerivedCategory.obj ω)) := by
  let Φ : ModuleCat.{max w x} R ⥤ ModuleCat.{max w x} S :=
    ModuleCat.restrictScalars.{max w x} e.toRingHom
  have hΦ : Φ.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
  obtain ⟨a, b, I, hge, hle, hinj, ⟨eI⟩⟩ := hω.finiteInjectiveDimension
  have : I.IsStrictlyGE a := hge
  have : ∀ i : ℤ, Injective (I.X i) := hinj
  have hJge : CochainComplex.IsStrictlyGE
      ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) a :=
    (CochainComplex.isStrictlyGE_iff _ a).mpr fun i hi ↦
      Φ.map_isZero ((CochainComplex.isStrictlyGE_iff I a).mp hge i hi)
  have hJinj (i : ℤ) :
      Injective (((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I).X i) :=
    Φ.injective_obj_of_injective (hinj i)
  exact isIso_derivedHomothety_of_injectiveRepresentative d _
    ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) a
    ((Φ.mapDerivedCategoryFactors.app I).symm ≪≫ (Φ.mapDerivedCategory.mapIso eI).symm)
    (quasiIso_homothety_restrictScalars e I
      (hω.homothetyQuasiIso I ⟨eI.symm⟩ hinj ⟨a, b, hge, hle⟩))

end Transport

section OverRing

variable (A : Type u) [CommRing A] [IsNoetherianRing A]

/-- **The first hypothesis of the biduality criterion of [stacks 0A7C], from the dualizing
hypothesis of [stacks 0A7B].** The derived homothety `A ⟶ RHom_A(ω, ω)` of the adjunction of
[stacks 0A63] is invertible when `ω` is a dualizing complex. -/
theorem isIso_derivedHomothety_overRing_of_isDualizingComplex
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω) :
    IsIso (derivedHomothety (derivedHomAdjunctionOverRing A) (derivedTensorUnit A)
      (derivedTensorUnitLeft A) ω) :=
  isIso_derivedHomothety_overRing A ω
    (isIso_derivedHomothety_of_restrictScalars_isDualizingComplex
      (ULift.ringEquiv : ULift.{v} A ≃+* A) _ ω hω)

/-- **The evaluation morphism of [stacks 0A63] at `(ω, ω)` is an isomorphism for a dualizing
complex.** It is unconditional.

It is the case `K' = K` of the evaluation hypothesis `hev` of
`Stacks.SheafOfModules.exists_isInvertible_tensor_iso_of_affineLocal` ([stacks 0ATP]) read over a
Noetherian ring, before the transport to `Spec A`. The notes in
`StacksFrontier/AlgebraicGeometry/Duality/GlobalDualizingUniqueness.lean` and
`StacksFrontier/RingTheory/Dualizing/Biduality.lean` that record the homothety half as open are out
of date, and this is the composition they say is missing. -/
theorem isIso_evaluation_self_overRing_of_isDualizingComplex
    (ω : DerivedCategory (ModuleCat.{max u v} A)) (hω : IsDualizingComplex ω) :
    IsIso ((derivedHomAdjunctionOverRing A).evaluation ω ω) :=
  isIso_evaluation_self_overRing A ω
    (isIso_derivedHomothety_overRing_of_isDualizingComplex A ω hω)

end OverRing

end Dualizing

end
