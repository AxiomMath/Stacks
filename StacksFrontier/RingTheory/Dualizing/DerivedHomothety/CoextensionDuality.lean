module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.DiagonalModelHom

/-!
# Coextension duality at a general first argument

Let `f : A →+* B` be a homomorphism of commutative rings. Coextension of scalars
`Hom_A(B, -) : Mod(A) ⥤ Mod(B)` is right adjoint to restriction of scalars, and its total right
derived functor `RHom_A(B, -) : D(A) ⥤ D(B)` is right adjoint to restriction of scalars on derived
categories. Deriving the adjunction in its internal form gives the coextension duality formula

`RHom_B(K, RHom_A(B, M)) = RHom_A(K, M)` ,

an isomorphism of objects of `D(A)`: on the left the internal derived Hom is formed in `D(B)` out
of an arbitrary object `K` of `D(B)` and then read in `D(A)`, and on the right it is formed in
`D(A)` out of the restriction of scalars of `K`. At `K = RHom_A(B, M)` it identifies the derived
endomorphisms of a derived coextension with a double dual over `A`.

## Main definitions

* `Dualizing.cochainCoextendLinearEquiv`: the adjunction bijection on cochains: degree-`n`
  cochains from `K` into the degreewise coextension `Hom_A(B, I)` are degree-`n` cochains from
  `K` read over `A` into `I`.
* `Dualizing.restrictHomComplexCoextendIso`: the same, assembled into an isomorphism of
  complexes of `A`-modules `Hom^•_B(K, Hom_A(B, I))_A ≅ Hom^•_A(K_A, I)`.
* `Dualizing.modelHomCoextendIsoRestrictScalars`: the coextension duality formula at chosen
  representatives: for a cochain complex `K` representing an object of `D(B)` and a K-injective
  complex `I` representing an object `M` of `D(A)`, `RHom_A(K_A, M) ≅ RHom_B(K, RHom_A(B, M))_A`.

## Main results

* `Dualizing.nonempty_modelHomCoextendIsoRestrictScalars`: the coextension duality formula for
  arbitrary objects of `D(B)` and `D(A)`.
* `Dualizing.nonempty_modelHomCoextend_iso_iff`: consequently the two objects of `D(A)` are
  isomorphic to the same objects.
* `Dualizing.nonempty_modelHom_derivedHom_self_iso_doubleDual`:
  `RHom_B(RHom_A(B, M), RHom_A(B, M))_A ≅ RHom_A(RHom_A(B[0], M), M)`.

## Implementation notes

Both sides are computed on one pair of complexes: a K-injective `I` representing `M` and any
complex `K` representing the first argument. Then

* `RHom_A(B, M)` is the degreewise coextension `Hom_A(B, I)`, by
  `Dualizing.derivedHomObjIsoCoextend`, and that complex is K-injective over `B`
  (`coextend_isKInjective`), so the internal derived Hom out of `K` into it is the ordinary Hom
  complex `Hom^•_B(K, Hom_A(B, I))`;
* `RHom_A(K_A, M)` is the ordinary Hom complex `Hom^•_A(K_A, I)`, again because `I` is
  K-injective.

Both identifications are `Stacks.DerivedHom.BaseChange.homModelIso`, which needs no K-flatness of
the first argument, so no hypothesis on `K` appears. The two Hom complexes agree by
`Dualizing.restrictHomComplexCoextendIso`, the adjunction applied degreewise.

The module universe is the rings' own universe throughout: the internal derived Hom bifunctor
`StacksDraft.DerivedHom.DerivedInternalHom.Model.hom` is constructed there.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0A71](https://stacks.math.columbia.edu/tag/0A71)
* [Stacks Project, Tag 08YP](https://stacks.math.columbia.edu/tag/08YP)
* [Stacks Project, Tag 0917](https://stacks.math.columbia.edu/tag/0917)
-/

@[expose] public section

open CategoryTheory CochainComplex CochainComplex.HomComplex
open ModuleCat.RestrictionCoextensionAdj

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- Degreewise restriction of scalars along `f : A →+* B`, on cochain complexes. -/
noncomputable abbrev restrictComplex :
    CochainComplex (ModuleCat.{u} B) ℤ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  (ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)

section Underived

variable {X X' : ModuleCat.{u} A} {Y Y' : ModuleCat.{u} B}

/-- The adjunction bijection between restriction and coextension of scalars, in the direction
`Hom_B(Y, Hom_A(B, X)) → Hom_A(Y_A, X)` is restriction of scalars followed by the counit
`g ↦ g 1`. -/
theorem toRestriction_eq_map_comp_counit
    (g : Y ⟶ (ModuleCat.coextendScalars.{u, u, u} f).obj X) :
    HomEquiv.toRestriction f g =
      (ModuleCat.restrictScalars.{u} f).map g ≫
        (ModuleCat.RestrictionCoextensionAdj.counit' f).app X :=
  rfl

/-- The adjunction bijection between restriction and coextension of scalars, as a homomorphism of
additive groups. -/
noncomputable def toRestrictionAddHom (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B) :
    (Y ⟶ (ModuleCat.coextendScalars.{u, u, u} f).obj X) →+
      ((ModuleCat.restrictScalars.{u} f).obj Y ⟶ X) where
  toFun := HomEquiv.toRestriction f
  map_zero' := ModuleCat.hom_ext <| LinearMap.ext fun _ => rfl
  map_add' _ _ := ModuleCat.hom_ext <| LinearMap.ext fun _ => rfl

/-- The adjunction bijection is additive. -/
theorem toRestriction_add (g h : Y ⟶ (ModuleCat.coextendScalars.{u, u, u} f).obj X) :
    HomEquiv.toRestriction f (g + h) =
      HomEquiv.toRestriction f g + HomEquiv.toRestriction f h :=
  (toRestrictionAddHom f X Y).map_add g h

/-- The adjunction bijection commutes with integer scalars. -/
theorem toRestriction_zsmul (k : ℤ) (g : Y ⟶ (ModuleCat.coextendScalars.{u, u, u} f).obj X) :
    HomEquiv.toRestriction f (k • g) = k • HomEquiv.toRestriction f g :=
  map_zsmul (toRestrictionAddHom f X Y) k g

/-- The adjunction bijection is `A`-linear for the `A`-module structure that restriction of
scalars puts on the `B`-module `Hom_B(Y, Hom_A(B, X))`. -/
theorem toRestriction_smul (a : A) (g : Y ⟶ (ModuleCat.coextendScalars.{u, u, u} f).obj X) :
    HomEquiv.toRestriction f (f a • g) = a • HomEquiv.toRestriction f g := by
  refine ModuleCat.hom_ext <| LinearMap.ext fun y => ?_
  change ModuleCat.CoextendScalars.equiv f X (f a • g.hom y) (1 : B) =
    a • ModuleCat.CoextendScalars.equiv f X (g.hom y) (1 : B)
  rw [ModuleCat.CoextendScalars.smul_apply, one_mul, ← mul_one (f a)]
  exact (ModuleCat.CoextendScalars.equiv f X (g.hom y)).map_smul a (1 : B)

/-- The adjunction bijection commutes with precomposition. -/
theorem toRestriction_comp_left (k : Y' ⟶ Y)
    (g : Y ⟶ (ModuleCat.coextendScalars.{u, u, u} f).obj X) :
    HomEquiv.toRestriction f (k ≫ g) =
      (ModuleCat.restrictScalars.{u} f).map k ≫ HomEquiv.toRestriction f g :=
  rfl

/-- The adjunction bijection commutes with postcomposition by a coextended morphism. -/
theorem toRestriction_comp_right (g : Y ⟶ (ModuleCat.coextendScalars.{u, u, u} f).obj X)
    (d : X ⟶ X') :
    HomEquiv.toRestriction f (g ≫ (ModuleCat.coextendScalars.{u, u, u} f).map d) =
      HomEquiv.toRestriction f g ≫ d :=
  rfl

/-- The adjunction bijection commutes with postcomposition by a differential of the degreewise
coextension of a complex of `A`-modules. -/
theorem toRestriction_comp_coextendComplex_d (I : CochainComplex (ModuleCat.{u} A) ℤ) (i j : ℤ)
    (g : Y ⟶ ((coextendComplex.{u, u, u} f).obj I).X i) :
    HomEquiv.toRestriction f (g ≫ ((coextendComplex.{u, u, u} f).obj I).d i j) =
      HomEquiv.toRestriction f g ≫ I.d i j :=
  rfl

/-- The adjunction bijection is a bijection, first half. -/
theorem toRestriction_fromRestriction (g : (ModuleCat.restrictScalars.{u} f).obj Y ⟶ X) :
    HomEquiv.toRestriction f (HomEquiv.fromRestriction f g) = g := by
  refine ModuleCat.hom_ext <| LinearMap.ext fun y => ?_
  change g.hom ((1 : B) • (show (Y : Type u) from y)) = g.hom y
  rw [one_smul]

/-- The adjunction bijection is a bijection, second half. -/
theorem fromRestriction_toRestriction
    (g : Y ⟶ (ModuleCat.coextendScalars.{u, u, u} f).obj X) :
    HomEquiv.fromRestriction f (HomEquiv.toRestriction f g) = g := by
  refine ModuleCat.hom_ext <| LinearMap.ext fun y => ?_
  refine ModuleCat.CoextendScalars.ext <| LinearMap.ext fun s => ?_
  change ModuleCat.CoextendScalars.equiv f X (g.hom ((show B from s) • y)) (1 : B) =
    ModuleCat.CoextendScalars.equiv f X (g.hom y) s
  rw [map_smul, ModuleCat.CoextendScalars.smul_apply, one_mul]

end Underived

section Complexes

variable (K : CochainComplex (ModuleCat.{u} B) ℤ) (I : CochainComplex (ModuleCat.{u} A) ℤ)

/-- The adjunction bijection is additive on morphisms into a term of a degreewise coextension. -/
theorem toRestriction_coextendComplex_add (p i : ℤ)
    (g h : K.X p ⟶ ((coextendComplex.{u, u, u} f).obj I).X i) :
    HomEquiv.toRestriction f (g + h) =
      HomEquiv.toRestriction f g + HomEquiv.toRestriction f h :=
  toRestriction_add f g h

/-- The adjunction bijection commutes with integer scalars on morphisms into a term of a degreewise
coextension. -/
theorem toRestriction_coextendComplex_zsmul (p i : ℤ) (k : ℤ)
    (g : K.X p ⟶ ((coextendComplex.{u, u, u} f).obj I).X i) :
    HomEquiv.toRestriction f (k • g) = k • HomEquiv.toRestriction f g :=
  toRestriction_zsmul f k g

/-- The adjunction bijection carries the zero morphism into a term of a degreewise coextension to
zero. -/
theorem toRestriction_coextendComplex_zero (p i : ℤ) :
    HomEquiv.toRestriction f (0 : K.X p ⟶ ((coextendComplex.{u, u, u} f).obj I).X i) = 0 :=
  (toRestrictionAddHom f (I.X i) (K.X p)).map_zero

/-- The adjunction bijection commutes with precomposition by a differential of a complex of
`B`-modules, which becomes the differential of its restriction of scalars. -/
theorem toRestriction_restrictComplex_d_comp (i j k : ℤ)
    (g : K.X j ⟶ ((coextendComplex.{u, u, u} f).obj I).X k) :
    HomEquiv.toRestriction f (K.d i j ≫ g) =
      ((restrictComplex.{u} f).obj K).d i j ≫ HomEquiv.toRestriction f g :=
  rfl

end Complexes

/-- The adjunction bijection on cochains. For a complex `K` of `B`-modules and a complex `I`
of `A`-modules, a degree-`n` cochain from `K` into the degreewise coextension `Hom_A(B, I)` is
the same thing as a degree-`n` cochain from `K` read over `A` into `I`.  The `A`-module structure
on the left is the one restriction of scalars puts on the `B`-module of cochains. -/
noncomputable def cochainCoextendLinearEquiv
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    ((ModuleCat.restrictScalars.{u} f).obj
        ((HomComplexR B K ((coextendComplex.{u, u, u} f).obj I)).X n) : Type u) ≃ₗ[A]
      Cochain ((restrictComplex.{u} f).obj K) I n where
  toFun z := Cochain.mk fun p q hpq => HomEquiv.toRestriction f (z.v p q hpq)
  invFun w := Cochain.mk fun p q hpq => HomEquiv.fromRestriction f (w.v p q hpq)
  left_inv z := Cochain.ext _ _ fun p q hpq => fromRestriction_toRestriction f (z.v p q hpq)
  right_inv w := Cochain.ext _ _ fun p q hpq => toRestriction_fromRestriction f (w.v p q hpq)
  map_add' z w := Cochain.ext _ _ fun p q hpq =>
    toRestriction_add f (z.v p q hpq) (w.v p q hpq)
  map_smul' a z := Cochain.ext _ _ fun p q hpq => toRestriction_smul f a (z.v p q hpq)

/-- The transported cochain of `Dualizing.cochainCoextendLinearEquiv` commutes with the
Hom-complex differential `δ`. -/
theorem cochainCoextendLinearEquiv_delta
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (I : CochainComplex (ModuleCat.{u} A) ℤ) (n m : ℤ)
    (z : Cochain K ((coextendComplex.{u, u, u} f).obj I) n) :
    δ n m (Cochain.mk fun p q hpq => HomEquiv.toRestriction f (z.v p q hpq)) =
      (Cochain.mk fun p q hpq => HomEquiv.toRestriction f ((δ n m z).v p q hpq) :
        Cochain ((restrictComplex.{u} f).obj K) I m) := by
  by_cases hnm : n + 1 = m
  · refine Cochain.ext _ _ fun p q hpq => ?_
    rw [δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl, Cochain.mk_v, Cochain.mk_v, Cochain.mk_v,
      δ_v n m hnm z p q hpq (q - 1) (p + 1) rfl rfl,
      toRestriction_coextendComplex_add f K I, Units.smul_def, Units.smul_def,
      toRestriction_coextendComplex_zsmul f K I]
    exact congr_arg₂ (· + ·)
      (toRestriction_comp_coextendComplex_d f I (q - 1) q (z.v p (q - 1) (by omega))).symm
      (congrArg (fun t => (m.negOnePow : ℤ) • t)
        (toRestriction_restrictComplex_d_comp f K I p (p + 1) q
          (z.v (p + 1) q (by omega))).symm)
  · rw [δ_shape n m hnm, δ_shape n m hnm]
    refine Cochain.ext _ _ fun p q hpq => ?_
    rw [Cochain.zero_v, Cochain.mk_v, Cochain.zero_v]
    exact (toRestriction_coextendComplex_zero f K I p q).symm

/-- Coextension duality, underived. For a homomorphism of commutative rings `f : A →+* B`, a
complex `K` of `B`-modules and a complex `I` of `A`-modules, the Hom complex
`Hom^•_B(K, Hom_A(B, I))`, read as a complex of `A`-modules by restriction of scalars, is
isomorphic to the Hom complex `Hom^•_A(K_A, I)`. -/
noncomputable def restrictHomComplexCoextendIso
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (I : CochainComplex (ModuleCat.{u} A) ℤ) :
    (restrictComplex.{u} f).obj (HomComplexR B K ((coextendComplex.{u, u, u} f).obj I)) ≅
      HomComplexR A ((restrictComplex.{u} f).obj K) I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (cochainCoextendLinearEquiv.{u} f K I n).toModuleIso)
    (fun i j _ => ModuleCat.hom_ext <| LinearMap.ext fun z =>
      cochainCoextendLinearEquiv_delta.{u} f K I i j z)

/-- Coextension duality at a general first argument, at chosen representatives. For a
homomorphism of commutative rings `f : A →+* B`, an object of `D(B)` represented by a cochain
complex `K`, and an object `M` of `D(A)` represented by a K-injective complex `I`, the internal
derived Hom over `A` out of the restriction of scalars of `K` into `M` is the restriction of
scalars of the internal derived Hom over `B` out of `K` into the derived coextension
`RHom_A(B, M)`:

`RHom_A(K_A, M) ≅ RHom_B(K, RHom_A(B, M))_A` . -/
noncomputable def modelHomCoextendIsoRestrictScalars
    {Xb : DerivedCategory (ModuleCat.{u} B)} {M : DerivedCategory (ModuleCat.{u} A)}
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (I : CochainComplex (ModuleCat.{u} A) ℤ)
    (hI : I.IsKInjective) (eK : Xb ≅ DerivedCategory.Q.obj K)
    (eI : M ≅ DerivedCategory.Q.obj I) :
    (StacksDraft.DerivedHom.DerivedInternalHom.Model.hom A).obj
        (Opposite.op ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj Xb), M) ≅
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj
        ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom B).obj
          (Opposite.op Xb, (derivedHom.{u, u, u} f).obj M)) :=
  letI := hI
  letI : ((coextendComplex.{u, u, u} f).obj I).IsKInjective := coextend_isKInjective f I hI
  Stacks.DerivedHom.BaseChange.homModelIso ((restrictComplex.{u} f).obj K) I
      ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.mapIso eK ≪≫
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.app K) eI ≪≫
    (DerivedCategory.Q.mapIso (restrictHomComplexCoextendIso.{u} f K I)).symm ≪≫
    ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.app
      (HomComplexR B K ((coextendComplex.{u, u, u} f).obj I))).symm ≪≫
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.mapIso
      (Stacks.DerivedHom.BaseChange.homModelIso K ((coextendComplex.{u, u, u} f).obj I) eK
        ((derivedHom.{u, u, u} f).mapIso eI ≪≫
          derivedHomObjIsoCoextend.{u, u} f I hI)).symm

/-- Coextension duality at a general first argument: for `Xb` in `D(B)` and `M` in `D(A)`,
`RHom_A((Xb)_A, M) ≅ RHom_B(Xb, RHom_A(B, M))_A`. -/
theorem nonempty_modelHomCoextendIsoRestrictScalars
    (Xb : DerivedCategory (ModuleCat.{u} B)) (M : DerivedCategory (ModuleCat.{u} A)) :
    Nonempty
      ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom A).obj
          (Opposite.op ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj Xb), M) ≅
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj
          ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom B).obj
            (Opposite.op Xb, (derivedHom.{u, u, u} f).obj M))) := by
  obtain ⟨I, q, hq, hI⟩ :=
    CochainComplex.exists_quasiIso_isKInjective (DerivedCategory.Q.objPreimage M)
  have := hq
  exact ⟨modelHomCoextendIsoRestrictScalars f (DerivedCategory.Q.objPreimage Xb) I hI
    (DerivedCategory.Q.objObjPreimageIso Xb).symm
    ((DerivedCategory.Q.objObjPreimageIso M).symm ≪≫ asIso (DerivedCategory.Q.map q))⟩

/-- The two objects of `D(A)` compared by coextension duality are isomorphic to the same objects
of `D(A)`. -/
theorem nonempty_modelHomCoextend_iso_iff
    (Xb : DerivedCategory (ModuleCat.{u} B)) (M W : DerivedCategory (ModuleCat.{u} A)) :
    Nonempty
        ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom A).obj
          (Opposite.op ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj Xb), M) ≅ W) ↔
      Nonempty
        ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj
          ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom B).obj
            (Opposite.op Xb, (derivedHom.{u, u, u} f).obj M)) ≅ W) :=
  let ⟨e⟩ := nonempty_modelHomCoextendIsoRestrictScalars f Xb M
  ⟨fun ⟨h⟩ => ⟨e.symm ≪≫ h⟩, fun ⟨h⟩ => ⟨e ≪≫ h⟩⟩

/-- The target ring `B`, placed in degree zero and read in `D(A)` by derived restriction of
scalars. -/
noncomputable abbrev targetSingleModel : DerivedCategory (ModuleCat.{u} A) :=
  (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B))

/-- The derived endomorphisms of a derived coextension are a double dual over the base. For
`M` in `D(A)`, the internal derived Hom from `RHom_A(B, M)` to itself, formed in `D(B)` and read
in `D(A)`, is `RHom_A(RHom_A(B[0], M), M)`:

`RHom_B(RHom_A(B, M), RHom_A(B, M))_A ≅ RHom_A(RHom_A(B[0], M), M)` . -/
theorem nonempty_modelHom_derivedHom_self_iso_doubleDual
    (M : DerivedCategory (ModuleCat.{u} A)) :
    Nonempty
      ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj
          ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom B).obj
            (Opposite.op ((derivedHom.{u, u, u} f).obj M), (derivedHom.{u, u, u} f).obj M)) ≅
        (StacksDraft.DerivedHom.DerivedInternalHom.Model.hom A).obj
          (Opposite.op ((StacksDraft.DerivedHom.DerivedInternalHom.Model.hom A).obj
            (Opposite.op (targetSingleModel.{u} f), M)), M)) := by
  obtain ⟨e₁⟩ := nonempty_modelHomCoextendIsoRestrictScalars f ((derivedHom.{u, u, u} f).obj M) M
  obtain ⟨e₂⟩ := nonempty_modelHomIsoRestrictScalarsDerivedHom f M
  exact ⟨e₁.symm ≪≫ (StacksDraft.DerivedHom.DerivedInternalHom.Model.hom A).mapIso
    ((Iso.op e₂).prod (Iso.refl M))⟩

end Dualizing

end
