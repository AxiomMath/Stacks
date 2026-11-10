module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ExtensionOfScalars

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveConstructibility.FiniteCoefficients.ExtendScalarsAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveConstructibility.FiniteCoefficients.TensorCofan
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# The underlying abelian sheaf of `𝒢 ⊗_ℤ Λ̲` for a sheaf `𝒢` killed by a prime

Let `ℓ` be a prime, `Λ` a commutative ring and `𝒢` a sheaf of `ℤ/ℓ`-modules on a site `J`. Its
extension of scalars along `ℤ → Λ` is the sheaf of `Λ`-modules `𝒢 ⊗_ℤ Λ̲`
(`CategoryTheory.extendScalarsSheaf`). Choose `eᵢ ∈ Λ` whose images form a basis of the
`𝔽_ℓ`-vector space `Λ/ℓΛ`. Then the underlying abelian sheaf of `𝒢 ⊗_ℤ Λ̲` is the direct sum of
copies of the underlying abelian sheaf of `𝒢`, the `i`-th summand embedded by the unit
`𝒢 ⟶ 𝒢 ⊗_ℤ Λ̲` followed by multiplication by `eᵢ`. On sections this is
`Stacks.EtaleCohomology.FiniteCoefficients.isColimitTensorCofan`; it survives sheafification
because sheafification is a left adjoint commuting with forgetting the module structure.

## Main results

* `Stacks.EtaleCohomology.FiniteCoefficients.isColimit_cofan_of_iso`: transport of a colimit
  cofan of a constant family along isomorphisms of the summand and of the apex.
* `Stacks.EtaleCohomology.FiniteCoefficients.isColimitExtendScalarsSheafCofan`: the direct sum
  decomposition of the underlying abelian sheaf of `𝒢 ⊗_ℤ Λ̲`.
* `Stacks.EtaleCohomology.FiniteCoefficients.isIso_zmodExtendScalarsDesc`: the map
  `𝒢 ⊗_ℤ Λ̲ ⟶ ℋ` adjoint to `ψ` is an isomorphism when the maps `ψ` followed by multiplication
  by `eᵢ` exhibit the underlying abelian sheaf of `ℋ` as a direct sum of copies of that of `𝒢`.

## References

* [Stacks Project, Tag 0GKW](https://stacks.math.columbia.edu/tag/0GKW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

universe w v c

namespace Stacks.EtaleCohomology.FiniteCoefficients

/-- **Transport of a colimit cofan of a constant family** along isomorphisms `X' ≅ X` of the
summand and `c.pt ≅ Y'` of the apex. -/
def isColimit_cofan_of_iso {D : Type*} [Category D] {ι : Type*} {X X' Y' : D}
    {c : Cofan fun _ : ι ↦ X} (hc : IsColimit c) (eX : X' ≅ X) (eY : c.pt ≅ Y')
    (inj : ι → (X' ⟶ Y')) (h : ∀ i, inj i = eX.hom ≫ c.inj i ≫ eY.hom) :
    IsColimit (Cofan.mk Y' inj) :=
  Cofan.IsColimit.mk _ (fun s ↦ eY.inv ≫ Cofan.IsColimit.desc hc fun i ↦ eX.inv ≫ s.inj i)
    (fun s i ↦ by
      change inj i ≫ _ = _
      simp [h])
    (fun s m hm ↦ by
      rw [Iso.eq_inv_comp]
      refine Cofan.IsColimit.hom_ext hc _ _ fun i ↦ ?_
      rw [Cofan.IsColimit.fac, Iso.eq_inv_comp, ← hm i]
      change _ = inj i ≫ m
      simp [h])

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type w) [CommRing Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  [HasWeakSheafify J (ModuleCat.{w} Λ)] [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.HasSheafCompose (ModuleCat.restrictScalars.{w} (Int.castRingHom Λ))]
  [J.HasSheafCompose (ModuleCat.restrictScalars.{w} (Int.castRingHom (ZMod ℓ)))]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod ℓ)) AddCommGrpCat.{w})]
  [J.PreservesSheafification (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- The sheaf of `ℤ`-modules underlying a sheaf of `ℤ/ℓ`-modules. -/
abbrev zmodToInt (G : Sheaf J (ModuleCat.{w} (ZMod ℓ))) : Sheaf J (ModuleCat.{w} ℤ) :=
  (sheafCompose J (ModuleCat.restrictScalars.{w} (Int.castRingHom (ZMod ℓ)))).obj G

/-- **`𝒢 ⊗_ℤ Λ̲`**, the extension of scalars along `ℤ → Λ` of a sheaf of `ℤ/ℓ`-modules. -/
abbrev zmodExtendScalars (G : Sheaf J (ModuleCat.{w} (ZMod ℓ))) : Sheaf J (ModuleCat.{w} Λ) :=
  (extendScalarsSheaf.{w} J ℤ Λ (Int.castRingHom Λ)).obj (zmodToInt J ℓ G)

/-- The `i`-th summand of the underlying abelian sheaf of `𝒢 ⊗_ℤ Λ̲`: the unit
`𝒢 ⟶ 𝒢 ⊗_ℤ Λ̲` followed by multiplication by `e`. -/
abbrev zmodExtendScalarsInj (G : Sheaf J (ModuleCat.{w} (ZMod ℓ))) (e : Λ) :
    (sheafCompose J (forget₂ (ModuleCat.{w} (ZMod ℓ)) AddCommGrpCat.{w})).obj G ⟶
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj
        (zmodExtendScalars J Λ ℓ G) :=
  (sheafCompose J (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w})).map
      ((extendScalarsSheafAdj.{w} J ℤ Λ (Int.castRingHom Λ)).unit.app (zmodToInt J ℓ G)) ≫
    (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
      (e • 𝟙 (zmodExtendScalars J Λ ℓ G))

/-- The sections of `𝒢 ⊗_ℤ Λ̲` before sheafification: `U ↦ Λ ⊗_ℤ 𝒢(U)`. -/
abbrev zmodExtendScalarsPresheaf (G : Sheaf J (ModuleCat.{w} (ZMod ℓ))) :
    Cᵒᵖ ⥤ ModuleCat.{w} Λ :=
  (zmodToInt J ℓ G).obj ⋙ ModuleCat.extendScalars (Int.castRingHom Λ)

/-- The `i`-th summand of `U ↦ Λ ⊗_ℤ 𝒢(U)`: `m ↦ e ⊗ m`. -/
def zmodExtendScalarsPresheafInj (G : Sheaf J (ModuleCat.{w} (ZMod ℓ))) (e : Λ) :
    G.obj ⋙ forget₂ (ModuleCat.{w} (ZMod ℓ)) AddCommGrpCat.{w} ⟶
      zmodExtendScalarsPresheaf J Λ ℓ G ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w} where
  app U := AddCommGrpCat.ofHom
    { toFun := fun m ↦ (TensorProduct.tmul ℤ
        (show (ModuleCat.restrictScalars (Int.castRingHom Λ)).obj (ModuleCat.of Λ Λ) from e)
        (show (zmodToInt J ℓ G).obj.obj U from m) :
          TensorProduct ℤ ((ModuleCat.restrictScalars (Int.castRingHom Λ)).obj (ModuleCat.of Λ Λ))
            ((zmodToInt J ℓ G).obj.obj U))
      map_zero' := TensorProduct.tmul_zero _ _
      map_add' := fun m m' ↦ TensorProduct.tmul_add (R := ℤ)
        (show (ModuleCat.restrictScalars (Int.castRingHom Λ)).obj (ModuleCat.of Λ Λ) from e)
        (show (zmodToInt J ℓ G).obj.obj U from m) (show (zmodToInt J ℓ G).obj.obj U from m') }
  naturality U V φ := by
    ext m
    rfl

variable {Λ ℓ} in
/-- **The underlying abelian sheaf of `𝒢 ⊗_ℤ Λ̲` is a direct sum of copies of that of `𝒢`**, for a
sheaf `𝒢` of `ℤ/ℓ`-modules and `e : ι → Λ` a family whose image is a basis of `Λ/ℓΛ` with
coordinates `κ`: the `i`-th summand is the unit `𝒢 ⟶ 𝒢 ⊗_ℤ Λ̲` followed by multiplication by
`eᵢ`. -/
def isColimitExtendScalarsSheafCofan (G : Sheaf J (ModuleCat.{w} (ZMod ℓ))) {ι : Type w}
    (e : ι → Λ) (κ : Λ →+ (ι →₀ ZMod ℓ))
    (hspan : ∀ x : Λ, ∃ y : Λ, x = ((κ x).sum fun i k ↦ k.val • e i) + ℓ • y)
    (hκ : ∀ i, κ (e i) = Finsupp.single i 1) :
    IsColimit (Cofan.mk ((sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj
      (zmodExtendScalars J Λ ℓ G)) fun i ↦ zmodExtendScalarsInj J Λ ℓ G (e i)) := by
  let P := zmodExtendScalarsPresheaf J Λ ℓ G
  have h₀ : IsColimit (Cofan.mk (P ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})
      fun i ↦ zmodExtendScalarsPresheafInj J Λ ℓ G (e i)) := by
    refine evaluationJointlyReflectsColimits _ fun U ↦ ?_
    refine (isColimitMapCoconeCofanMkEquiv _ _ _).symm ?_
    exact isColimitTensorCofan (L := (ModuleCat.restrictScalars (Int.castRingHom Λ)).obj
        (ModuleCat.of Λ Λ)) (M := (zmodToInt J ℓ G).obj.obj U) (e := e) (κ := κ)
      (fun m ↦ by
        change ℓ • (show G.obj.obj U from m) = 0
        rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), ZMod.natCast_self, zero_smul]) hspan hκ
  refine isColimit_cofan_of_iso
    (isColimitCofanMkObjOfIsColimit (presheafToSheaf J AddCommGrpCat.{w}) _ _ h₀)
    (sheafificationIso ((sheafCompose J (forget₂ (ModuleCat.{w} (ZMod ℓ))
      AddCommGrpCat.{w})).obj G))
    ((sheafComposeNatIso J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})
      (sheafificationAdjunction J _) (sheafificationAdjunction J _)).app P) _ fun i ↦ ?_
  have hfac := sheafComposeNatTrans_fac J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})
    (sheafificationAdjunction J _) (sheafificationAdjunction J _) P
  simp only [sheafificationAdjunction_unit_app] at hfac
  ext1
  change _ = toSheafify J _ ≫ sheafifyMap J _ ≫
    (sheafToPresheaf J _).map ((sheafComposeNatTrans J _ _ _).app P)
  have key := (toSheafify_naturality_assoc J (zmodExtendScalarsPresheafInj J Λ ℓ G (e i))
    ((sheafToPresheaf J _).map ((sheafComposeNatTrans J (forget₂ (ModuleCat.{w} Λ)
      AddCommGrpCat.{w}) (sheafificationAdjunction J _)
        (sheafificationAdjunction J _)).app P))).symm.trans
    (congrArg (fun t ↦ zmodExtendScalarsPresheafInj J Λ ℓ G (e i) ≫ t) hfac)
  refine Eq.trans ?_ key.symm
  ext U m
  have hu := congrArg (fun φ ↦ (φ.app U).hom m)
    (extendScalarsSheafAdj_unit_app_val.{w} J ℤ Λ (Int.castRingHom Λ) (zmodToInt J ℓ G))
  simp only [Functor.comp_obj, NatTrans.comp_app, Functor.whiskerRight_app,
    Adjunction.whiskerRight_unit_app_app] at hu
  change ((e i • 𝟙 (zmodExtendScalars J Λ ℓ G)).hom.app U).hom
      ((((extendScalarsSheafAdj.{w} J ℤ Λ (Int.castRingHom Λ)).unit.app
        (zmodToInt J ℓ G)).hom.app U).hom m) = ((toSheafify J P).app U).hom _
  rw [hu]
  change e i • ((toSheafify J P).app U).hom ((1 : Λ) ⊗ₜ[ℤ,Int.castRingHom Λ] m) =
    ((toSheafify J P).app U).hom ((e i : Λ) ⊗ₜ[ℤ,Int.castRingHom Λ] m)
  conv_rhs => rw [← mul_one (e i)]
  exact (((toSheafify J P).app U).hom.map_smul (e i)
    ((1 : Λ) ⊗ₜ[ℤ,Int.castRingHom Λ] m)).symm

/-- An additive map of the underlying abelian sheaves of a sheaf of `ℤ/ℓ`-modules `𝒢` and of a
sheaf of `Λ`-modules `ℋ`, read as a map of sheaves of `ℤ`-modules `𝒢 ⟶ ℋ`. -/
def zmodToIntHom (G : Sheaf J (ModuleCat.{w} (ZMod ℓ))) {H : Sheaf J (ModuleCat.{w} Λ)}
    (ψ : (sheafCompose J (forget₂ (ModuleCat.{w} (ZMod ℓ)) AddCommGrpCat.{w})).obj G ⟶
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj H) :
    zmodToInt J ℓ G ⟶
      (sheafCompose J (ModuleCat.restrictScalars.{w} (Int.castRingHom Λ))).obj H :=
  (sheafCompose J (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}) ⋙
    sheafToPresheaf J AddCommGrpCat.{w}).preimage ψ.hom

omit [HasWeakSheafify J (ModuleCat.{w} Λ)] [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.PreservesSheafification (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})] in
/-- On sections, `zmodToIntHom J Λ ℓ G ψ` agrees with `ψ`. -/
theorem zmodToIntHom_app_apply (G : Sheaf J (ModuleCat.{w} (ZMod ℓ)))
    {H : Sheaf J (ModuleCat.{w} Λ)}
    (ψ : (sheafCompose J (forget₂ (ModuleCat.{w} (ZMod ℓ)) AddCommGrpCat.{w})).obj G ⟶
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj H) (U : Cᵒᵖ)
    (m : G.obj.obj U) :
    ((zmodToIntHom J Λ ℓ G ψ).hom.app U).hom m = (ψ.hom.app U).hom m :=
  congrArg (fun φ ↦ (φ.app U).hom m)
    ((sheafCompose J (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}) ⋙
      sheafToPresheaf J AddCommGrpCat.{w}).map_preimage (X := zmodToInt J ℓ G)
        (Y := (sheafCompose J (ModuleCat.restrictScalars.{w} (Int.castRingHom Λ))).obj H) ψ.hom)

/-- The map of sheaves of `Λ`-modules `𝒢 ⊗_ℤ Λ̲ ⟶ ℋ` adjoint to an additive map `ψ` of
underlying abelian sheaves. -/
def zmodExtendScalarsDesc (G : Sheaf J (ModuleCat.{w} (ZMod ℓ))) {H : Sheaf J (ModuleCat.{w} Λ)}
    (ψ : (sheafCompose J (forget₂ (ModuleCat.{w} (ZMod ℓ)) AddCommGrpCat.{w})).obj G ⟶
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj H) :
    zmodExtendScalars J Λ ℓ G ⟶ H :=
  ((extendScalarsSheafAdj.{w} J ℤ Λ (Int.castRingHom Λ)).homEquiv _ _).symm
    (zmodToIntHom J Λ ℓ G ψ)

omit [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.PreservesSheafification (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})] in
/-- The summand `zmodExtendScalarsInj J Λ ℓ G e` followed by `zmodExtendScalarsDesc J Λ ℓ G ψ` is
`ψ` followed by multiplication by `e`. -/
theorem zmodExtendScalarsInj_comp_zmodExtendScalarsDesc (G : Sheaf J (ModuleCat.{w} (ZMod ℓ)))
    {H : Sheaf J (ModuleCat.{w} Λ)}
    (ψ : (sheafCompose J (forget₂ (ModuleCat.{w} (ZMod ℓ)) AddCommGrpCat.{w})).obj G ⟶
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj H) (e : Λ) :
    zmodExtendScalarsInj J Λ ℓ G e ≫
        (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
          (zmodExtendScalarsDesc J Λ ℓ G ψ) =
      ψ ≫ (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map (e • 𝟙 H) := by
  have h₂ := (extendScalarsSheafAdj.{w} J ℤ Λ (Int.castRingHom Λ)).homEquiv_unit
    (zmodToInt J ℓ G) H (zmodExtendScalarsDesc J Λ ℓ G ψ)
  rw [zmodExtendScalarsDesc, Equiv.apply_symm_apply] at h₂
  ext1
  ext U m
  change ((zmodExtendScalarsDesc J Λ ℓ G ψ).hom.app U).hom
      (e • (show (zmodExtendScalars J Λ ℓ G).obj.obj U from
        (((extendScalarsSheafAdj.{w} J ℤ Λ (Int.castRingHom Λ)).unit.app
          (zmodToInt J ℓ G)).hom.app U).hom m)) =
      e • (show H.obj.obj U from (ψ.hom.app U).hom m)
  rw [map_smul]
  exact congrArg (e • ·) ((congrArg (fun φ ↦ (φ.hom.app U).hom m) h₂).symm.trans
    (zmodToIntHom_app_apply J Λ ℓ G ψ U m))

variable {Λ ℓ} in
/-- **`𝒢 ⊗_ℤ Λ̲ ≅ ℋ` from a direct sum decomposition of `ℋ`.** Let `𝒢` be a sheaf of
`ℤ/ℓ`-modules, `ℋ` a sheaf of `Λ`-modules and `ψ : 𝒢 ⟶ ℋ` an additive map of the underlying
abelian sheaves. Suppose the maps `ψ` followed by multiplication by `eᵢ` exhibit the underlying
abelian sheaf of `ℋ` as a direct sum of copies of that of `𝒢`, for a family `e` whose image is a
basis of `Λ/ℓΛ`. Then the `Λ`-linear map `𝒢 ⊗_ℤ Λ̲ ⟶ ℋ` adjoint to `ψ` is an isomorphism. -/
theorem isIso_zmodExtendScalarsDesc (G : Sheaf J (ModuleCat.{w} (ZMod ℓ)))
    {H : Sheaf J (ModuleCat.{w} Λ)}
    (ψ : (sheafCompose J (forget₂ (ModuleCat.{w} (ZMod ℓ)) AddCommGrpCat.{w})).obj G ⟶
      (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj H)
    {ι : Type w} (e : ι → Λ) (κ : Λ →+ (ι →₀ ZMod ℓ))
    (hspan : ∀ x : Λ, ∃ y : Λ, x = ((κ x).sum fun i k ↦ k.val • e i) + ℓ • y)
    (hκ : ∀ i, κ (e i) = Finsupp.single i 1)
    (hH : IsColimit (Cofan.mk ((sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj H)
      fun i ↦ ψ ≫ (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
        (e i • 𝟙 H))) :
    IsIso (zmodExtendScalarsDesc J Λ ℓ G ψ) := by
  have h₁ := isColimitExtendScalarsSheafCofan J G e κ hspan hκ
  have : (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
      (zmodExtendScalarsDesc J Λ ℓ G ψ) = (h₁.coconePointUniqueUpToIso hH).hom :=
    Cofan.IsColimit.hom_ext h₁ _ _ fun i ↦
      (zmodExtendScalarsInj_comp_zmodExtendScalarsDesc J Λ ℓ G ψ (e i)).trans
        (IsColimit.comp_coconePointUniqueUpToIso_hom h₁ hH ⟨i⟩).symm
  have : IsIso ((sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map
      (zmodExtendScalarsDesc J Λ ℓ G ψ)) := by
    rw [this]
    infer_instance
  exact isIso_of_reflects_iso _ (sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}))

end Stacks.EtaleCohomology.FiniteCoefficients

end
