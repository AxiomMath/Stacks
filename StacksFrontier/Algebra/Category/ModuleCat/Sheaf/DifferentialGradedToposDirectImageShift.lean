module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedShiftBy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDirectImage

/-!
# The direct image of a shifted differential graded module

Let `f : X ⟶ Y` be a morphism of ringed topoi, presented as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedToposDirectImage.lean` by an
additive lax monoidal functor `G` of sheaves of modules together with a unital homomorphism
`ψ : A ⟶ f_*B`, and write `f_{*,ψ}` for the direct image of right differential graded modules.
**The direct image commutes with the shift `Q ↦ Q[k]`**: `f_{*,ψ}(Q[k]) ≅ (f_{*,ψ}Q)[k]`,
naturally in `Q`, by the identity in every degree.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.toposPushforwardShiftByIso`: the isomorphism.

## Main results

* `SheafOfModules.DifferentialGradedModule.smulSheaf_shiftBy`: the morphism-level action of a
  shift is that of the module in the shifted degree, followed by a transport of degrees.
* `SheafOfModules.DifferentialGradedModule.toposPushforwardShiftByIso_hom_naturality`: the
  isomorphism is natural.

## Implementation notes

Both modules have, in degree `n`, the sheaf `G(Q^{n + k})`, so the isomorphism is the identity
in every degree. It commutes with the differentials because `G` is additive, and with the actions
because the action of a transport is the transported morphism-level action
(`SheafOfModules.DifferentialGradedModule.smulSheaf_transport`) and the morphism-level action of a
shift is a transport of degrees (`smulSheaf_shiftBy`), which a functor carries to a transport of
degrees.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CategoryTheory.Sheaf PresheafOfModules

universe w v₁ u₁ v₂ u₂

namespace SheafOfModules.DifferentialGradedModule

section DirectImageShift

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-- **The morphism-level action of a shift** is the action of the module in the shifted degree,
followed by the transport of degrees `n + k + i = n + i + k`. -/
theorem smulSheaf_shiftBy {E : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
    (M : DifferentialGradedModule.{w, w, w} E) (k n i : ℤ) :
    smulSheaf (shiftBy M k) n i =
      smulSheaf M (n + k) i ≫
        eqToHom (congrArg M.complex.X (show n + k + i = n + i + k by omega)) := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp)
    (F := M.complex.X (n + k)) (G := E.complex.X i) (Q := M.complex.X (n + i + k))
    fun U x y ↦ ?_
  refine (smulSheaf_unit (shiftBy M k) n i U x y).trans ?_
  refine Eq.trans ?_ (congrArg
    ((eqToHom (congrArg M.complex.X (show n + k + i = n + i + k by omega))).val.app U)
    (smulSheaf_unit M (n + k) i U x y).symm)
  exact castBilinearMap_app_apply _ _ U x y

variable (G : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [G.LaxMonoidal] [G.Additive]
  {B : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp)}
  (ψ : A ⟶ toposPushforwardAlgebra G B) (hψ : ψ.IsUnital)

/-- The action of the transport of a shift, on local sections, is the action of the transport
in the shifted degree followed by a transport of degrees. -/
theorem transport_shiftBy_mul_app (Q : DifferentialGradedModule.{w, w, w} B) (k n i : ℤ)
    (U : Dᵒᵖ) (x : (G.obj (Q.complex.X (n + k))).val.obj U)
    (z : ((toposPushforwardAlgebra G B).complex.X i).val.obj U) :
    ((transport G (shiftBy Q k)
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Osharp)
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Psharp)).mul
        n i).app U x z =
      (eqToHom (congrArg (fun q ↦ G.obj (Q.complex.X q))
          (show n + k + i = n + i + k by omega))).val.app U
        (((transport G Q
          (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Osharp)
          (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Psharp)).mul
          (n + k) i).app U x z) := by
  have hs : smulSheaf (transport G (shiftBy Q k)
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Osharp)
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Psharp)) n i =
      smulSheaf (transport G Q
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Osharp)
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Psharp)) (n + k) i ≫
        eqToHom (congrArg (fun q ↦ G.obj (Q.complex.X q))
          (show n + k + i = n + i + k by omega)) := by
    rw [smulSheaf_transport, smulSheaf_transport]
    change Stacks.MonoidalGraded.mapMul G (smulSheaf (shiftBy Q k) n i) = _
    rw [smulSheaf_shiftBy Q k n i]
    exact (transportedSmul_comp_eqToHom G Q (n + k) i (show n + k + i = n + i + k by omega)).symm
  have h := congrArg (fun φ ↦ φ.val.app U
    ((tensorSheafUnit (G.obj (Q.complex.X (n + k)))
      ((toposPushforwardAlgebra G B).complex.X i)).app U (x ⊗ₜ z))) hs
  dsimp only at h
  refine (smulSheaf_unit (transport G (shiftBy Q k)
      (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Osharp)
      (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Psharp))
    n i U x z).symm.trans (h.trans ?_)
  exact congrArg (fun w ↦ (eqToHom (congrArg (fun q ↦ G.obj (Q.complex.X q))
    (show n + k + i = n + i + k by omega))).val.app U w) (smulSheaf_unit (transport G Q
      (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Osharp)
      (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf Psharp))
    (n + k) i U x z)

/-- The identity in every degree from the direct image of a shift to the shift of the direct
image commutes with the differentials. -/
noncomputable def shiftByComplexHom (Q : DifferentialGradedModule.{w, w, w} B) (k : ℤ) :
    ((toposPushforward G ψ hψ).obj (shiftBy Q k)).complex ⟶
      (shiftBy ((toposPushforward G ψ hψ).obj Q) k).complex where
  f n := 𝟙 (G.obj (Q.complex.X (n + k)))
  comm' n m _ := by
    change 𝟙 _ ≫ (k.negOnePow • G.map (Q.complex.d (n + k) (m + k))) =
      G.map (k.negOnePow • Q.complex.d (n + k) (m + k)) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, Units.smul_def, Units.smul_def, Functor.map_zsmul]

/-- The identity in every degree from the shift of the direct image to the direct image of the
shift commutes with the differentials. -/
noncomputable def shiftByComplexInv (Q : DifferentialGradedModule.{w, w, w} B) (k : ℤ) :
    (shiftBy ((toposPushforward G ψ hψ).obj Q) k).complex ⟶
      ((toposPushforward G ψ hψ).obj (shiftBy Q k)).complex where
  f n := 𝟙 (G.obj (Q.complex.X (n + k)))
  comm' n m _ := by
    change 𝟙 _ ≫ G.map (k.negOnePow • Q.complex.d (n + k) (m + k)) =
      (k.negOnePow • G.map (Q.complex.d (n + k) (m + k))) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, Units.smul_def, Units.smul_def, Functor.map_zsmul]

/-- The two actions agree on local sections. -/
theorem shiftBy_toposPushforward_mul_app (Q : DifferentialGradedModule.{w, w, w} B)
    (k n i : ℤ) (U : Dᵒᵖ) (x : (G.obj (Q.complex.X (n + k))).val.obj U)
    (y : (A.complex.X i).val.obj U) :
    (((toposPushforward G ψ hψ).obj (shiftBy Q k)).mul n i).app U x y =
      ((shiftBy ((toposPushforward G ψ hψ).obj Q) k).mul n i).app U x y := by
  refine (transport_shiftBy_mul_app G Q k n i U x _).trans ?_
  rw [shiftBy_mul]
  exact (castBilinearMap_app_apply
    (congrArg ((toposPushforward G ψ hψ).obj Q).complex.X (show n + k + i = n + i + k by omega))
    (((toposPushforward G ψ hψ).obj Q).mul (n + k) i) U x y).symm

/-- **The direct image commutes with the shift**: `f_{*,ψ}(Q[k]) ≅ (f_{*,ψ}Q)[k]`, by the
identity in every degree. -/
noncomputable def toposPushforwardShiftByIso (Q : DifferentialGradedModule.{w, w, w} B) (k : ℤ) :
    (toposPushforward G ψ hψ).obj (shiftBy Q k) ≅ shiftBy ((toposPushforward G ψ hψ).obj Q) k where
  hom :=
    { toHomologicalComplex := shiftByComplexHom G ψ hψ Q k
      map_mul n i U x y := shiftBy_toposPushforward_mul_app G ψ hψ Q k n i U x y }
  inv :=
    { toHomologicalComplex := shiftByComplexInv G ψ hψ Q k
      map_mul n i U x y := (shiftBy_toposPushforward_mul_app G ψ hψ Q k n i U x y).symm }
  hom_inv_id := Hom.ext fun _ ↦ Category.id_comp _
  inv_hom_id := Hom.ext fun _ ↦ Category.id_comp _

/-- The components of `toposPushforwardShiftByIso` are identities. -/
theorem toposPushforwardShiftByIso_hom_f (Q : DifferentialGradedModule.{w, w, w} B) (k n : ℤ) :
    (toposPushforwardShiftByIso G ψ hψ Q k).hom.toHomologicalComplex.f n = 𝟙 _ := rfl

/-- **The isomorphism `f_{*,ψ}(Q[k]) ≅ (f_{*,ψ}Q)[k]` is natural in `Q`.** -/
theorem toposPushforwardShiftByIso_hom_naturality {Q Q' : DifferentialGradedModule.{w, w, w} B}
    (g : Q ⟶ Q') (k : ℤ) :
    (toposPushforward G ψ hψ).map (shiftByMap k g) ≫ (toposPushforwardShiftByIso G ψ hψ Q' k).hom =
      (toposPushforwardShiftByIso G ψ hψ Q k).hom ≫
        shiftByMap k ((toposPushforward G ψ hψ).map g) :=
  Hom.ext fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm

end DirectImageShift

end SheafOfModules.DifferentialGradedModule

end
