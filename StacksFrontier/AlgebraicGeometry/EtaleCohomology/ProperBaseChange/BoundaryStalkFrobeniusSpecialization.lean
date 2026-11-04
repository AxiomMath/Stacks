module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundaryStalkFrobeniusBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkSectionsTransitivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem

/-!
# The specialization map of `j_* F` at a boundary point on germs

Let `j : U ⟶ S`, `s` a geometric point of `S`, `π : Spec 𝒪^{sh}_{S,s} ⟶ S` the strict
henselization, `U ×_S Spec 𝒪^{sh} ≅ Spec K` and `g : Spec K ⟶ U` the projection. This file computes
the identification of Tag 03Q9 of `(j_* F)_s` with the sections of `g⁻¹ F` over `Spec K`
(`Stacks.EtaleCohomology.directImageStalkIsoFieldSections`) as an explicit composite, the input
of the germ formula for the specialization map `(j_* F)_s ⟶ F_{g(t̄)}` used for the Frobenius
equivariance of `H⁰_loc` (Weil II 1.8).

## Main results

* `Stacks.EtaleCohomology.directImageStalkIsoBaseChangeSections_hom_app` and
  `Stacks.EtaleCohomology.directImageStalkIsoFieldSections_hom_app` — the components of the
  identifications of Tag 03Q9, as explicit composites.
* `Stacks.EtaleCohomology.toPresheafFiber_directImageStalkToStalk` — the germ formula: the germ
  of `τ` at a lift `x` of `s` goes to the germ of `τ` at the lift of `g(t̄)` to `U ×_S V` built
  from a section of `V ×_S Spec 𝒪^{sh}` through `x`.
* `Stacks.EtaleCohomology.pointSmallEtaleHom_sheafFiber_comp_directImageStalkToStalk` — the
  Frobenius equivariance of the specialization map: the map of stalks induced by an endomorphism
  `a` of `s` corresponds to the map of Tag 04FN along a lift `ã` to `t̄` of the induced
  endomorphism `id ×_S β_a` of `U ×_S Spec 𝒪^{sh} ≅ Spec K`.
* `Stacks.EtaleCohomology.directImageStalkToStalkHom_pointSmallEtaleHom_geometricPointStalkMap` —
  the same for sheaves of modules, on the additive specialization map.
* `Stacks.EtaleCohomology.representationLevelDirectImageStalkHom_pointSmallEtaleHom` — Frobenius
  on `H⁰_loc` of the levels of `ℱ_ρ`: on the inertia invariants in `(ℤ/ℓ^kℤ)^r` it is
  `ρ mod ℓ^k` of a lift of Frobenius;
  `Stacks.EtaleCohomology.exists_representationLevelDirectImageStalkHom_pointSmallEtaleHom` — the
  same with the lift produced (`AlgebraicGeometry.GeometricPoint.exists_iso_comp_hom_eq_hom_comp`:
  automorphisms fixing the image of an algebraic geometric point lift to it).

## Implementation notes

The kernel cannot check the component formula of `directImageStalkIsoBaseChangeSections` in one
step (it unfolds the sheaf functors); it checks the definitional unfolding and a generic
component formula separately, which are combined with `congrArg`.

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (Weil II 1.8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace CategoryTheory.GrothendieckTopology.Point

universe w

/-- **The identification of the fibre of `P ⋙ F` with `F` of the fibre of `P` is natural in the
point.** -/
theorem Hom.presheafFiberCompIso_inv_naturality {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {A B : Type*} [Category* A] [Category* B]
    [HasColimitsOfSize.{w, w} A] [HasColimitsOfSize.{w, w} B] (F : A ⥤ B) [LocallySmall.{w} C]
    [PreservesFilteredColimitsOfSize.{w, w} F] {Φ₁ Φ₂ : Point.{w} J} (f : Φ₁ ⟶ Φ₂)
    (P : Cᵒᵖ ⥤ A) :
    (Φ₂.presheafFiberCompIso F).inv.app P ≫ f.presheafFiber.app (P ⋙ F) =
      F.map (f.presheafFiber.app P) ≫ (Φ₁.presheafFiberCompIso F).inv.app P := by
  have key : (Φ₂.presheafFiberCompIso F).hom.app P ≫ F.map (f.presheafFiber.app P) =
      f.presheafFiber.app (P ⋙ F) ≫ (Φ₁.presheafFiberCompIso F).hom.app P := by
    refine Φ₂.presheafFiber_hom_ext (fun X x => ?_)
    have a1 := toPresheafFiber_presheafFiberCompIso_hom_app Φ₂ F X x P
    have a2 := Hom.toPresheafFiber_presheafFiber_app f P X x
    have a3 := Hom.toPresheafFiber_presheafFiber_app f (P ⋙ F) X x
    have a4 := toPresheafFiber_presheafFiberCompIso_hom_app Φ₁ F X
      (ConcreteCategory.hom (f.hom.app X) x) P
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) a1).trans ?_)
    refine (F.map_comp _ _).symm.trans ((congrArg F.map a2).trans ?_)
    refine a4.symm.trans ?_
    exact (congrArg (· ≫ _) a3.symm).trans (Category.assoc _ _ _)
  exact (CommSq.horiz_inv (f := (Φ₂.presheafFiberCompIso F).app P)
    (i := (Φ₁.presheafFiberCompIso F).app P) ⟨key⟩).w

end CategoryTheory.GrothendieckTopology.Point

namespace AlgebraicGeometry

attribute [local instance] GeometricPoint.residueFieldAlgebra in
/-- **Lifting an automorphism to an algebraic geometric point.** If `t̄` is an algebraic geometric
point of `Z` (its field `Ω` is an algebraic closure of the residue field `κ(x)` at its image `x`)
and `b` is an automorphism of `Z` fixing `x`, there is an automorphism `α` of `Spec Ω` with
`α ≫ t̄ = t̄ ≫ b`: the automorphism of `κ(x)` induced by `b` extends to `Ω`. -/
theorem GeometricPoint.exists_iso_comp_hom_eq_hom_comp {Z : Scheme.{u}} (t : GeometricPoint Z)
    (ht : t.IsAlgebraic) (b : Z ⟶ Z) [IsIso b] (hb : b (t.hom default) = t.hom default) :
    ∃ α : t.source ≅ t.source, α.hom ≫ t.hom = t.hom ≫ b := by
  let := residueFieldAlgebra t
  have : IsAlgClosure (Z.residueField (t.hom default)) t.residueField := ht
  let θ' : Z.residueField (t.hom default) ⟶ Z.residueField (t.hom default) :=
    (Z.residueFieldCongr hb.symm).hom ≫ b.residueFieldMap (t.hom default)
  let θ : Z.residueField (t.hom default) ≃+* Z.residueField (t.hom default) :=
    (asIso θ').commRingCatIsoToRingEquiv
  let ψ : t.residueField ≃+* t.residueField := IsAlgClosure.equivOfEquiv t.residueField
    t.residueField θ
  refine ⟨Scheme.Spec.mapIso ψ.toCommRingCatIso.op, ?_⟩
  have hring : CommRingCat.ofHom (residueFieldHom t) ≫ ψ.toCommRingCatIso.hom =
      θ' ≫ CommRingCat.ofHom (residueFieldHom t) := by
    ext c
    exact IsAlgClosure.equivOfEquiv_algebraMap t.residueField t.residueField θ c
  have h := specMap_residueFieldHom_comp_fromSpecResidueField t
  change Spec.map ψ.toCommRingCatIso.hom ≫ t.hom = t.hom ≫ b
  calc Spec.map ψ.toCommRingCatIso.hom ≫ t.hom
      = Spec.map ψ.toCommRingCatIso.hom ≫ Spec.map (CommRingCat.ofHom (residueFieldHom t)) ≫
          Z.fromSpecResidueField (t.hom default) := by rw [h]
    _ = Spec.map (CommRingCat.ofHom (residueFieldHom t) ≫ ψ.toCommRingCatIso.hom) ≫
          Z.fromSpecResidueField (t.hom default) := by rw [Spec.map_comp, Category.assoc]
    _ = Spec.map (θ' ≫ CommRingCat.ofHom (residueFieldHom t)) ≫
          Z.fromSpecResidueField (t.hom default) := by rw [hring]
    _ = Spec.map (CommRingCat.ofHom (residueFieldHom t)) ≫
          Spec.map (b.residueFieldMap (t.hom default)) ≫
          Spec.map (Z.residueFieldCongr hb.symm).hom ≫ Z.fromSpecResidueField (t.hom default) := by
        refine congrArg (· ≫ Z.fromSpecResidueField (t.hom default)) ((Spec.map_comp _ _).trans
          (congrArg (Spec.map (CommRingCat.ofHom (residueFieldHom t)) ≫ ·)
            (Spec.map_comp _ _))) |>.trans ?_
        simp only [Category.assoc]
    _ = t.hom ≫ b := by
        rw [Scheme.residueFieldCongr_fromSpecResidueField,
          Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, h]

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

/-- Components of a composite of the shape of `directImageStalkIsoBaseChangeSections`. -/
theorem isoChain₀_hom_app {𝒜 ℬ 𝒟 ℰ 𝒯 : Type*} [Category* 𝒜] [Category* ℬ] [Category* 𝒟]
    [Category* ℰ] [Category* 𝒯]
    (P : 𝒜 ⥤ ℬ) (St : ℬ ⥤ 𝒟) (πinv : ℬ ⥤ ℰ) (ΓSH : ℰ ⥤ 𝒟) (α : St ≅ πinv ⋙ ΓSH)
    (fstinv : 𝒜 ⥤ 𝒯) (snd : 𝒯 ⥤ ℰ) (β : P ⋙ πinv ⟶ fstinv ⋙ snd)
    (hβ : IsIso (Functor.whiskerRight β ΓSH)) (ΓT : 𝒯 ⥤ 𝒟) (γ : snd ⋙ ΓSH ≅ ΓT) (F : 𝒜) :
    (Functor.isoWhiskerLeft P α ≪≫ (Functor.associator P πinv ΓSH).symm ≪≫
        @asIso _ _ _ _ (Functor.whiskerRight β ΓSH) hβ ≪≫
        Functor.associator fstinv snd ΓSH ≪≫ Functor.isoWhiskerLeft fstinv γ).hom.app F =
    α.hom.app (P.obj F) ≫ ΓSH.map (β.app F) ≫ γ.hom.app (fstinv.obj F) := by
  simp

/-- Components of a composite of the shape of `directImageStalkIsoFieldSections`. -/
theorem isoChain₁_hom_app {𝒜 𝒟 𝒯 𝒦 : Type*} [Category* 𝒜] [Category* 𝒟]
    [Category* 𝒯] [Category* 𝒦] (L : 𝒜 ⥤ 𝒟)
    (fstinv : 𝒜 ⥤ 𝒯) (ΓT : 𝒯 ⥤ 𝒟) (D0 : L ≅ fstinv ⋙ ΓT)
    (epush : 𝒯 ⥤ 𝒦) (ΓK : 𝒦 ⥤ 𝒟) (γe : epush ⋙ ΓK ≅ ΓT) (ginv : 𝒜 ⥤ 𝒦)
    (FI : fstinv ⋙ epush ≅ ginv) (F : 𝒜) :
    (D0 ≪≫ Functor.isoWhiskerLeft fstinv γe.symm ≪≫ (Functor.associator fstinv epush ΓK).symm ≪≫
      Functor.isoWhiskerRight FI ΓK).hom.app F =
    D0.hom.app F ≫ γe.inv.app (fstinv.obj F) ≫ ΓK.map (FI.hom.app F) := by
  simp

/-- An endomorphism commuting with the three factors of a natural map of underlying sets,
factored through natural isomorphisms, commutes with the induced morphism of abelian groups. -/
theorem natTransAddHom_comm {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
    (F G : C ⥤ AddCommGrpCat.{v}) [F.Additive] [G.Additive]
    (a : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat)
    {P Q : C ⥤ Type v} (α : F ⋙ forget AddCommGrpCat ≅ P) (β : G ⋙ forget AddCommGrpCat ≅ Q)
    (ψ : P ⟶ Q) (ha : a = α.hom ≫ ψ ≫ β.inv) (X : C) (fF : F.obj X ⟶ F.obj X)
    (fG : G.obj X ⟶ G.obj X) (fP : P.obj X ⟶ P.obj X) (fQ : Q.obj X ⟶ Q.obj X)
    (h1 : α.hom.app X ≫ fP = (forget AddCommGrpCat).map fF ≫ α.hom.app X)
    (h2 : fP ≫ ψ.app X = ψ.app X ≫ fQ)
    (h3 : β.inv.app X ≫ (forget AddCommGrpCat).map fG = fQ ≫ β.inv.app X)
    (z : F.obj X) :
    ConcreteCategory.hom (natTransAddHom F G a X) (ConcreteCategory.hom fF z) =
      ConcreteCategory.hom fG (ConcreteCategory.hom (natTransAddHom F G a X) z) := by
  subst ha
  exact ConcreteCategory.congr_hom
    (show (forget AddCommGrpCat).map fF ≫ α.hom.app X ≫ ψ.app X ≫ β.inv.app X =
      α.hom.app X ≫ ψ.app X ≫ β.inv.app X ≫ (forget AddCommGrpCat).map fG by
      rw [h3, ← reassoc_of% h2, ← reassoc_of% h1]) z

/-- `natTransAddHom_comm` for a middle factor whiskered by a functor `E` and source and target
functors spelled as composites `A ⋙ Φ` and `I ⋙ Ψ`, so that the hypotheses are read on
`Φ.obj (A.obj (E.obj X))` and `Ψ.obj (I.obj (E.obj X))` with no unfolding of composites. -/
theorem natTransAddHom_comm_whiskerLeft {C D₁ D₂ D₃ : Type*} [Category* C] [Preadditive C]
    [HasBinaryBiproducts C] [Category* D₁] [Category* D₂] [Category* D₃]
    (F G : C ⥤ AddCommGrpCat.{v}) [F.Additive] [G.Additive]
    (a : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat) (E : C ⥤ D₁) (A : D₁ ⥤ D₂)
    (Φ : D₂ ⥤ Type v) (I : D₁ ⥤ D₃) (Ψ : D₃ ⥤ Type v)
    (α : F ⋙ forget AddCommGrpCat ≅ E ⋙ (A ⋙ Φ)) (β : G ⋙ forget AddCommGrpCat ≅ E ⋙ (I ⋙ Ψ))
    (ψ : A ⋙ Φ ⟶ I ⋙ Ψ) (ha : a = α.hom ≫ Functor.whiskerLeft E ψ ≫ β.inv) (X : C)
    (fF : F.obj X ⟶ F.obj X) (fG : G.obj X ⟶ G.obj X)
    (fP : Φ.obj (A.obj (E.obj X)) ⟶ Φ.obj (A.obj (E.obj X)))
    (fQ : Ψ.obj (I.obj (E.obj X)) ⟶ Ψ.obj (I.obj (E.obj X)))
    (h1 : α.hom.app X ≫ fP = (forget AddCommGrpCat).map fF ≫ α.hom.app X)
    (h2 : fP ≫ ψ.app (E.obj X) = ψ.app (E.obj X) ≫ fQ)
    (h3 : β.inv.app X ≫ (forget AddCommGrpCat).map fG = fQ ≫ β.inv.app X)
    (z : F.obj X) :
    ConcreteCategory.hom (natTransAddHom F G a X) (ConcreteCategory.hom fF z) =
      ConcreteCategory.hom fG (ConcreteCategory.hom (natTransAddHom F G a X) z) :=
  natTransAddHom_comm F G a α β (Functor.whiskerLeft E ψ) ha X fF fG fP fQ h1 h2 h3 z

section Lift

variable {S U SH : Scheme.{u}} (j : U ⟶ S) (π : SH ⟶ S) {K : Type u} [Field K]
  (e : pullback j π ≅ Spec (.of K)) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (t : Spec (.of Ω) ⟶ Spec (.of K))

/-- The left component of the inverse of the lift-matching iso of a base change. -/
theorem pointSmallEtaleBaseChangeFiberIso_inv_app_left {Z X : Scheme.{u}} (i : Z ⟶ X)
    (s : Spec (.of Ω) ⟶ Z) (W : X.Etale)
    (w : (pointSmallEtale s).fiber.obj ((smallEtaleBaseChange i).obj W)) :
    ((pointSmallEtaleBaseChangeFiberIso i s).inv.app W w).left = w.left ≫ pullback.fst W.hom i := by
  simp [pointSmallEtaleBaseChangeFiberIso, Over.mapPullbackAdj]
  rfl

/-- For `h : k = k'`, the transport between the base changes of `A` along `k` and along `k'`,
followed by the first projection of the base change along `k'`, is the first projection of the
base change along `k`. -/
theorem smallEtaleBaseChange_eqToHom_left_fst {X Y : Scheme.{u}} {k k' : X ⟶ Y} (h : k = k')
    (A : Y.Etale) :
    (eqToHom (congrArg (fun k => (smallEtaleBaseChange k).obj A) h)).left ≫ pullback.fst A.hom k' =
      pullback.fst A.hom k := by
  subst h
  exact Category.id_comp _

private theorem chain_lift {𝒞 : Type*} [Category* 𝒞] {a b c d e f g h k l x y : 𝒞}
    (Lk : a ⟶ b) (a4 : b ⟶ c) (a3 : c ⟶ d) (a2 : d ⟶ e) (a1 : e ⟶ f) (p1 : f ⟶ g) (p0 : g ⟶ h)
    (fj : e ⟶ h) (fπ : d ⟶ h) (q1 : c ⟶ k) (q0 : k ⟶ h) (r : b ⟶ l) (σl : l ⟶ k)
    (t' : a ⟶ x) (ei : x ⟶ y) (sn : y ⟶ l)
    (f1 : a1 ≫ p1 ≫ p0 = fj) (f2 : a2 ≫ fj = fπ) (f3 : a3 ≫ fπ = q1 ≫ q0)
    (f4 : a4 ≫ q1 = r ≫ σl) (f5 : Lk ≫ r = t' ≫ ei ≫ sn) :
    (((((Lk ≫ a4) ≫ a3) ≫ a2) ≫ a1) ≫ p1) ≫ p0 = t' ≫ ei ≫ sn ≫ σl ≫ q0 := by
  simp only [Category.assoc]
  rw [f1, f2, f3, reassoc_of% f4, reassoc_of% f5]

private theorem chain_pt {𝒞 : Type*} [Category* 𝒞] {a b c d e f : 𝒞}
    (x : a ⟶ b) (y : b ⟶ c) (z : c ⟶ d) (f0 : d ⟶ f) (Wh : d ⟶ e) (sn : e ⟶ f) (q : c ⟶ b)
    (ei : b ⟶ e) (h1 : f0 = Wh ≫ sn) (h2 : z ≫ Wh = q ≫ ei) (h3 : y ≫ q = 𝟙 _) :
    (x ≫ y ≫ z) ≫ f0 = x ≫ ei ≫ sn := by
  subst h1
  simp only [Category.assoc]
  rw [reassoc_of% h2, reassoc_of% h3]

/-- The lift of `t ≫ e⁻¹` to the final object of `U ×_S SH` given by a section `ρ`, followed by
the projection to `SH`, is `t ≫ e⁻¹ ≫ snd`. -/
theorem pointLiftOfSection_left_fst (ρ : Scheme.Etale.mk (𝟙 (Spec (.of K))) ⟶
      (smallEtaleBaseChange e.inv).obj
        ((smallEtaleBaseChange (pullback.snd j π)).obj (Scheme.Etale.mk (𝟙 SH)))) :
    (pointLiftOfSection e.inv t _ ρ).left ≫
        pullback.fst (Scheme.Etale.mk (𝟙 SH)).hom (pullback.snd j π) =
      t ≫ e.inv ≫ pullback.snd j π := by
  let W := (smallEtaleBaseChange (pullback.snd j π)).obj (Scheme.Etale.mk (𝟙 SH))
  have hw : ρ.left ≫ pullback.snd W.hom e.inv = 𝟙 _ := CategoryTheory.Over.w ρ.hom
  have h1 : pullback.fst (Scheme.Etale.mk (𝟙 SH)).hom (pullback.snd j π) =
      W.hom ≫ pullback.snd j π :=
    (Category.comp_id _).symm.trans pullback.condition
  exact chain_pt t ρ.left (pullback.fst W.hom e.inv) _ W.hom (pullback.snd j π)
    (pullback.snd W.hom e.inv) e.inv h1 pullback.condition hw

/-- **The lift of `t̄` through the specialization map**, first projection: the lift of `t ≫ e⁻¹`
to `U ×_S V` obtained from a section `σ` of `V ×_S SH`, through Tag 03Q1 and the base change
isomorphisms, followed by the projection to `V`, is `t ≫ e⁻¹ ≫ snd ≫ σ ≫ pr_V`. -/
theorem baseChangeLift_left_fst (V : S.Etale)
    (σ : Scheme.Etale.mk (𝟙 SH) ⟶ (smallEtaleBaseChange π).obj V)
    (ρ : Scheme.Etale.mk (𝟙 (Spec (.of K))) ⟶ (smallEtaleBaseChange e.inv).obj
      ((smallEtaleBaseChange (pullback.snd j π)).obj (Scheme.Etale.mk (𝟙 SH)))) :
    ((pointSmallEtaleBaseChangeFiberIso (pullback.fst j π) (t ≫ e.inv)).inv.app
        ((smallEtaleBaseChange j).obj V)
      ((pointSmallEtale (t ≫ e.inv)).fiber.map
        ((smallEtaleBaseChangeComp (pullback.fst j π) j).hom.app V)
        ((pointSmallEtale (t ≫ e.inv)).fiber.map
          (eqToHom (congrArg (fun k : pullback j π ⟶ S ↦ (smallEtaleBaseChange k).obj V)
            pullback.condition.symm))
          ((pointSmallEtale (t ≫ e.inv)).fiber.map
            ((smallEtaleBaseChangeComp (pullback.snd j π) π).inv.app V)
            ((pointSmallEtale (t ≫ e.inv)).fiber.map
              ((smallEtaleBaseChange (pullback.snd j π)).map σ)
              (pointLiftOfSection e.inv t _ ρ)))))).left ≫ pullback.fst V.hom j =
      t ≫ e.inv ≫ pullback.snd j π ≫ σ.left ≫ pullback.fst V.hom π := by
  rw [pointSmallEtaleBaseChangeFiberIso_inv_app_left]
  exact chain_lift (pointLiftOfSection e.inv t _ ρ).left
    ((smallEtaleBaseChange (pullback.snd j π)).map σ).left
    ((smallEtaleBaseChangeComp (pullback.snd j π) π).inv.app V).left
    (eqToHom (congrArg (fun k : pullback j π ⟶ S ↦ (smallEtaleBaseChange k).obj V)
      pullback.condition.symm)).left
    ((smallEtaleBaseChangeComp (pullback.fst j π) j).hom.app V).left
    (pullback.fst (pullback.snd V.hom j) (pullback.fst j π)) (pullback.fst V.hom j)
    (pullback.fst V.hom (pullback.fst j π ≫ j)) (pullback.fst V.hom (pullback.snd j π ≫ π))
    (pullback.fst (pullback.snd V.hom π) (pullback.snd j π)) (pullback.fst V.hom π)
    (pullback.fst (Scheme.Etale.mk (𝟙 SH)).hom (pullback.snd j π)) σ.left
    t e.inv (pullback.snd j π)
    (smallEtaleBaseChangeComp_hom_app_left_fst (pullback.fst j π) j V)
    (smallEtaleBaseChange_eqToHom_left_fst pullback.condition.symm V)
    (smallEtaleBaseChangeComp_inv_app_left_fst (pullback.snd j π) π V)
    (smallEtaleBaseChange_map_left_fst (pullback.snd j π) σ)
    (pointLiftOfSection_left_fst j π e t ρ)

end Lift

section Boundary

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (B' : BigEtaleSite.{u}) (U : B'.Scheme) (j : U.1 ⟶ S)
  (K : Type u) [Field K] (e : pullback j (strictHenselizationToBase B S hS s) ≅ Spec (.of K))
  (hK : B'.Contains (Spec (.of K))) (g : B'.obj (Spec (.of K)) hK ⟶ U)
  (hg : B'.inclusion.map g = e.inv ≫ pullback.fst j (strictHenselizationToBase B S hS s))

/-- `directImageStalkIsoBaseChangeSections` is the composite of the identification of the stalk at
`s` with sections over the strict henselization, the base change isomorphism of the square formed
by `j` and `Spec 𝒪^{sh}_{S,s} ⟶ S`, and the identification of sections of a pushforward along
`pullback.snd` with sections over `U ×_S Spec 𝒪^{sh}`. -/
theorem directImageStalkIsoBaseChangeSections_eq [QuasiCompact j] [QuasiSeparated j] :
    directImageStalkIsoBaseChangeSections B S hS s j =
      Functor.isoWhiskerLeft _ (stalkIsoStrictHenselizationGamma B S hS s) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        @asIso _ _ _ _ (Functor.whiskerRight
          (smallEtaleSetBaseChange.{u, 0} (pullback.fst j (strictHenselizationToBase B S hS s))
            (pullback.snd j (strictHenselizationToBase B S hS s)) j
            (strictHenselizationToBase B S hS s) pullback.condition)
          (Sheaf.Γ (strictHenselization B S hS s).smallEtaleTopology (Type (u + 1))))
          (@NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
            (fun F => isIso_whiskerRight_smallEtaleSetBaseChange_app B S hS s j F)) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, 0}
            (pullback.fst j (strictHenselizationToBase B S hS s)))
          (smallEtalePushforwardGammaIso.{u, 0}
            (pullback.snd j (strictHenselizationToBase B S hS s))) :=
  rfl

/-- **Stacks 03Q9 in degree zero, on components**: the stalk at `s` of `j_* F` goes to the
sections over `Spec 𝒪^{sh}` of the pull-back, then through the base change map of the square
to the sections of `fst⁻¹ F` over `U ×_S Spec 𝒪^{sh}`. -/
theorem directImageStalkIsoBaseChangeSections_hom_app [QuasiCompact j] [QuasiSeparated j]
    (F : Sheaf U.1.smallEtaleTopology (Type (u + 1))) :
    (directImageStalkIsoBaseChangeSections B S hS s j).hom.app F =
      (stalkIsoStrictHenselizationGamma B S hS s).hom.app
          (((smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
            (smallEtaleTopology S) (smallEtaleTopology U.1)).obj F) ≫
        (Sheaf.Γ (strictHenselization B S hS s).smallEtaleTopology (Type (u + 1))).map
          ((smallEtaleSetBaseChange.{u, 0} (pullback.fst j (strictHenselizationToBase B S hS s))
            (pullback.snd j (strictHenselizationToBase B S hS s)) j
            (strictHenselizationToBase B S hS s) pullback.condition).app F) ≫
        (smallEtalePushforwardGammaIso.{u, 0}
          (pullback.snd j (strictHenselizationToBase B S hS s))).hom.app
          ((smallEtaleInverseImage.{u, 0}
            (pullback.fst j (strictHenselizationToBase B S hS s))).obj F) :=
  (congrArg (fun φ => φ.hom.app F) (directImageStalkIsoBaseChangeSections_eq B S hS s B' U j)).trans
    (isoChain₀_hom_app _ _ _ _ _ _ _ _ _ _ _ F)

/-- **The stalk of `j_* F` as sections over `Spec K`, on components.** -/
theorem directImageStalkIsoFieldSections_hom_app [QuasiCompact j] [QuasiSeparated j]
    (F : Sheaf U.1.smallEtaleTopology (Type (u + 1))) :
    (directImageStalkIsoFieldSections B S hS s B' U j K e hK g hg).hom.app F =
      (directImageStalkIsoBaseChangeSections B S hS s j).hom.app F ≫
        (smallEtalePushforwardGammaIso.{u, 0} e.hom).inv.app
          ((smallEtaleInverseImage.{u, 0}
            (pullback.fst j (strictHenselizationToBase B S hS s))).obj F) ≫
        (Sheaf.Γ (Spec (.of K)).smallEtaleTopology (Type (u + 1))).map
          ((baseChangeFieldInverseImageIso B S hS s B' U j K e hK g hg).hom.app F) :=
  isoChain₁_hom_app _ _ _ _ _ _ _ _ _ F

private theorem chain_F4 {𝒞 : Type*} [Category* 𝒞]
    {a b c d e f g h i k l m n o p q r w : 𝒞}
    (G : a ⟶ b) (St : b ⟶ c) (ΓBC : c ⟶ d) (γsnd : d ⟶ e) (γei : e ⟶ f) (ΓFI : f ⟶ g)
    (ΓNK : g ⟶ h) (germt : h ⟶ i) (Qh : i ⟶ k) (Pb : k ⟶ l)
    (un : a ⟶ m) (M1 : m ⟶ n) (M2 : n ⟶ o) (M3 : o ⟶ p) (M4 : p ⟶ q) (ΓNTi : q ⟶ e)
    (gW : q ⟶ r) (Q' : r ⟶ w) (E : w ⟶ k) (gw : m ⟶ r) (gy0 : a ⟶ w) (gy : a ⟶ k)
    (hA : G ≫ St ≫ ΓBC ≫ γsnd = un ≫ M1 ≫ M2 ≫ M3 ≫ M4 ≫ ΓNTi)
    (hB : ΓNTi ≫ γei ≫ ΓFI ≫ ΓNK ≫ germt ≫ Qh = gW ≫ Q' ≫ E)
    (hW : M1 ≫ M2 ≫ M3 ≫ M4 ≫ gW = gw) (hU : un ≫ gw ≫ Q' = gy0) (hE : gy0 ≫ E = gy) :
    G ≫ ((St ≫ ΓBC ≫ γsnd) ≫ γei ≫ ΓFI) ≫ (ΓNK ≫ germt) ≫ Qh ≫ Pb = gy ≫ Pb := by
  subst hW hU hE
  simp only [Category.assoc]
  rw [reassoc_of% hA, reassoc_of% hB]

variable (t : GeometricPoint (Spec (.of K)))

/-- The component at `F` of the specialization map `(j_* F)_s ⟶ F_{g(t̄)}` is the identification
of `(j_* F)_s` with the sections of `g⁻¹ F` over `Spec K`, followed by the germ at `t̄`, the
identification of the stalk of `g⁻¹ F` at `t̄` with the stalk of `F` at `g(t̄)`, and the
identification of that stalk with the fibre of the point of the site of `U`. -/
theorem directImageStalkToStalk_app_eq [QuasiCompact j] [QuasiSeparated j]
    (F : Sheaf U.1.smallEtaleTopology (Type (u + 1))) :
    (directImageStalkToStalk B S hS s B' U j K e hK g hg t).app F =
      (directImageStalkIsoFieldSections B S hS s B' U j K e hK g hg).hom.app F ≫
        (smallEtaleGlobalGerm t.hom).app
          ((smallEtaleInverseImage.{u, 0} (B'.inclusion.map g)).obj F) ≫
        (smallEtaleInverseImageStalkIso.{0, u} (B'.inclusion.map g) t.hom).hom.app F ≫
        (pointSmallEtaleSheafFiberIso B' U.1 U.2 (t.map (B'.inclusion.map g))).hom.app F :=
  rfl

/-- **The germ formula for the specialization map of `j_* F` at a boundary point.** The germ at
`s` of a section `τ` of `j_* F` over `V`, at a lift `x` of `s` to `V`, goes to the germ of `τ` at
the lift `y` of `g(t̄)` to `U ×_S V` whose projection to `V` is `t̄ ≫ e⁻¹ ≫ snd ≫ σ ≫ pr_V`, where
`σ` is a section of `V ×_S Spec 𝒪^{sh}` through `x` (read on the bounded site). -/
theorem toPresheafFiber_directImageStalkToStalk [QuasiCompact j] [QuasiSeparated j]
    (F : Sheaf U.1.smallEtaleTopology (Type (u + 1))) (V : S.Etale)
    (x : (pointSmallEtale s.hom).fiber.obj V)
    (σ : Scheme.Etale.mk (𝟙 (strictHenselization B S hS s)) ⟶
      (smallEtaleBaseChange (strictHenselizationToBase B S hS s)).obj V)
    (hσ : geometricPointToStrictHenselization B S hS s ≫ σ.left ≫
      pullback.fst V.hom (strictHenselizationToBase B S hS s) = x.left)
    (y : (pointSmallEtale (t.hom ≫ B'.inclusion.map g)).fiber.obj ((smallEtaleBaseChange j).obj V))
    (hy : y.left ≫ pullback.fst V.hom j = t.hom ≫ e.inv ≫
      pullback.snd j (strictHenselizationToBase B S hS s) ≫ σ.left ≫
        pullback.fst V.hom (strictHenselizationToBase B S hS s)) :
    (pointSmallEtale s.hom).toPresheafFiber V x
        (((smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology S) (smallEtaleTopology U.1)).obj F).obj ≫
      (directImageStalkToStalk B S hS s B' U j K e hK g hg t).app F =
    (pointSmallEtale (t.hom ≫ B'.inclusion.map g)).toPresheafFiber
        ((smallEtaleBaseChange j).obj V) y F.obj ≫
      (pointSmallEtaleSheafFiberIso B' U.1 U.2 (t.map (B'.inclusion.map g))).hom.app F := by
  let π := strictHenselizationToBase B S hS s
  let fst := pullback.fst j π
  let snd := pullback.snd j π
  let X := (smallEtaleInverseImage.{u, 0} fst).obj F
  let hW := isTerminalSmallEtaleBaseChangeObj snd
    (isTerminalEtaleMkId (strictHenselization B S hS s))
  let W := (smallEtaleBaseChange snd).obj (Scheme.Etale.mk (𝟙 (strictHenselization B S hS s)))
  let ρ := (isTerminalSmallEtaleBaseChangeObj e.inv hW).from (Scheme.Etale.mk (𝟙 (Spec (.of K))))
  let L := pointLiftOfSection e.inv t.hom W ρ
  let k4 := (smallEtaleBaseChange snd).map σ
  let k3 := (smallEtaleBaseChangeComp snd π).inv.app V
  let k2 := eqToHom (congrArg (fun k : pullback j π ⟶ S ↦ (smallEtaleBaseChange k).obj V)
    (pullback.condition (f := j) (g := π)).symm)
  let k1 := (smallEtaleBaseChangeComp fst j).hom.app V
  let pt := pointSmallEtale (t.hom ≫ e.inv)
  let w4 := pt.fiber.map k4 L
  let w3 := pt.fiber.map k3 w4
  let w2 := pt.fiber.map k2 w3
  let w1 := pt.fiber.map k1 w2
  let y0 := (pointSmallEtaleBaseChangeFiberIso fst (t.hom ≫ e.inv)).inv.app
    ((smallEtaleBaseChange j).obj V) w1
  have hWc : X.obj.map k1.op ≫ X.obj.map k2.op ≫ X.obj.map k3.op ≫ X.obj.map k4.op ≫
      pt.toPresheafFiber W L X.obj = pt.toPresheafFiber _ w1 X.obj :=
    (congrArg (X.obj.map k1.op ≫ X.obj.map k2.op ≫ X.obj.map k3.op ≫ ·)
      (pt.toPresheafFiber_w k4 L X.obj)).trans
      ((congrArg (X.obj.map k1.op ≫ X.obj.map k2.op ≫ ·) (pt.toPresheafFiber_w k3 w4 X.obj)).trans
        ((congrArg (X.obj.map k1.op ≫ ·) (pt.toPresheafFiber_w k2 w3 X.obj)).trans
          (pt.toPresheafFiber_w k1 w2 X.obj)))
  have hyw : (pointSmallEtaleBaseChangeFiberIso fst (t.hom ≫ e.inv)).hom.app
      ((smallEtaleBaseChange j).obj V) y0 = w1 := by
    simp [y0]
  have hU := smallEtaleInverseImageStalkIso_hom_germ_unit.{0, u} fst (t.hom ≫ e.inv) F
    ((smallEtaleBaseChange j).obj V) y0
  rw [hyw] at hU
  have e0 : (t.hom ≫ e.inv) ≫ fst = t.hom ≫ B'.inclusion.map g := by
    rw [hg, Category.assoc]
  have hE := toPresheafFiber_comp_eqToHom.{0, u} e0 ((smallEtaleBaseChange j).obj V) y0 F.obj
  have hy0 : (CategoryTheory.Over.homMk y0.left (by rw [← e0]; exact CategoryTheory.Over.w y0) :
      (pointSmallEtale (t.hom ≫ B'.inclusion.map g)).fiber.obj ((smallEtaleBaseChange j).obj V)) =
      y :=
    CategoryTheory.Over.OverMorphism.ext (pullback.hom_ext
      ((baseChangeLift_left_fst j π e t.hom V σ ρ).trans hy.symm)
      ((CategoryTheory.Over.w y0).trans (e0.trans (CategoryTheory.Over.w y).symm)))
  rw [hy0] at hE
  rw [directImageStalkToStalk_app_eq, directImageStalkIsoFieldSections_hom_app,
    directImageStalkIsoBaseChangeSections_hom_app]
  exact chain_F4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (toPresheafFiber_directImageStalk_baseChange B S hS s j F V x σ hσ)
    (fieldSections_toPresheafFiber fst F e (B'.inclusion.map g) hg t.hom hW) hWc hU hE

/-- The endomorphism `id ×_S β_a` of `U ×_S Spec 𝒪^{sh}` induced by the endomorphism `β_a` of the
strict henselization attached to an endomorphism `a` of the geometric point `s`. -/
def baseChangeStrictHenselizationEndomorphism (a : GeometricPoint.Hom s s) :
    pullback j (strictHenselizationToBase B S hS s) ⟶
      pullback j (strictHenselizationToBase B S hS s) :=
  pullback.map j (strictHenselizationToBase B S hS s) j (strictHenselizationToBase B S hS s)
    (𝟙 U.1) (strictHenselizationEndomorphism B S hS a) (𝟙 S)
    ((Category.comp_id j).trans (Category.id_comp j).symm)
    ((Category.comp_id _).trans (strictHenselizationEndomorphism_comp_toBase B S hS a).symm)

/-- The endomorphism `β_a` of the strict henselization induced by an endomorphism `a` of the
geometric point is an isomorphism: it is the spectrum of the map of Tag 04FN on the étale local
ring, which is an isomorphism for every morphism of geometric points. -/
instance isIso_strictHenselizationEndomorphism (a : GeometricPoint.Hom s s) :
    IsIso (strictHenselizationEndomorphism B S hS a) := by
  have : IsIso (etaleLocalRingEndomorphism B S hS a) := by
    have := geometricPointStalkMap_isIso B S hS a RingCat.{u}
    exact NatIso.isIso_app_of_isIso _ _
  have : IsIso (CommRingCat.ofHom (etaleLocalRingEndomorphism B S hS a).hom) :=
    (asIso (etaleLocalRingEndomorphism B S hS a)).ringCatIsoToRingEquiv.toCommRingCatIso.isIso_hom
  unfold strictHenselizationEndomorphism
  infer_instance

/-- The endomorphism `id ×_S β_a` of `U ×_S Spec 𝒪^{sh}` is an isomorphism. -/
instance isIso_baseChangeStrictHenselizationEndomorphism (a : GeometricPoint.Hom s s) :
    IsIso (baseChangeStrictHenselizationEndomorphism B S hS s B' U j a) := by
  unfold baseChangeStrictHenselizationEndomorphism
  infer_instance

/-- **The lift `ã` exists**: for an algebraic geometric point `t̄` of `Spec K` and an endomorphism
`a` of `s`, there is an automorphism `ã` of `Spec Ω` lifting the automorphism of `Spec K` induced
by `id ×_S β_a`, i.e. with `ã ≫ t̄ = t̄ ≫ e⁻¹ ≫ (id ×_S β_a) ≫ e`. -/
theorem exists_iso_comp_hom_eq_baseChangeStrictHenselizationEndomorphism (ht : t.IsAlgebraic)
    (a : GeometricPoint.Hom s s) :
    ∃ ã : t.source ≅ t.source, ã.hom ≫ t.hom =
      t.hom ≫ e.inv ≫ baseChangeStrictHenselizationEndomorphism B S hS s B' U j a ≫ e.hom :=
  GeometricPoint.exists_iso_comp_hom_eq_hom_comp t ht _ (Subsingleton.elim _ _)

/-- If `ã` lifts the endomorphism `e ∘ Φ ∘ e⁻¹` along `t`, and `Φ ≫ q = q'`, then
`ã ≫ t ≫ e⁻¹ ≫ q = t ≫ e⁻¹ ≫ q'`. -/
private theorem comp_comp_inv_comp_of_comp_eq {𝒞 : Type*} [Category* 𝒞] {A P X T : 𝒞}
    (ã : A ⟶ A) (t : A ⟶ X) (e : P ≅ X) (Φ : P ⟶ P) (q q' : P ⟶ T)
    (hã : ã ≫ t = t ≫ e.inv ≫ Φ ≫ e.hom) (hq : Φ ≫ q = q') :
    ã ≫ t ≫ e.inv ≫ q = t ≫ e.inv ≫ q' := by
  rw [← Category.assoc ã, hã]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hq]

include hg in
/-- A lift `ã` to `t̄` of the endomorphism `e ∘ (id ×_S β_a) ∘ e⁻¹` of `Spec K` is an endomorphism
of the geometric point `g(t̄)` of `U`. -/
theorem comp_inclusion_map_of_comp_baseChangeStrictHenselizationEndomorphism
    (a : GeometricPoint.Hom s s) (ã : t.source ⟶ t.source)
    (hã : ã ≫ t.hom = t.hom ≫ e.inv ≫ baseChangeStrictHenselizationEndomorphism B S hS s B' U j a ≫
      e.hom) :
    ã ≫ t.hom ≫ B'.inclusion.map g = t.hom ≫ B'.inclusion.map g := by
  rw [hg]
  exact comp_comp_inv_comp_of_comp_eq ã t.hom e _ _ _ hã
    ((pullback.lift_fst _ _ _).trans (Category.comp_id _))

/-- A lift `ã` to `t̄` of the endomorphism `e ∘ (id ×_S β_a) ∘ e⁻¹` of `Spec K` intertwines the
projection `t̄ ≫ e⁻¹ ≫ snd` to the strict henselization with `β_a`. -/
private theorem comp_snd_of_comp_baseChangeStrictHenselizationEndomorphism
    (a : GeometricPoint.Hom s s) (ã : t.source ⟶ t.source)
    (hã : ã ≫ t.hom = t.hom ≫ e.inv ≫ baseChangeStrictHenselizationEndomorphism B S hS s B' U j a ≫
      e.hom) :
    ã ≫ t.hom ≫ e.inv ≫ pullback.snd j (strictHenselizationToBase B S hS s) =
      t.hom ≫ e.inv ≫ pullback.snd j (strictHenselizationToBase B S hS s) ≫
        strictHenselizationEndomorphism B S hS a := by
  exact comp_comp_inv_comp_of_comp_eq ã t.hom e _ _ _ hã (pullback.lift_snd _ _ _)

private theorem chain_frob {𝒞 : Type*} [Category* 𝒞] {a b c e : 𝒞}
    (germ : a ⟶ b) (Fr : b ⟶ b) (sp : b ⟶ c) (fn : c ⟶ c) (germx : a ⟶ b) (gy : a ⟶ e)
    (gy' : a ⟶ e) (Hm : e ⟶ e) (P : e ⟶ c)
    (h1 : germ ≫ Fr = germx) (h2 : germx ≫ sp = gy' ≫ P) (h3 : germ ≫ sp = gy ≫ P)
    (h4 : P ≫ fn = Hm ≫ P) (h5 : gy ≫ Hm = gy') :
    germ ≫ Fr ≫ sp = germ ≫ sp ≫ fn := by
  rw [reassoc_of% h1, h2, reassoc_of% h3, h4, reassoc_of% h5]

/-- **The specialization map of `j_* F` at a boundary point is Frobenius-equivariant** (the
Frobenius of `H⁰_loc`, Weil II 1.8): for an endomorphism `a` of the geometric point `s` and an
endomorphism `ã` of `t̄` lifting the induced endomorphism `e ∘ (id ×_S β_a) ∘ e⁻¹` of `Spec K`,
the map of stalks of `j_* F` at `s` induced by `a` corresponds, under the specialization map, to
the map of Tag 04FN along `ã`, an endomorphism of the geometric point `g(t̄)` of `U`. -/
theorem pointSmallEtaleHom_sheafFiber_comp_directImageStalkToStalk [QuasiCompact j]
    [QuasiSeparated j] (a : GeometricPoint.Hom s s) (ã : t.source ⟶ t.source)
    (hã : ã ≫ t.hom = t.hom ≫ e.inv ≫ baseChangeStrictHenselizationEndomorphism B S hS s B' U j a ≫
      e.hom)
    (hãg : ã ≫ t.hom ≫ B'.inclusion.map g = t.hom ≫ B'.inclusion.map g)
    (F : Sheaf U.1.smallEtaleTopology (Type (u + 1))) :
    (pointSmallEtaleHom s.hom s.hom a.hom a.comm).sheafFiber.app
        (((smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology S) (smallEtaleTopology U.1)).obj F) ≫
      (directImageStalkToStalk B S hS s B' U j K e hK g hg t).app F =
    (directImageStalkToStalk B S hS s B' U j K e hK g hg t).app F ≫
      (geometricPointStalkMap B' U.1 U.2
        (⟨ã, hãg⟩ : GeometricPoint.Hom (t.map (B'.inclusion.map g)) (t.map (B'.inclusion.map g)))
        (Type (u + 1))).app
          ((SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).inverse.obj F).obj := by
  let π := strictHenselizationToBase B S hS s
  let pt := geometricPointToStrictHenselization B S hS s
  let β := strictHenselizationEndomorphism B S hS a
  let gU := B'.inclusion.map g
  refine (pointSmallEtale s.hom).presheafFiber_hom_ext (fun V x => ?_)
  obtain ⟨τ, hτ1, hτ2⟩ := exists_hom_of_strictlyHenselian s π pt
    (geometricPointToStrictHenselization_comp B S hS s)
    (geometricPointToStrictHenselization_base_default B S hS s) V.hom x.left
    (CategoryTheory.Over.w x)
  let mkσ (τ' : strictHenselization B S hS s ⟶ V.left) (h : τ' ≫ V.hom = π) :
      Scheme.Etale.mk (𝟙 (strictHenselization B S hS s)) ⟶ (smallEtaleBaseChange π).obj V :=
    MorphismProperty.Over.homMk (pullback.lift τ' (𝟙 _) (h.trans (Category.id_comp π).symm))
      (pullback.lift_snd _ _ _) trivial
  have hβτ : (β ≫ τ) ≫ V.hom = π :=
    ((Category.assoc _ _ _).trans ((congrArg (β ≫ ·) hτ1).trans
      (strictHenselizationEndomorphism_comp_toBase B S hS a)))
  let σ := mkσ τ hτ1
  let σ' := mkσ (β ≫ τ) hβτ
  have hσ : pt ≫ σ.left ≫ pullback.fst V.hom π = x.left :=
    (congrArg (pt ≫ ·) (pullback.lift_fst τ (𝟙 _) _)).trans hτ2
  let x' : (pointSmallEtale s.hom).fiber.obj V :=
    (CategoryTheory.Over.homMk a.hom a.comm : Over.mk s.hom ⟶ Over.mk s.hom) ≫ x
  have hσ' : pt ≫ σ'.left ≫ pullback.fst V.hom π = x'.left :=
    (congrArg (pt ≫ ·) (pullback.lift_fst (β ≫ τ) (𝟙 _) _)).trans (((reassoc_of%
      geometricPointToStrictHenselization_comp_strictHenselizationEndomorphism B S hS a) τ).trans
        (congrArg (a.hom ≫ ·) hτ2))
  have hyc : (t.hom ≫ e.inv ≫ pullback.snd j π ≫ τ) ≫ V.hom = (t.hom ≫ gU) ≫ j := by
    simp only [Category.assoc]
    rw [hτ1, ← pullback.condition, ← Category.assoc e.inv, ← hg]
  let y : (pointSmallEtale (t.hom ≫ gU)).fiber.obj ((smallEtaleBaseChange j).obj V) :=
    CategoryTheory.Over.homMk (pullback.lift _ _ hyc) (pullback.lift_snd _ _ _)
  have hy : y.left ≫ pullback.fst V.hom j =
      t.hom ≫ e.inv ≫ pullback.snd j π ≫ σ.left ≫ pullback.fst V.hom π :=
    (pullback.lift_fst _ _ hyc).trans (congrArg (fun k => t.hom ≫ e.inv ≫ pullback.snd j π ≫ k)
      (pullback.lift_fst τ (𝟙 _) _).symm)
  let y' : (pointSmallEtale (t.hom ≫ gU)).fiber.obj ((smallEtaleBaseChange j).obj V) :=
    (CategoryTheory.Over.homMk ã hãg : Over.mk (t.hom ≫ gU) ⟶ Over.mk (t.hom ≫ gU)) ≫ y
  have hy' : y'.left ≫ pullback.fst V.hom j =
      t.hom ≫ e.inv ≫ pullback.snd j π ≫ σ'.left ≫ pullback.fst V.hom π :=
    ((Category.assoc _ _ _).trans (congrArg (ã ≫ ·) (pullback.lift_fst _ _ hyc))).trans
      (((reassoc_of% comp_snd_of_comp_baseChangeStrictHenselizationEndomorphism B S hS s B' U j K e
        t a ã hã) τ).trans (congrArg (fun k => t.hom ≫ e.inv ≫ pullback.snd j π ≫ k)
          (pullback.lift_fst (β ≫ τ) (𝟙 _) _)).symm)
  exact chain_frob _ _ _ _ _ _ _ _ _
    (toPresheafFiber_pointSmallEtaleHom s.hom s.hom a.hom a.comm
      (((smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology S) (smallEtaleTopology U.1)).obj F).obj V x)
    (toPresheafFiber_directImageStalkToStalk B S hS s B' U j K e hK g hg t F V x' σ' hσ' y' hy')
    (toPresheafFiber_directImageStalkToStalk B S hS s B' U j K e hK g hg t F V x σ hσ y hy)
    (pointSmallEtaleSheafFiberIso_hom_naturality B' U.1 U.2
      (⟨ã, hãg⟩ : GeometricPoint.Hom (t.map gU) (t.map gU)) F)
    (toPresheafFiber_pointSmallEtaleHom (t.hom ≫ gU) (t.hom ≫ gU) ã hãg F.obj
      ((smallEtaleBaseChange j).obj V) y)

end Boundary

section ModuleFrobenius

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (B' : BigEtaleSite.{u}) (U : B'.Scheme) (j : U.1 ⟶ S)
  (K : Type u) [Field K] (e : pullback j (strictHenselizationToBase B S hS s) ≅ Spec (.of K))
  (hK : B'.Contains (Spec (.of K))) (g : B'.obj (Spec (.of K)) hK ⟶ U)
  (hg : B'.inclusion.map g = e.inv ≫ pullback.fst j (strictHenselizationToBase B S hS s))
  (t : GeometricPoint (Spec (.of K))) (R : Type) [Ring R]

/-- The component at `M` of `directImageStalkAbForgetIso` is the inverse of the identification of
the fibre at `s` of the underlying presheaf of sets of `j_* M` with the underlying set of its
fibre. -/
theorem directImageStalkAbForgetIso_hom_app
    (M : Sheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (directImageStalkAbForgetIso S s B' U j R).hom.app M =
      ((pointSmallEtale s.hom).presheafFiberCompIso (forget (ModuleCat.{u + 1} R))).inv.app
        (((smallEtaleBaseChange j).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
          (smallEtaleTopology S) (smallEtaleTopology U.1)).obj M).obj := by
  simp only [Functor.comp_obj, directImageStalkAbForgetIso, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, Functor.whiskerLeft_app, GrothendieckTopology.Point.sheafFiberCompIso_inv_app]
  exact Category.id_comp _

/-- The identification of the underlying set of `(j_* M)_s` with the stalk of `j_*` of the
underlying sheaf of sets intertwines the maps induced by an endomorphism of `s`. -/
theorem directImageStalkAbForgetIso_hom_app_pointSmallEtaleHom (a : GeometricPoint.Hom s s)
    (M : Sheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (directImageStalkAbForgetIso S s B' U j R).hom.app M ≫
      (pointSmallEtaleHom s.hom s.hom a.hom a.comm).sheafFiber.app
        (((smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology S) (smallEtaleTopology U.1)).obj
          ((sheafCompose U.1.smallEtaleTopology (forget (ModuleCat.{u + 1} R))).obj M)) =
      (forget AddCommGrpCat.{u + 1}).map ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
          ((pointSmallEtaleHom s.hom s.hom a.hom a.comm).sheafFiber.app
            (((smallEtaleBaseChange j).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
              (smallEtaleTopology S) (smallEtaleTopology U.1)).obj M))) ≫
        (directImageStalkAbForgetIso S s B' U j R).hom.app M := by
  rw [directImageStalkAbForgetIso_hom_app]
  exact GrothendieckTopology.Point.Hom.presheafFiberCompIso_inv_naturality
    (forget (ModuleCat.{u + 1} R)) (pointSmallEtaleHom s.hom s.hom a.hom a.comm)
    (((smallEtaleBaseChange j).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
      (smallEtaleTopology S) (smallEtaleTopology U.1)).obj M).obj

/-- The identification of the underlying set of the stalk of `M` at `g(t̄)` with the stalk of the
underlying sheaf of sets intertwines the maps of Tag 04FN, inverse form. -/
theorem pointStalkAbForgetIso_inv_app_geometricPointStalkMap
    (M : Sheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} R))
    (a' : GeometricPoint.Hom (t.map (B'.inclusion.map g)) (t.map (B'.inclusion.map g))) :
    (pointStalkAbForgetIso B' U K hK g t R).inv.app M ≫
      (forget AddCommGrpCat.{u + 1}).map ((forget₂ (ModuleCat.{u + 1} R)
        AddCommGrpCat.{u + 1}).map ((geometricPointStalkMap B' U.1 U.2 a' (ModuleCat.{u + 1} R)).app
          ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} R)).inverse.obj M).obj)) =
      (geometricPointStalkMap B' U.1 U.2 a' (Type (u + 1))).app
          ((SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).inverse.obj
            ((sheafCompose U.1.smallEtaleTopology (forget (ModuleCat.{u + 1} R))).obj M)).obj ≫
        (pointStalkAbForgetIso B' U K hK g t R).inv.app M := by
  let Ms := (sheafCompose U.1.smallEtaleTopology (forget (ModuleCat.{u + 1} R))).obj M
  have h3' : (forget AddCommGrpCat.{u + 1}).map ((forget₂ (ModuleCat.{u + 1} R)
      AddCommGrpCat.{u + 1}).map ((geometricPointStalkMap B' U.1 U.2 a' (ModuleCat.{u + 1} R)).app
        ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} R)).inverse.obj M).obj)) ≫
      (pointStalkAbForgetIso B' U K hK g t R).hom.app M =
      (pointStalkAbForgetIso B' U K hK g t R).hom.app M ≫
        (geometricPointStalkMap B' U.1 U.2 a' (Type (u + 1))).app
          ((SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).inverse.obj Ms).obj := by
    ext w
    exact pointStalkAbForgetIso_hom_app_geometricPointStalkMap B' U K hK g t R M a' w
  exact (CommSq.horiz_inv (f := (pointStalkAbForgetIso B' U K hK g t R).app M)
    (i := (pointStalkAbForgetIso B' U K hK g t R).app M) ⟨h3'.symm⟩).w

/-- The specialization map of `j_* M` is the additive map attached to its underlying natural map
of sets. -/
theorem directImageStalkToStalkHom_eq_natTransAddHom [QuasiCompact j] [QuasiSeparated j]
    (M : Sheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    directImageStalkToStalkHom B S hS s B' U j K e hK g hg t R M =
      natTransAddHom (directImageStalkAb S s B' U j R) (pointStalkAb B' U K hK g t R)
        (directImageStalkToStalkAb B S hS s B' U j K e hK g hg t R) M :=
  rfl

/-- **The specialization map of `j_* M` at a boundary point is Frobenius-equivariant**, for sheaves
of `R`-modules, against any endomorphism `fG` of the stalk `M_{g(t̄)}` which on underlying sets is
the map of Tag 04FN along a lift `ã` to `t̄` of the endomorphism `id ×_S β_a` of
`U ×_S Spec 𝒪^{sh} ≅ Spec K` induced by `a` (for instance `fG` the map of Tag 04FN on `M` itself,
by `pointStalkAbForgetIso_inv_app_geometricPointStalkMap`). -/
theorem directImageStalkToStalkHom_pointSmallEtaleHom [QuasiCompact j] [QuasiSeparated j]
    (a : GeometricPoint.Hom s s) (ã : t.source ⟶ t.source)
    (hã : ã ≫ t.hom = t.hom ≫ e.inv ≫ baseChangeStrictHenselizationEndomorphism B S hS s B' U j a ≫
      e.hom)
    (hãg : ã ≫ t.hom ≫ B'.inclusion.map g = t.hom ≫ B'.inclusion.map g)
    (M : Sheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} R))
    (fG : (pointStalkAb B' U K hK g t R).obj M ⟶ (pointStalkAb B' U K hK g t R).obj M)
    (hG : (pointStalkAbForgetIso B' U K hK g t R).inv.app M ≫
        (forget AddCommGrpCat.{u + 1}).map fG =
      (geometricPointStalkMap B' U.1 U.2
        (⟨ã, hãg⟩ : GeometricPoint.Hom (t.map (B'.inclusion.map g)) (t.map (B'.inclusion.map g)))
        (Type (u + 1))).app ((SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).inverse.obj
          ((sheafCompose U.1.smallEtaleTopology (forget (ModuleCat.{u + 1} R))).obj M)).obj ≫
        (pointStalkAbForgetIso B' U K hK g t R).inv.app M)
    (z : (directImageStalkAb S s B' U j R).obj M) :
    ConcreteCategory.hom (directImageStalkToStalkHom B S hS s B' U j K e hK g hg t R M)
        (ConcreteCategory.hom (X := (directImageStalkAb S s B' U j R).obj M)
          (Y := (directImageStalkAb S s B' U j R).obj M)
          ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
          ((pointSmallEtaleHom s.hom s.hom a.hom a.comm).sheafFiber.app
            (((smallEtaleBaseChange j).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
              (smallEtaleTopology S) (smallEtaleTopology U.1)).obj M))) z) =
      ConcreteCategory.hom fG
        (ConcreteCategory.hom
          (directImageStalkToStalkHom B S hS s B' U j K e hK g hg t R M) z) := by
  have h1 := directImageStalkAbForgetIso_hom_app_pointSmallEtaleHom S s B' U j R a M
  have h2 := pointSmallEtaleHom_sheafFiber_comp_directImageStalkToStalk B S hS s B' U j K e hK g hg
    t a ã hã hãg ((sheafCompose U.1.smallEtaleTopology (forget (ModuleCat.{u + 1} R))).obj M)
  have key := natTransAddHom_comm_whiskerLeft (directImageStalkAb S s B' U j R)
    (pointStalkAb B' U K hK g t R) (directImageStalkToStalkAb B S hS s B' U j K e hK g hg t R)
    (sheafCompose U.1.smallEtaleTopology (forget (ModuleCat.{u + 1} R)))
    ((smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
      (smallEtaleTopology S) (smallEtaleTopology U.1))
    ((pointSmallEtale s.hom).sheafFiber (A := Type (u + 1)))
    (SmallEtale.sheafEquiv B' U.1 U.2 (Type (u + 1))).inverse
    (geometricPointSitePoint B' U.1 U.2 (t.map (B'.inclusion.map g))).sheafFiber
    (directImageStalkAbForgetIso S s B' U j R) (pointStalkAbForgetIso B' U K hK g t R)
    (directImageStalkToStalk B S hS s B' U j K e hK g hg t) rfl M _ fG _ _ h1 h2 hG z
  rw [directImageStalkToStalkHom_eq_natTransAddHom]
  convert key using 2

/-- The module-level Frobenius equivariance with the map of Tag 04FN on `M`. -/
theorem directImageStalkToStalkHom_pointSmallEtaleHom_geometricPointStalkMap [QuasiCompact j]
    [QuasiSeparated j] (a : GeometricPoint.Hom s s) (ã : t.source ⟶ t.source)
    (hã : ã ≫ t.hom = t.hom ≫ e.inv ≫ baseChangeStrictHenselizationEndomorphism B S hS s B' U j a ≫
      e.hom)
    (hãg : ã ≫ t.hom ≫ B'.inclusion.map g = t.hom ≫ B'.inclusion.map g)
    (M : Sheaf U.1.smallEtaleTopology (ModuleCat.{u + 1} R))
    (z : (directImageStalkAb S s B' U j R).obj M) :
    ConcreteCategory.hom (directImageStalkToStalkHom B S hS s B' U j K e hK g hg t R M)
        (ConcreteCategory.hom (X := (directImageStalkAb S s B' U j R).obj M)
          (Y := (directImageStalkAb S s B' U j R).obj M)
          ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
          ((pointSmallEtaleHom s.hom s.hom a.hom a.comm).sheafFiber.app
            (((smallEtaleBaseChange j).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
              (smallEtaleTopology S) (smallEtaleTopology U.1)).obj M))) z) =
      ConcreteCategory.hom (X := (pointStalkAb B' U K hK g t R).obj M)
        (Y := (pointStalkAb B' U K hK g t R).obj M)
        ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map
          ((geometricPointStalkMap B' U.1 U.2
            (⟨ã, hãg⟩ :
              GeometricPoint.Hom (t.map (B'.inclusion.map g)) (t.map (B'.inclusion.map g)))
            (ModuleCat.{u + 1} R)).app
            ((SmallEtale.sheafEquiv B' U.1 U.2 (ModuleCat.{u + 1} R)).inverse.obj M).obj))
        (ConcreteCategory.hom (directImageStalkToStalkHom B S hS s B' U j K e hK g hg t R M) z) :=
  directImageStalkToStalkHom_pointSmallEtaleHom B S hS s B' U j K e hK g hg t R a ã hã hãg M _
    (pointStalkAbForgetIso_inv_app_geometricPointStalkMap B' U K hK g t R M ⟨ã, hãg⟩) z

end ModuleFrobenius

section LevelFrobenius

open AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (B' : BigEtaleSite.{u}) (U : B'.Scheme) [ConnectedSpace U.1] (x : GeometricPoint U.1)
  (j : U.1 ⟶ S)
  (K : Type u) [Field K] (e : pullback j (strictHenselizationToBase B S hS s) ≅ Spec (.of K))
  (hK : B'.Contains (Spec (.of K))) (g : B'.obj (Spec (.of K)) hK ⟶ U)
  (hg : B'.inclusion.map g = e.inv ≫ pullback.fst j (strictHenselizationToBase B S hS s))
  (t : GeometricPoint (Spec (.of K)))
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  (ρ : EtaleFundamentalGroup U.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)
  (p : finiteEtaleFiberFunctor (X := U.1) (t.map (B'.inclusion.map g)) ≅
    finiteEtaleFiberFunctor x) (k : ℕ)

/-- **Frobenius on `H⁰_loc` of the `k`-th level of `ℱ_ρ` at a boundary point** (Weil II 1.8): under
the identification of `(j_* ℱ_k)_s` with a submodule of `(ℤ/ℓ^kℤ)^r`, the map of stalks induced by
an endomorphism `a` of `s` is `ρ mod ℓ^k` of the element of `π₁(U, x̄)` which the path `p`
transports from any `σ ∈ π₁(U, g(t̄))` acting on the fibre functor as the lift `ã` to `t̄` of the
endomorphism `id ×_S β_a` of `U ×_S Spec 𝒪^{sh} ≅ Spec K`. -/
theorem representationLevelDirectImageStalkHom_pointSmallEtaleHom [QuasiCompact j]
    [QuasiSeparated j] (a : GeometricPoint.Hom s s) (ã : t.source ⟶ t.source)
    (hã : ã ≫ t.hom = t.hom ≫ e.inv ≫ baseChangeStrictHenselizationEndomorphism B S hS s B' U j a ≫
      e.hom)
    (hãg : ã ≫ t.hom ≫ B'.inclusion.map g = t.hom ≫ B'.inclusion.map g)
    (σ : EtaleFundamentalGroup U.1 (t.map (B'.inclusion.map g)))
    (hσ : σ.hom = finiteEtaleFiberMap
      (⟨ã, hãg⟩ : GeometricPoint.Hom (t.map (B'.inclusion.map g)) (t.map (B'.inclusion.map g))))
    (y : (directImageStalkAb S s B' U j (ZMod (ℓ ^ k))).obj
      (representationLevelSheafMathlib B' U x ρ hρ k)) :
    (ConcreteCategory.hom
        (representationLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p k)
        (ConcreteCategory.hom (X := (directImageStalkAb S s B' U j (ZMod (ℓ ^ k))).obj
            (representationLevelSheafMathlib B' U x ρ hρ k))
          (Y := (directImageStalkAb S s B' U j (ZMod (ℓ ^ k))).obj
            (representationLevelSheafMathlib B' U x ρ hρ k))
          ((forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1}).map
            ((pointSmallEtaleHom s.hom s.hom a.hom a.comm).sheafFiber.app
              (((smallEtaleBaseChange j).sheafPushforwardContinuous
                (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))
                (smallEtaleTopology S) (smallEtaleTopology U.1)).obj
                (representationLevelSheafMathlib B' U x ρ hρ k)))) y)).down =
      levelRepresentation ρ k (etaleFundamentalGroupMulEquiv p σ)
        (ConcreteCategory.hom
          (representationLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p k)
          y).down := by
  have h1 := directImageStalkToStalkHom_pointSmallEtaleHom_geometricPointStalkMap B S hS s B' U j K
    e hK g hg t (ZMod (ℓ ^ k)) a ã hã hãg (representationLevelSheafMathlib B' U x ρ hρ k) y
  have h2 := representationLevelPointStalkTrivialization_geometricPointStalkMap B' U x K hK g t ρ hρ
    p k ⟨ã, hãg⟩ σ hσ
    (ConcreteCategory.hom (directImageStalkToStalkHom B S hS s B' U j K e hK g hg t
      (ZMod (ℓ ^ k)) (representationLevelSheafMathlib B' U x ρ hρ k)) y)
  exact (congrArg (fun w => (ConcreteCategory.hom
    (representationLevelPointStalkTrivialization B' U x K hK g t ρ hρ p k).hom w).down) h1).trans h2

/-- **Frobenius on `H⁰_loc` of the levels of `ℱ_ρ` is `ρ` of a lift of Frobenius** (Weil II 1.8),
existence form: for an algebraic geometric point `t̄` of `Spec K` and an endomorphism `a` of `s`
there is `σ ∈ π₁(U, g(t̄))` such that, on the inertia invariants in `(ℤ/ℓ^kℤ)^r`, the map of
stalks of `j_* ℱ_k` induced by `a` is `ρ mod ℓ^k` of the transport of `σ` along `p`. -/
theorem exists_representationLevelDirectImageStalkHom_pointSmallEtaleHom [QuasiCompact j]
    [QuasiSeparated j] (ht : t.IsAlgebraic) (a : GeometricPoint.Hom s s) :
    ∃ σ : EtaleFundamentalGroup U.1 (t.map (B'.inclusion.map g)),
      ∀ y : (directImageStalkAb S s B' U j (ZMod (ℓ ^ k))).obj
        (representationLevelSheafMathlib B' U x ρ hρ k),
      (ConcreteCategory.hom
          (representationLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p k)
          (ConcreteCategory.hom (X := (directImageStalkAb S s B' U j (ZMod (ℓ ^ k))).obj
              (representationLevelSheafMathlib B' U x ρ hρ k))
            (Y := (directImageStalkAb S s B' U j (ZMod (ℓ ^ k))).obj
              (representationLevelSheafMathlib B' U x ρ hρ k))
            ((forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1}).map
              ((pointSmallEtaleHom s.hom s.hom a.hom a.comm).sheafFiber.app
                (((smallEtaleBaseChange j).sheafPushforwardContinuous
                  (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))
                  (smallEtaleTopology S) (smallEtaleTopology U.1)).obj
                  (representationLevelSheafMathlib B' U x ρ hρ k)))) y)).down =
        levelRepresentation ρ k (etaleFundamentalGroupMulEquiv p σ)
          (ConcreteCategory.hom
            (representationLevelDirectImageStalkHom B S hS s B' U x j K e hK g hg t ρ hρ p k)
            y).down := by
  obtain ⟨ã, hã⟩ := exists_iso_comp_hom_eq_baseChangeStrictHenselizationEndomorphism B S hS s B' U
    j K e t ht a
  have hãg := comp_inclusion_map_of_comp_baseChangeStrictHenselizationEndomorphism B S hS s B' U j
    K e hK g hg t a ã.hom hã
  exact ⟨GeometricPoint.sourceAutElement (S := U.1) (t.map (B'.inclusion.map g)) ã hãg,
    representationLevelDirectImageStalkHom_pointSmallEtaleHom B S hS s B' U x j K e hK g hg t
      ρ hρ p k a ã.hom hã hãg _
      (GeometricPoint.sourceAutElement_hom_eq_finiteEtaleFiberMap (S := U.1)
        (t.map (B'.inclusion.map g)) ã hãg _ rfl)⟩

end LevelFrobenius

end Stacks.EtaleCohomology

end
