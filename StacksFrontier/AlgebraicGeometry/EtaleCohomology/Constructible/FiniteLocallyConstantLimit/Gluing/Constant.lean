module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Gluing.Transition
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateNaturality
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp

/-!
# The inverse image of a constant sheaf along a composite

The comparison `AlgebraicGeometry.smallEtaleConstantPullbackIso` between the inverse image of a
constant small étale sheaf and the constant sheaf is compatible with the composition comparison
`AlgebraicGeometry.smallEtaleSheafPullbackCompIso'` of inverse images. Both comparisons are
identifications of left adjoints, so this is checked on the right adjoints, where it is the fact
that two morphisms into the final object of the small étale site agree.

## Main results

* `AlgebraicGeometry.SmallEtaleGluing.smallEtaleConstantPullbackIso_comp` — the compatibility.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

/-- The adjoint mate of the identification of two left adjoints of isomorphic right adjoints is
the inverse of that isomorphism. -/
public theorem conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (σ : R₁ ≅ R₂) :
    conjugateEquiv adj₂ adj₁ (Adjunction.leftAdjointUniq (adj₁.ofNatIsoRight σ) adj₂).hom =
      σ.inv :=
  Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom adj₁ σ adj₂

/-- If the mate of `i.inv` is `j.hom`, then the mate of `i.hom` is `j.inv`. -/
private theorem conjugateEquiv_hom_eq_inv_of_inv_eq_hom {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (i : L₂ ≅ L₁) (j : R₂ ≅ R₁)
    (h : conjugateEquiv adj₂ adj₁ i.inv = j.hom) : conjugateEquiv adj₁ adj₂ i.hom = j.inv := by
  have h₂ := conjugateEquiv_comp adj₁ adj₂ adj₁ i.hom i.inv
  rw [h, Iso.inv_hom_id, conjugateEquiv_id] at h₂
  rw [← Category.comp_id (conjugateEquiv adj₁ adj₂ i.hom), ← j.hom_inv_id, ← Category.assoc, h₂,
    Category.id_comp]

/-- The mate of the inverse associator is the inverse associator. -/
private theorem conjugateEquiv_associator_inv {E F : Type*} [Category E] [Category F]
    {L₀₁ : C ⥤ D} {R₁₀ : D ⥤ C} {L₁₂ : D ⥤ E} {R₂₁ : E ⥤ D} {L₂₃ : E ⥤ F} {R₃₂ : F ⥤ E}
    (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁) (adj₂₃ : L₂₃ ⊣ R₃₂) :
    conjugateEquiv ((adj₀₁.comp adj₁₂).comp adj₂₃) (adj₀₁.comp (adj₁₂.comp adj₂₃))
      (Functor.associator _ _ _).inv = (Functor.associator _ _ _).inv :=
  conjugateEquiv_hom_eq_inv_of_inv_eq_hom _ _ (Functor.associator _ _ _).symm
    (Functor.associator _ _ _) (conjugateEquiv_associator_hom adj₀₁ adj₁₂ adj₂₃)

end CategoryTheory

namespace AlgebraicGeometry

namespace SmallEtaleGluing

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]

/-- The comparison between inverse images of constant sheaves is compatible with the
composition comparison of inverse images. -/
private theorem smallEtaleSheafPullbackConstantSheafIso_comp {X Y Z : B.Scheme} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    Functor.whiskerLeft (constantSheaf (SmallEtale.topology B Z.obj Z.property) A)
        (smallEtaleSheafPullbackCompIso B X Y Z f g A).hom ≫
      (smallEtaleSheafPullbackConstantSheafIso B (f ≫ g) A).hom =
    Functor.whiskerRight (smallEtaleSheafPullbackConstantSheafIso B g A).hom
        (smallEtaleSheafPullback B A f) ≫
      (smallEtaleSheafPullbackConstantSheafIso B f A).hom := by
  let adjC := fun (W : B.Scheme) => constantSheafAdj (SmallEtale.topology B W.obj W.property) A
    (SmallEtale.finalIsTerminal B W.obj W.property)
  let adjP := fun {W W' : B.Scheme} (k : W ⟶ W') =>
    (smallEtaleBaseChange B k).sheafAdjunctionContinuous A
      (SmallEtale.topology B W'.obj W'.property) (SmallEtale.topology B W.obj W.property)
  let σ := fun {W W' : B.Scheme} (k : W ⟶ W') =>
    Stacks.ConstantSheaf.pushforwardSectionsIsoOfTerminal (smallEtaleBaseChange B k) A
      (SmallEtale.topology B W'.obj W'.property) (SmallEtale.topology B W.obj W.property)
      (smallEtaleFinalBaseChangeIso B k)
  have hN : ∀ {W W' : B.Scheme} (k : W ⟶ W'),
      conjugateEquiv (adjC W) ((adjC W').comp (adjP k))
        (smallEtaleSheafPullbackConstantSheafIso B k A).hom = (σ k).inv := fun k =>
    conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _
  let e := Functor.sheafPushforwardContinuousComp' (smallEtaleBaseChange_compIso B X Y Z f g).val
    A (SmallEtale.topology B Z.obj Z.property) (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B X.obj X.property)
  have hI : conjugateEquiv (adjP (f ≫ g)) ((adjP g).comp (adjP f))
      (smallEtaleSheafPullbackCompIso B X Y Z f g A).hom = e.inv :=
    conjugateEquiv_hom_eq_inv_of_inv_eq_hom _ _ _ e
      (Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _)
  have hR : Functor.whiskerRight (smallEtaleSheafPullbackConstantSheafIso B g A).hom
        (smallEtaleSheafPullback B A f) ≫ (smallEtaleSheafPullbackConstantSheafIso B f A).hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (smallEtaleSheafPullbackConstantSheafIso B g A).hom
          (smallEtaleSheafPullback B A f) ≫
        (smallEtaleSheafPullbackConstantSheafIso B f A).hom := by ext; simp
  apply (conjugateEquiv (adjC X) ((adjC Z).comp ((adjP g).comp (adjP f)))).injective
  rw [← conjugateEquiv_comp (adjC X) ((adjC Z).comp (adjP (f ≫ g))), hN,
    conjugateEquiv_whiskerLeft, hI, hR,
    ← conjugateEquiv_comp (adjC X) (((adjC Z).comp (adjP g)).comp (adjP f)),
    ← conjugateEquiv_comp (adjC X) ((adjC Y).comp (adjP f)), hN, conjugateEquiv_whiskerRight,
    hN, conjugateEquiv_associator_inv]
  have hσ : ∀ {W W' : B.Scheme} (k : W ⟶ W')
      (G : Sheaf (SmallEtale.topology B W.obj W.property) A),
      (σ k).inv.app G = G.obj.map (smallEtaleFinalBaseChangeIso B k).hom.op := fun _ _ => rfl
  have he : ∀ (G : Sheaf (SmallEtale.topology B X.obj X.property) A),
      (e.inv.app G).hom.app (op (SmallEtale.final B Z.obj Z.property)) =
        G.obj.map ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app
          (SmallEtale.final B Z.obj Z.property)).op := fun _ => Category.comp_id _
  ext N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.comp_id, hσ]
  show _ ≫ (e.inv.app N).hom.app (op (SmallEtale.final B Z.obj Z.property)) = _
  rw [he]
  refine ((N.obj.map_comp _ _).symm.trans ?_).trans (N.obj.map_comp _
    ((smallEtaleBaseChange B f).op.map (smallEtaleFinalBaseChangeIso B g).hom.op))
  congr 1
  exact Quiver.Hom.unop_inj ((SmallEtale.finalIsTerminal B X.obj X.property).hom_ext _ _)

/-- **The inverse image of a constant sheaf along a composite.** -/
public theorem smallEtaleConstantPullbackIso_comp {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (e : f ≫ g = h) (E : A) :
    (smallEtaleSheafPullbackCompIso' B A f g h e).hom.app
        ((constantSheaf (SmallEtale.topology B Z.obj Z.property) A).obj E) ≫
      (smallEtaleConstantPullbackIso B A h E).hom =
    (smallEtaleSheafPullback B A f).map (smallEtaleConstantPullbackIso B A g E).hom ≫
      (smallEtaleConstantPullbackIso B A f E).hom := by
  subst e
  rw [smallEtaleSheafPullbackCompIso'_rfl]
  exact NatTrans.congr_app (smallEtaleSheafPullbackConstantSheafIso_comp B A f g) E

/-- The transport of an isomorphism of constant sheaves along a morphism `a`: its inverse image,
read between constant sheaves through `AlgebraicGeometry.smallEtaleConstantPullbackIso`. -/
public def constantTransport {T O : B.Scheme} (a : T ⟶ O) {E E' : A}
    (τ : (constantSheaf (SmallEtale.topology B O.obj O.property) A).obj E ≅
      (constantSheaf (SmallEtale.topology B O.obj O.property) A).obj E') :
    (constantSheaf (SmallEtale.topology B T.obj T.property) A).obj E ≅
      (constantSheaf (SmallEtale.topology B T.obj T.property) A).obj E' :=
  (smallEtaleConstantPullbackIso B A a E).symm ≪≫ (smallEtaleSheafPullback B A a).mapIso τ ≪≫
    smallEtaleConstantPullbackIso B A a E'

/-- **The inverse image of a gluing isomorphism between constant sheaves.** -/
public theorem pullbackTransition_constant {Y Y' X₁ X₂ : B.Scheme} (g : Y' ⟶ Y) (f₁ : Y ⟶ X₁)
    (f₂ : Y ⟶ X₂) {E E' : A}
    (τ : (constantSheaf (SmallEtale.topology B Y.obj Y.property) A).obj E ≅
      (constantSheaf (SmallEtale.topology B Y.obj Y.property) A).obj E')
    (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    pullbackTransition B A g (smallEtaleConstantPullbackIso B A f₁ E ≪≫ τ ≪≫
        (smallEtaleConstantPullbackIso B A f₂ E').symm) gf₁ gf₂ h₁ h₂ =
      smallEtaleConstantPullbackIso B A gf₁ E ≪≫ constantTransport B A g τ ≪≫
        (smallEtaleConstantPullbackIso B A gf₂ E').symm := by
  have k₁ := smallEtaleConstantPullbackIso_comp B A g f₁ gf₁ h₁ E
  have k₂ := smallEtaleConstantPullbackIso_comp B A g f₂ gf₂ h₂ E'
  simp only [Iso.app_hom] at k₁ k₂
  apply Iso.ext
  simp only [pullbackTransition, constantTransport, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← cancel_epi ((smallEtaleSheafPullbackCompIso' B A g f₁ gf₁ h₁).hom.app
      ((constantSheaf (SmallEtale.topology B X₁.obj X₁.property) A).obj E)),
    Iso.hom_inv_id_app_assoc, reassoc_of% k₁, Iso.hom_inv_id_app_assoc]
  congr 2
  rw [← cancel_mono ((smallEtaleSheafPullbackConstantSheafIso B gf₂ A).hom.app E'),
    Category.assoc, k₂, Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]

end SmallEtaleGluing

end AlgebraicGeometry

end
