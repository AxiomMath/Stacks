module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImageStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Normality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationFunctoriality

/-!
# The inverse image of `ℱ_ρ` is `ℱ_{ρ ∘ f_*}`

Let `f : Y ⟶ X` be a morphism of connected Noetherian schemes, `ȳ` a geometric point of `Y` and
`ρ : π₁(X, f(ȳ)) → GL_r(ℤ_ℓ)` continuous. The ℓ-adic sheaf `ℱ_ρ` has as level `k` the finite
locally constant sheaf of `ℤ/ℓ^k`-modules attached by Tag 0DV5 (2) to `(ℤ/ℓ^k)^r` with the action
through `ρ`; Tag 0DV6, in the conjugate form `f⁻¹ ∘ E_X⁻¹ ≅ E_Y⁻¹ ∘ res_{f_*}`
(`Stacks.EtaleCohomology.nonempty_pullback_inverse_iso`), identifies the underlying abelian
sheaves of `f⁻¹` of these levels with those of `ℱ_{ρ ∘ f_*}`, naturally in the finite module.

To get an isomorphism of sheaves of modules compatible with the transition maps, the comparison
is built through adjunction: its adjoint `ℱ_{ρ,k} → f_* ℱ_{ρ ∘ f_*, k}` is, on underlying abelian
sheaves, the unit of `f⁻¹ ⊣ f_*` followed by `f_*` of the abelian comparison, which commutes with
the scalar operations by naturality, hence is a map of sheaves of modules. Its adjoint is an
isomorphism because the unit of the inverse image of sheaves of modules is, on underlying abelian
sheaves, the unit of the inverse image of abelian sheaves up to an isomorphism
(`Stacks.Sites.AbelianPullback.exists_forget₂_sheafAdjunctionContinuous_unit`, from the uniqueness
of left adjoints behind `Stacks.Sites.AbelianPullback.moduleSheafPullbackScalarSquare`), and it
commutes with the transition maps because the reduction maps of both sides are images of the
reduction `(ℤ/ℓ^{k+1})^r → (ℤ/ℓ^k)^r`, which the abelian comparison respects by naturality.

## Main results

* `Stacks.Sites.AbelianPullback.exists_forget₂_sheafAdjunctionContinuous_unit`: the unit of the
  inverse image of sheaves of modules on underlying abelian sheaves.
* `Stacks.EtaleCohomology.representationLevelInverseImageHom` and
  `Stacks.EtaleCohomology.isIso_representationLevelInverseImageHom`: the level comparisons.
* `Stacks.EtaleCohomology.representationLevelInverseImageHom_transition`: they commute with the
  transition maps.
* `Stacks.EtaleCohomology.representationLAdicSheafInverseImageIso`: **`f⁻¹ℱ_ρ ≅ ℱ_{ρ ∘ f_*}`**
  as ℓ-adic sheaves.
* `Stacks.EtaleCohomology.representationLAdicSheafInverseImageHom_naturality`: the comparison is
  natural in intertwiners `A ρ(g) = ρ'(g) A`, hence respects any extra linear structure given by
  intertwiners, such as the action of a finite `ℤ_ℓ`-algebra `O` on `ℱ_ρ` for an `O`-linear `ρ`.

## References

* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
* [Stacks Project, Tag 0DV6](https://stacks.math.columbia.edu/tag/0DV6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe r v₁ u₁ v₂ u₂ uW

namespace Stacks.Sites.AbelianPullback

section ModulePullbackUnit

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K]
  (Λ : Type r) [Ring Λ]
  [HasSheafify J AddCommGrpCat.{uW}] [HasSheafify K AddCommGrpCat.{uW}]
  [(F.sheafPushforwardContinuous AddCommGrpCat.{uW} J K).IsRightAdjoint]
  [(F.sheafPushforwardContinuous (ModuleCat.{uW} Λ) J K).IsRightAdjoint]
  [J.HasSheafCompose (forget₂ (ModuleCat.{uW} Λ) AddCommGrpCat.{uW})]
  [K.HasSheafCompose (forget₂ (ModuleCat.{uW} Λ) AddCommGrpCat.{uW})]
  [ReflectsLimitsOfSize.{v₁, max v₁ u₁} (forget₂ (ModuleCat.{uW} Λ) AddCommGrpCat.{uW})]
  [ReflectsLimitsOfSize.{v₂, max v₂ u₂} (forget₂ (ModuleCat.{uW} Λ) AddCommGrpCat.{uW})]

/-- **The unit of the inverse image of sheaves of modules is the unit of the inverse image of the
underlying abelian sheaves**, up to an isomorphism `f⁻¹(P_ab) ≅ (f⁻¹P)_ab`. -/
public theorem exists_forget₂_sheafAdjunctionContinuous_unit (P : Sheaf J (ModuleCat.{uW} Λ)) :
    ∃ τ : (F.sheafPullback AddCommGrpCat.{uW} J K).obj
        ((sheafCompose J (forget₂ (ModuleCat.{uW} Λ) AddCommGrpCat.{uW})).obj P) ≅
      (sheafCompose K (forget₂ (ModuleCat.{uW} Λ) AddCommGrpCat.{uW})).obj
        ((F.sheafPullback (ModuleCat.{uW} Λ) J K).obj P),
    (sheafCompose J (forget₂ (ModuleCat.{uW} Λ) AddCommGrpCat.{uW})).map
        ((F.sheafAdjunctionContinuous (ModuleCat.{uW} Λ) J K).unit.app P) =
      (F.sheafAdjunctionContinuous AddCommGrpCat.{uW} J K).unit.app _ ≫
        (F.sheafPushforwardContinuous AddCommGrpCat.{uW} J K).map τ.hom := by
  let hR : ((moduleSheafScalarActionEquivalence K Λ).functor ⋙
        additiveWhiskerRight Λ (F.sheafPushforwardContinuous AddCommGrpCat.{uW} J K)) ⋙
          (moduleSheafScalarActionEquivalence J Λ).inverse ≅
      F.sheafPushforwardContinuous (ModuleCat.{uW} Λ) J K :=
    Functor.isoWhiskerRight (eqToIso (moduleSheafPushforwardScalarSquare F J K Λ)).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (moduleSheafScalarActionEquivalence J Λ).unitIso.symm ≪≫
      Functor.rightUnitor _
  let adj2 := ((moduleSheafScalarActionEquivalence J Λ).toAdjunction.comp
      ((additiveWhiskerRightAdjunction Λ
          (F.sheafAdjunctionContinuous AddCommGrpCat.{uW} J K)).comp
        (moduleSheafScalarActionEquivalence K Λ).symm.toAdjunction)).ofNatIsoRight hR
  let e := (F.sheafAdjunctionContinuous (ModuleCat.{uW} Λ) J K).leftAdjointUniq adj2
  refine ⟨(sheafCompose K (forget₂ (ModuleCat.{uW} Λ) AddCommGrpCat.{uW})).mapIso
    (e.app P).symm, ?_⟩
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (F.sheafAdjunctionContinuous (ModuleCat.{uW} Λ) J K) adj2 P
  have h' : (F.sheafAdjunctionContinuous (ModuleCat.{uW} Λ) J K).unit.app P =
      adj2.unit.app P ≫
        (F.sheafPushforwardContinuous (ModuleCat.{uW} Λ) J K).map (e.inv.app P) := by
    rw [← h, Category.assoc, ← Functor.map_comp]
    simp [e]
  rw [h', Functor.map_comp]
  congr 1

end ModulePullbackUnit

end Stacks.Sites.AbelianPullback

open AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.ConstantSheaf Stacks.GroupCohomology

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : Y ⟶ X) [ConnectedSpace X.1]
  [ConnectedSpace Y.1] {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  (y : GeometricPoint Y.1)
  (β : (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)).inverse ⋙
        finiteLocallyConstantAbelianSheafPullback B f ≅
      ContinuousGAddCommGrp.resIsFinite (etaleFundamentalGroupMap f.hom y) ⋙
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y).inverse)
  (ρ : EtaleFundamentalGroup X.1 (y.map f.hom) →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)

/-- The abelian adjoint `F_X → f_* F_Y` of the comparison `β` at level `k`: the unit of
`f⁻¹ ⊣ f_*` followed by the direct image of `β`. -/
public abbrev representationLevelInverseImageAbelianAdjoint (k : ℕ) :
    representationLevelAbelian B X (y.map f.hom)
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ k ⟶
      (smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2) |>.obj
        (representationLevelAbelian B Y y
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y)
          (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) k) :=
  ((smallEtaleBaseChange B f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).unit.app _ ≫
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).map
      (β.hom.app (levelAbelian ρ hρ k)).hom

/-- **The adjoint `F_X → f_* F_Y` of the comparison at level `k`, as sheaves of
`ℤ/ℓ^kℤ`-modules**: the abelian adjoint commutes with the scalar operations, by naturality of the
unit and of `β`. -/
public def representationLevelInverseImageAdjoint (k : ℕ) :
    representationLevelSheaf B X (y.map f.hom)
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ k ⟶
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))
          (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).obj
        (representationLevelSheaf B Y y
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y)
          (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) k) :=
  (scalarActionToModuleSheaf (SmallEtale.topology B X.1 X.2) (ZMod (ℓ ^ k))).map
    (ObjectProperty.homMk (Y := (additiveWhiskerRight (ZMod (ℓ ^ k))
        ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2))).obj
        (representationLevelScalars B Y y
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y)
          (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) k))
      { app := fun _ => representationLevelInverseImageAbelianAdjoint B f y β ρ hρ k
        naturality := by
          rintro ⟨⟩ ⟨⟩ a
          have hη := ((smallEtaleBaseChange B f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
            (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).unit.naturality
            ((representationLevelScalars B X (y.map f.hom)
              (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom))
              ρ hρ k).obj.map a)
          have hβ := congrArg (fun g => g.hom) (β.hom.naturality
            ((finiteContinuousScalarFunctor (ZMod (ℓ ^ k)) _ (levelModule ρ hρ k)).map a))
          exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hη).trans
            ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
              ((((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
                (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).map_comp _
                  _).symm.trans ((congrArg ((smallEtaleBaseChange B f).sheafPushforwardContinuous
                    AddCommGrpCat.{u + 1} (SmallEtale.topology B X.1 X.2)
                    (SmallEtale.topology B Y.1 Y.2)).map hβ).trans
                  (((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
                    (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).map_comp _
                      _)))))) })

/-- The adjoint has the abelian adjoint as underlying map. -/
public theorem forget₂_representationLevelInverseImageAdjoint (k : ℕ) :
    (sheafCompose (SmallEtale.topology B X.1 X.2)
      (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1})).map
        (representationLevelInverseImageAdjoint B f y β ρ hρ k) =
      representationLevelInverseImageAbelianAdjoint B f y β ρ hρ k :=
  rfl

/-- **The comparison `f⁻¹ F_X → F_Y` at level `n + 1`**, adjoint to
`Stacks.EtaleCohomology.representationLevelInverseImageAdjoint`. -/
public def representationLevelInverseImageHom (n : ℕ) :
    (LAdicSheaf.levelPullback f n).obj (representationLevelSheaf B X (y.map f.hom)
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ (n + 1)) ⟶
      representationLevelSheaf B Y y (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y)
        (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
        (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) (n + 1) :=
  ((LAdicSheaf.levelAdjunction f n).homEquiv _ _).symm
    (representationLevelInverseImageAdjoint B f y β ρ hρ (n + 1))

/-- On underlying abelian sheaves the comparison is `β`, up to the identification of the
underlying abelian sheaf of the inverse image. -/
public theorem exists_forget₂_representationLevelInverseImageHom (n : ℕ) :
    ∃ τ : ((smallEtaleBaseChange B f).sheafPullback AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).obj
        (representationLevelAbelian B X (y.map f.hom)
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ (n + 1)) ≅
      (sheafCompose (SmallEtale.topology B Y.1 Y.2)
        (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1})).obj
        ((LAdicSheaf.levelPullback f n).obj (representationLevelSheaf B X (y.map f.hom)
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ (n + 1))),
      τ.hom ≫ (sheafCompose (SmallEtale.topology B Y.1 Y.2)
        (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1})).map
          (representationLevelInverseImageHom B f y β ρ hρ n) =
        (β.hom.app (levelAbelian ρ hρ (n + 1))).hom := by
  obtain ⟨τ, hτ⟩ := Stacks.Sites.AbelianPullback.exists_forget₂_sheafAdjunctionContinuous_unit
    (smallEtaleBaseChange B f) (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)
    (ZMod (ℓ ^ (n + 1))) (representationLevelSheaf B X (y.map f.hom)
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ (n + 1))
  refine ⟨τ, ?_⟩
  apply (((smallEtaleBaseChange B f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).homEquiv _ _).injective
  have h := congrArg (sheafCompose (SmallEtale.topology B X.1 X.2)
    (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1})).map
    (((LAdicSheaf.levelAdjunction f n).homEquiv_unit _ _
      (representationLevelInverseImageHom B f y β ρ hρ n)).symm.trans
      (Equiv.apply_symm_apply _ _))
  refine ((Adjunction.homEquiv_unit _ _ _ _).trans ?_).trans
    (Adjunction.homEquiv_unit _ _ _ _).symm
  have hp : (sheafCompose (SmallEtale.topology B X.1 X.2)
      (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1})).map
        ((LAdicSheaf.levelPushforward f n).map
          (representationLevelInverseImageHom B f y β ρ hρ n)) =
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).map
        ((sheafCompose (SmallEtale.topology B Y.1 Y.2)
          (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1})).map
          (representationLevelInverseImageHom B f y β ρ hρ n)) := rfl
  exact (congrArg (_ ≫ ·) (Functor.map_comp _ _ _)).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hτ.symm).trans ((congrArg (_ ≫ ·) hp.symm).trans
      ((Functor.map_comp _ _ _).symm.trans
      (h.trans (forget₂_representationLevelInverseImageAdjoint B f y β ρ hρ (n + 1)))))))

/-- **The comparison at each level is an isomorphism.** -/
public instance isIso_representationLevelInverseImageHom (n : ℕ) :
    IsIso (representationLevelInverseImageHom B f y β ρ hρ n) := by
  obtain ⟨τ, hτ⟩ := exists_forget₂_representationLevelInverseImageHom B f y β ρ hρ n
  have : IsIso ((sheafCompose (SmallEtale.topology B Y.1 Y.2)
      (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1})).map
        (representationLevelInverseImageHom B f y β ρ hρ n)) := by
    have e : (sheafCompose (SmallEtale.topology B Y.1 Y.2)
        (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1})).map
          (representationLevelInverseImageHom B f y β ρ hρ n) =
        (τ.symm ≪≫ (ObjectProperty.ι _).mapIso (β.app (levelAbelian ρ hρ (n + 1)))).hom :=
      (Iso.inv_hom_id_assoc τ _).symm.trans (congrArg (τ.inv ≫ ·) hτ)
    rw [e]
    exact Iso.isIso_hom _
  exact isIso_of_reflects_iso _ (sheafCompose (SmallEtale.topology B Y.1 Y.2)
    (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1}))

/-- The abelian adjoints at two objects are compatible with a morphism `g`, by naturality of the
unit and of `β`. -/
private theorem unit_comp_map_hom_naturality {G G' : _} (g : G ⟶ G') :
    ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)).inverse.map g).hom ≫
      (((smallEtaleBaseChange B f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).unit.app _ ≫
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).map
        (β.hom.app G').hom) =
    (((smallEtaleBaseChange B f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).unit.app _ ≫
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).map
        (β.hom.app G).hom) ≫
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).map
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y).inverse.map
          ((ContinuousGAddCommGrp.resIsFinite (etaleFundamentalGroupMap f.hom y)).map g)).hom := by
  have hη := ((smallEtaleBaseChange B f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).unit.naturality
    ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)).inverse.map g).hom
  have hβ := congrArg (fun g => g.hom) (β.hom.naturality g)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hη).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      ((((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).map_comp _
          _).symm.trans ((congrArg ((smallEtaleBaseChange B f).sheafPushforwardContinuous
            AddCommGrpCat.{u + 1} (SmallEtale.topology B X.1 X.2)
            (SmallEtale.topology B Y.1 Y.2)).map hβ).trans
          (((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).map_comp _
              _))))))

/-- The abelian adjoints commute with reduction, by naturality of the unit and of `β`. -/
public theorem representationLevelInverseImageAbelianAdjoint_reduction (k : ℕ) :
    ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)).inverse.map
        (levelAbelianReduction ρ hρ k)).hom ≫
      representationLevelInverseImageAbelianAdjoint B f y β ρ hρ k =
    representationLevelInverseImageAbelianAdjoint B f y β ρ hρ (k + 1) ≫
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).map
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y).inverse.map
          (levelAbelianReduction (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
            (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) k)).hom := by
  exact unit_comp_map_hom_naturality B f y β (levelAbelianReduction ρ hρ k)

variable [IsNoetherian X.1] [IsNoetherian Y.1]

/-- The instance family `∀ n T, HasWeakSheafify` that `LAdicSheaf.inverseImage` asks for, written
so that its components are the instances found for each level. -/
local instance hasWeakSheafify_smallEtale_levels (n : ℕ) (T : B.Scheme) :
    HasWeakSheafify (SmallEtale.topology B T.obj T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) :=
  inferInstance

/-- **Module adjoints lifting the abelian ones commute with the transition maps.** -/
public theorem representationLevelInverseImage_adjoint_transition
    (θ : ∀ k : ℕ, representationLevelSheaf B X (y.map f.hom)
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ k ⟶
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))
          (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).obj
        (representationLevelSheaf B Y y
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y)
          (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) k))
    (hθ : ∀ k, (sheafCompose (SmallEtale.topology B X.1 X.2)
      (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1})).map (θ k) =
        representationLevelInverseImageAbelianAdjoint B f y β ρ hρ k) (n : ℕ) :
    representationLevelTransition B X (y.map f.hom)
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ (n + 1) ≫
      (LAdicSheaf.levelRestrict X n).map (θ (n + 1)) ≫
      (LAdicSheaf.levelPushforwardRestrictIso f n).inv.app _ =
    θ (n + 1 + 1) ≫
      (LAdicSheaf.levelPushforward f (n + 1)).map
        (representationLevelTransition B Y y
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y)
          (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) (n + 1)) := by
  apply (sheafCompose (SmallEtale.topology B X.1 X.2)
    (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1 + 1)))) AddCommGrpCat.{u + 1})).map_injective
  simp only [Functor.map_comp, LAdicSheaf.levelPushforwardRestrictIso, NatIso.ofComponents_inv_app,
    Iso.refl_inv, Functor.map_id, Category.comp_id]
  refine Eq.trans ?_ ((representationLevelInverseImageAbelianAdjoint_reduction B f y β ρ hρ
    (n + 1)).trans ?_)
  · exact congrArg₂ (· ≫ ·) rfl (hθ (n + 1))
  · exact congrArg₂ (· ≫ ·) (hθ (n + 1 + 1)).symm rfl

/-- The level comparisons commute with the transition maps, for any family of module adjoints
lifting the abelian ones. -/
public theorem representationLevelInverseImage_transition_of_adjoint
    (θ : ∀ k : ℕ, representationLevelSheaf B X (y.map f.hom)
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ k ⟶
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} (ZMod (ℓ ^ k)))
          (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).obj
        (representationLevelSheaf B Y y
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y)
          (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) k))
    (hθ : ∀ k, (sheafCompose (SmallEtale.topology B X.1 X.2)
      (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ k))) AddCommGrpCat.{u + 1})).map (θ k) =
        representationLevelInverseImageAbelianAdjoint B f y β ρ hρ k) (n : ℕ) :
    ((LAdicSheaf.levelAdjunction f (n + 1)).homEquiv _ _).symm (θ (n + 1 + 1)) ≫
        representationLevelTransition B Y y
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y)
          (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) (n + 1) =
      LAdicSheaf.inverseImageTransition f (representationLAdicSheaf B X (y.map f.hom)
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ) n ≫
        (LAdicSheaf.levelRestrict Y n).map (((LAdicSheaf.levelAdjunction f n).homEquiv _ _).symm
          (θ (n + 1))) := by
  apply ((LAdicSheaf.levelAdjunction f (n + 1)).homEquiv _ _).injective
  have e5 : (LAdicSheaf.levelAdjunction f n).unit.app (representationLevelSheaf B X (y.map f.hom)
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ (n + 1)) ≫
      (LAdicSheaf.levelPushforward f n).map
        (((LAdicSheaf.levelAdjunction f n).homEquiv _ _).symm (θ (n + 1))) =
      θ (n + 1) :=
    ((LAdicSheaf.levelAdjunction f n).homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have e6 : (LAdicSheaf.levelAdjunction f (n + 1)).unit.app (representationLevelSheaf B X
        (y.map f.hom) (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ
          (n + 1 + 1)) ≫
      (LAdicSheaf.levelPushforward f (n + 1)).map
        (((LAdicSheaf.levelAdjunction f (n + 1)).homEquiv _ _).symm (θ (n + 1 + 1))) =
      θ (n + 1 + 1) :=
    ((LAdicSheaf.levelAdjunction f (n + 1)).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  have hτ := unit_comp_inverseImageTransition B f (representationLAdicSheaf B X (y.map f.hom)
    (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ) n
  have hτ' := ((LAdicSheaf.levelAdjunction f (n + 1)).homEquiv_unit
    ((representationLAdicSheaf B X (y.map f.hom)
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ).level (n + 1))
    ((LAdicSheaf.levelRestrict Y n).obj ((LAdicSheaf.levelPullback f n).obj
      (representationLevelSheaf B X (y.map f.hom)
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ (n + 1))))
    (LAdicSheaf.inverseImageTransition f (representationLAdicSheaf B X (y.map f.hom)
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ) n)).trans hτ
  have hR := (((LAdicSheaf.levelAdjunction f (n + 1)).homEquiv_naturality_right
      (LAdicSheaf.inverseImageTransition f (representationLAdicSheaf B X (y.map f.hom)
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ) n)
      ((LAdicSheaf.levelRestrict Y n).map
        (((LAdicSheaf.levelAdjunction f n).homEquiv _ _).symm (θ (n + 1))))).trans
      (congrArg (· ≫ (LAdicSheaf.levelPushforward f (n + 1)).map
        ((LAdicSheaf.levelRestrict Y n).map
          (((LAdicSheaf.levelAdjunction f n).homEquiv _ _).symm (θ (n + 1)))))
        hτ'))
  have hL := (((LAdicSheaf.levelAdjunction f (n + 1)).homEquiv_naturality_right
      (((LAdicSheaf.levelAdjunction f (n + 1)).homEquiv _ _).symm (θ (n + 1 + 1)))
      (representationLevelTransition B Y y
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y)
          (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) (n + 1))).trans
      (congrArg (· ≫ (LAdicSheaf.levelPushforward f (n + 1)).map
        (representationLevelTransition B Y y
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y)
          (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) (n + 1)))
        (((LAdicSheaf.levelAdjunction f (n + 1)).homEquiv_unit _ _ _).trans e6)))
  have hM : (representationLevelTransition B X (y.map f.hom)
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ (n + 1) ≫
      (LAdicSheaf.levelRestrict X n).map ((LAdicSheaf.levelAdjunction f n).unit.app
        (representationLevelSheaf B X (y.map f.hom)
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ (n + 1))) ≫
      (LAdicSheaf.levelPushforwardRestrictIso f n).inv.app ((LAdicSheaf.levelPullback f n).obj
        (representationLevelSheaf B X (y.map f.hom)
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ
            (n + 1)))) ≫
      (LAdicSheaf.levelPushforward f (n + 1)).map
        ((LAdicSheaf.levelRestrict Y n).map
          (((LAdicSheaf.levelAdjunction f n).homEquiv _ _).symm (θ (n + 1)))) =
      representationLevelTransition B X (y.map f.hom)
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ (n + 1) ≫
      (LAdicSheaf.levelRestrict X n).map (θ (n + 1)) ≫
      (LAdicSheaf.levelPushforwardRestrictIso f n).inv.app _ := by
    refine Eq.trans ?_ (congrArg (fun g => representationLevelTransition B X (y.map f.hom)
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ (n + 1) ≫
        (LAdicSheaf.levelRestrict X n).map g ≫
        (LAdicSheaf.levelPushforwardRestrictIso f n).inv.app _) e5)
    rfl
  exact hL.trans
    ((representationLevelInverseImage_adjoint_transition B f y β ρ hρ θ hθ n).symm.trans
      (hR.trans hM).symm)

/-- **The level comparisons commute with the transition maps.** -/
public theorem representationLevelInverseImageHom_transition (n : ℕ) :
    representationLevelInverseImageHom B f y β ρ hρ (n + 1) ≫
        representationLevelTransition B Y y
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y)
          (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) (n + 1) =
      LAdicSheaf.inverseImageTransition f (representationLAdicSheaf B X (y.map f.hom)
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ) n ≫
        (LAdicSheaf.levelRestrict Y n).map (representationLevelInverseImageHom B f y β ρ hρ n) :=
  representationLevelInverseImage_transition_of_adjoint B f y β ρ hρ
    (representationLevelInverseImageAdjoint B f y β ρ hρ)
    (forget₂_representationLevelInverseImageAdjoint B f y β ρ hρ) n

/-- **The comparison `f⁻¹ℱ_ρ → ℱ_{ρ ∘ f_*}` of ℓ-adic sheaves.** -/
public def representationLAdicSheafInverseImageHom :
    LAdicSheaf.inverseImage f (representationLAdicSheaf B X (y.map f.hom)
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ) ⟶
      representationLAdicSheaf B Y y (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y)
        (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
        (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) where
  app n := representationLevelInverseImageHom B f y β ρ hρ n
  naturality n := representationLevelInverseImageHom_transition B f y β ρ hρ n

public instance isIso_representationLAdicSheafInverseImageHom :
    IsIso (representationLAdicSheafInverseImageHom B f y β ρ hρ) :=
  (LAdicSheaf.isIso_iff_app_isIso _).2 fun n =>
    isIso_representationLevelInverseImageHom B f y β ρ hρ n

/-- **The inverse image of `ℱ_ρ` is `ℱ_{ρ ∘ f_*}`**: for `f : Y ⟶ X` of connected Noetherian
schemes and a continuous `ρ : π₁(X, f(ȳ)) → GL_r(ℤ_ℓ)`, `f⁻¹ℱ_ρ ≅ ℱ_{ρ ∘ f_*}` where
`f_* : π₁(Y, ȳ) → π₁(X, f(ȳ))`, through a choice of the isomorphism of Tag 0DV6. -/
public def representationLAdicSheafInverseImageIso :
    LAdicSheaf.inverseImage f (representationLAdicSheaf B X (y.map f.hom)
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) ρ hρ) ≅
      representationLAdicSheaf B Y y (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y)
        (ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
        (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous) :=
  asIso (representationLAdicSheafInverseImageHom B f y
    (nonempty_pullback_inverse_iso B f y).some ρ hρ)

section Intertwiner

variable {r' : ℕ} {ρ' : EtaleFundamentalGroup X.1 (y.map f.hom) →* GL (Fin r') ℤ_[ℓ]}
  (hρ' : Continuous ρ') (A : Matrix (Fin r') (Fin r) ℤ_[ℓ])
  (hA : ∀ g, A * (ρ g).val = (ρ' g).val * A)

/-- The abelian adjoints commute with the maps induced by an intertwiner. -/
public theorem representationLevelInverseImageAbelianAdjoint_levelAbelianMap (k : ℕ) :
    ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)).inverse.map
        (levelAbelianMap hρ hρ' A hA k)).hom ≫
      representationLevelInverseImageAbelianAdjoint B f y β ρ' hρ' k =
    representationLevelInverseImageAbelianAdjoint B f y β ρ hρ k ≫
      ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).map
        ((canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y).inverse.map
          (levelAbelianMap (ρ := ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
            (ρ' := ρ'.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
            (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous)
            (hρ'.comp (etaleFundamentalGroupMap f.hom y).continuous) A
            (fun g => hA _) k)).hom := by
  exact unit_comp_map_hom_naturality B f y β (levelAbelianMap hρ hρ' A hA k)

/-- **The level comparisons are natural in intertwiners.** -/
public theorem representationLevelInverseImageHom_representationLevelMap (n : ℕ) :
    representationLevelInverseImageHom B f y β ρ hρ n ≫
        representationLevelMap B Y y (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y)
          (ρ := ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (ρ' := ρ'.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous)
          (hρ'.comp (etaleFundamentalGroupMap f.hom y).continuous) A (fun g => hA _) (n + 1) =
      (LAdicSheaf.levelPullback f n).map (representationLevelMap B X (y.map f.hom)
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) hρ hρ' A hA
          (n + 1)) ≫
        representationLevelInverseImageHom B f y β ρ' hρ' n := by
  apply ((LAdicSheaf.levelAdjunction f n).homEquiv _ _).injective
  have e1 : ((LAdicSheaf.levelAdjunction f n).homEquiv _ _)
      (representationLevelInverseImageHom B f y β ρ hρ n) =
      representationLevelInverseImageAdjoint B f y β ρ hρ (n + 1) :=
    Equiv.apply_symm_apply _ _
  have e2 : ((LAdicSheaf.levelAdjunction f n).homEquiv _ _)
      (representationLevelInverseImageHom B f y β ρ' hρ' n) =
      representationLevelInverseImageAdjoint B f y β ρ' hρ' (n + 1) :=
    Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left, e1, e2]
  apply (sheafCompose (SmallEtale.topology B X.1 X.2)
    (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1})).map_injective
  simp only [Functor.map_comp]
  exact (representationLevelInverseImageAbelianAdjoint_levelAbelianMap B f y β ρ hρ hρ' A hA
    (n + 1)).symm

/-- **The comparison `f⁻¹ℱ_ρ → ℱ_{ρ ∘ f_*}` is natural in intertwiners.** -/
public theorem representationLAdicSheafInverseImageHom_naturality :
    representationLAdicSheafInverseImageHom B f y β ρ hρ ≫
        representationLAdicSheafMap B Y y
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B Y y)
          (ρ := ρ.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (ρ' := ρ'.comp (etaleFundamentalGroupMap f.hom y).toMonoidHom)
          (hρ.comp (etaleFundamentalGroupMap f.hom y).continuous)
          (hρ'.comp (etaleFundamentalGroupMap f.hom y).continuous) A (fun g => hA _) =
      LAdicSheaf.inverseImageMap f (representationLAdicSheafMap B X (y.map f.hom)
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X (y.map f.hom)) hρ hρ' A hA) ≫
        representationLAdicSheafInverseImageHom B f y β ρ' hρ' :=
  LAdicSheaf.Hom.ext (h := fun n =>
    representationLevelInverseImageHom_representationLevelMap B f y β ρ hρ hρ' A hA n)

end Intertwiner

end Stacks.EtaleCohomology
