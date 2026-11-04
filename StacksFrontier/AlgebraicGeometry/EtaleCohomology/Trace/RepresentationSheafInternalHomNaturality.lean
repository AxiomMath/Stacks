module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafInternalHom

/-!
# Naturality of `Hom(ℱ_M, ℱ_W) = ℱ_{Hom(M, W)}` in `M`

The isomorphism `AlgebraicGeometry.representationSheafModuleSheafHomIso` of
`SheafHom_{ℤ/n}(ℱ_M, ℱ_W)` with the sheaf of the `Λᵐᵒᵖ`-module `Hom_ℤ(M, W)` is natural in the
finite `Λ`-module `M` with continuous `π₁(X, x)`-action.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf Stacks.GroupCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1) (Λ : Type) [Ring Λ] [Finite Λ]

omit [ConnectedSpace X.1] in
/-- **`internalHomSheafEquivFunctorIso` is natural in the first variable.** -/
lemma internalHomSheafEquivFunctorIso_naturality
    {𝒜 𝒜' : Sheaf (SmallEtale.topology B X.1 X.2) AddCommGrpCat.{u + 1}} (w : 𝒜' ⟶ 𝒜)
    (ℬ : Sheaf (SmallEtale.topology B X.1 X.2) AddCommGrpCat.{u + 1}) :
    Stacks.Sites.internalHomSheafPrecomp X.1.smallEtaleTopology
        ((SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor.map w) _ ≫
        (internalHomSheafEquivFunctorIso B X 𝒜' ℬ).hom =
      (internalHomSheafEquivFunctorIso B X 𝒜 ℬ).hom ≫
        (SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor.map
          (Stacks.Sites.internalHomSheafPrecomp (SmallEtale.topology B X.1 X.2) w ℬ) := by
  let Φ := SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}
  let P := Stacks.Sites.internalHomSheafPrecomp X.1.smallEtaleTopology (Φ.functor.map w)
    (Φ.functor.obj ℬ)
  let A := Stacks.Sites.internalHomSheafPushforwardIso (J := SmallEtale.topology B X.1 X.2)
    (SmallEtale.toEtaleSite B X.1 X.2) (Φ.functor.obj 𝒜) (Φ.functor.obj ℬ)
  let A' := Stacks.Sites.internalHomSheafPushforwardIso (J := SmallEtale.topology B X.1 X.2)
    (SmallEtale.toEtaleSite B X.1 X.2) (Φ.functor.obj 𝒜') (Φ.functor.obj ℬ)
  let C := Stacks.Sites.internalHomSheafCongr (SmallEtale.topology B X.1 X.2)
    (Φ.unitIso.app 𝒜).symm (Φ.unitIso.app ℬ).symm
  let C' := Stacks.Sites.internalHomSheafCongr (SmallEtale.topology B X.1 X.2)
    (Φ.unitIso.app 𝒜').symm (Φ.unitIso.app ℬ).symm
  have h₁ : Φ.inverse.map P ≫ A'.hom =
      A.hom ≫ Stacks.Sites.internalHomSheafPrecomp (SmallEtale.topology B X.1 X.2)
        (Φ.inverse.map (Φ.functor.map w)) (Φ.inverse.obj (Φ.functor.obj ℬ)) :=
    Stacks.Sites.internalHomSheafPushforwardIso_naturality (J₁ := SmallEtale.topology B X.1 X.2)
      (SmallEtale.toEtaleSite B X.1 X.2) (Φ.functor.map w) (Φ.functor.obj ℬ)
  have h₂ : Stacks.Sites.internalHomSheafPrecomp (SmallEtale.topology B X.1 X.2)
        (Φ.inverse.map (Φ.functor.map w)) (Φ.inverse.obj (Φ.functor.obj ℬ)) ≫ C'.hom =
      C.hom ≫ Stacks.Sites.internalHomSheafPrecomp (SmallEtale.topology B X.1 X.2) w ℬ :=
    Stacks.Sites.internalHomSheafPrecomp_comp_internalHomSheafCongr
      (SmallEtale.topology B X.1 X.2) (Φ.unitIso.app 𝒜).symm (Φ.unitIso.app 𝒜').symm
      (Φ.unitIso.app ℬ).symm (Φ.inverse.map (Φ.functor.map w)) w (Φ.unitIso.inv.naturality w)
  let H := internalHomSheaf X.1.smallEtaleTopology (Φ.functor.obj 𝒜) (Φ.functor.obj ℬ)
  let H' := internalHomSheaf X.1.smallEtaleTopology (Φ.functor.obj 𝒜') (Φ.functor.obj ℬ)
  have h₃ : P ≫ Φ.counitIso.inv.app H' = Φ.counitIso.inv.app H ≫ Φ.functor.map (Φ.inverse.map P) :=
    Φ.counitIso.inv.naturality P
  have key : Φ.inverse.map P ≫ A'.hom ≫ C'.hom =
      (A.hom ≫ C.hom) ≫ Stacks.Sites.internalHomSheafPrecomp (SmallEtale.topology B X.1 X.2) w ℬ :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ C'.hom) h₁).trans
      ((Category.assoc _ _ _).trans ((congrArg (A.hom ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))
  calc P ≫ Φ.counitIso.inv.app H' ≫ Φ.functor.map (A'.hom ≫ C'.hom)
      = (P ≫ Φ.counitIso.inv.app H') ≫ Φ.functor.map (A'.hom ≫ C'.hom) :=
        (Category.assoc _ _ _).symm
    _ = (Φ.counitIso.inv.app H ≫ Φ.functor.map (Φ.inverse.map P)) ≫
          Φ.functor.map (A'.hom ≫ C'.hom) :=
        congrArg (· ≫ Φ.functor.map (A'.hom ≫ C'.hom)) h₃
    _ = Φ.counitIso.inv.app H ≫ Φ.functor.map (Φ.inverse.map P ≫ A'.hom ≫ C'.hom) :=
        (Category.assoc _ _ _).trans
          (congrArg (Φ.counitIso.inv.app H ≫ ·) (Φ.functor.map_comp _ _).symm)
    _ = (Φ.counitIso.inv.app H ≫ Φ.functor.map (A.hom ≫ C.hom)) ≫
          Φ.functor.map
            (Stacks.Sites.internalHomSheafPrecomp (SmallEtale.topology B X.1 X.2) w ℬ) :=
        (congrArg (fun φ ↦ Φ.counitIso.inv.app H ≫ Φ.functor.map φ) key).trans
          ((congrArg (Φ.counitIso.inv.app H ≫ ·) (Φ.functor.map_comp _ _)).trans
            (Category.assoc _ _ _).symm)

omit [ConnectedSpace X.1] in
/-- `sheafComposeForgetUliftIso` is natural. -/
lemma sheafComposeForgetUliftIso_naturality (R : Type) [Ring R]
    {S S' : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} R)} (h : S ⟶ S') :
    (sheafCompose (SmallEtale.topology B X.1 X.2)
        (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).map
        ((sheafCompose (SmallEtale.topology B X.1 X.2)
          (ModuleCat.uliftFunctor.{0, u + 1} R)).map h) ≫
        (sheafComposeForgetUliftIso B X R S').hom =
      (sheafComposeForgetUliftIso B X R S).hom ≫
        (sheafCompose (SmallEtale.topology B X.1 X.2)
          (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).map h := by
  apply Sheaf.hom_ext
  ext U a
  rfl

/-- The morphism of finite locally constant abelian sheaves underlying `ℱ_g`, on the site of
Stacks 021B. -/
abbrev representationAbelianSheafSmallMap (R : Type) [Ring R] [Finite R]
    {N N' : FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1 x)}
    (g : N ⟶ N') :
    representationAbelianSheafSmall B X x R N ⟶ representationAbelianSheafSmall B X x R N' :=
  ObjectProperty.homMk ((sheafCompose (SmallEtale.topology B X.1 X.2)
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).map
      ((finiteTypeLocallyConstantModuleSheafEquivalence B X x R).inverse.map g).hom)

/-- **`representationSheafForgetIso` is natural.** -/
lemma representationSheafForgetIso_naturality (R : Type) [Ring R] [Finite R]
    {N N' : FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1 x)}
    (g : N ⟶ N') :
    (sheafCompose X.1.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).map
        ((representationSheaf B X x R).map g) ≫ (representationSheafForgetIso B X x R N').hom =
      (representationSheafForgetIso B X x R N).hom ≫
        (SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor.map
          (representationAbelianSheafSmallMap B X x R g).hom := by
  let := Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize.{u, u, 0, u + 1} R
  have h₁ := (CommSq.mk ((sheafEquivFunctorIsoModuleLift B X R).hom.naturality
    ((sheafCompose (SmallEtale.topology B X.1 X.2) (ModuleCat.uliftFunctor.{0, u + 1} R)).map
      ((finiteTypeLocallyConstantModuleSheafEquivalence B X x R).inverse.map g).hom))).map
    (sheafCompose X.1.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}))
  have h₂ := (CommSq.mk (sheafComposeForgetUliftIso_naturality B X R
    ((finiteTypeLocallyConstantModuleSheafEquivalence B X x R).inverse.map g).hom)).map
    (SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor
  exact (h₁.vert_comp h₂).w

/-- On morphisms, Tag 0DV5 (2) applied to the abelian sheaf map underlying `ℱ_g` is the abelian
map underlying Tag 0DV5 (3) applied to `ℱ_g`. -/
lemma finiteLocallyConstantAbelianSheafEquivalence_map_representationAbelianSheafSmallMap
    (R : Type) [Ring R] [Finite R]
    {N N' : FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1 x)}
    (g : N ⟶ N') :
    (finiteLocallyConstantAbelianSheafEquivalence B X x).functor.map
        (representationAbelianSheafSmallMap B X x R g) =
      (finiteTypeContinuousModuleForgetAbelian R (EtaleFundamentalGroup X.1 x)).map
        ((finiteTypeLocallyConstantModuleSheafEquivalence B X x R).functor.map
          ((finiteTypeLocallyConstantModuleSheafEquivalence B X x R).inverse.map g)) := by
  apply finiteContinuousAbelianHom_ext
  exact AddMonoidHom.ext fun _ ↦ rfl

/-- The counit of Tag 0DV5 (3) is natural, read on the abelian sheaf map underlying `ℱ_g`. -/
lemma representationAbelianSheafSmallMap_counit (R : Type) [Ring R] [Finite R]
    {N N' : FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1 x)}
    (g : N ⟶ N') :
    (finiteLocallyConstantAbelianSheafEquivalence B X x).functor.map
        (representationAbelianSheafSmallMap B X x R g) ≫
        (representationAbelianCounitIso B X x R N').hom =
      (representationAbelianCounitIso B X x R N).hom ≫
        (finiteTypeContinuousModuleForgetAbelian R (EtaleFundamentalGroup X.1 x)).map g := by
  let F := finiteTypeContinuousModuleForgetAbelian R (EtaleFundamentalGroup X.1 x)
  let Q := finiteTypeLocallyConstantModuleSheafEquivalence B X x R
  have h : Q.functor.map (Q.inverse.map g) ≫ Q.counitIso.hom.app N' = Q.counitIso.hom.app N ≫ g :=
    Q.counitIso.hom.naturality g
  exact (congrArg (· ≫ F.map (Q.counitIso.hom.app N'))
      (finiteLocallyConstantAbelianSheafEquivalence_map_representationAbelianSheafSmallMap
        B X x R g)).trans
    ((F.map_comp _ _).symm.trans ((congrArg F.map h).trans (F.map_comp _ _)))

/-- The isomorphism `representationAbelianSheafSmallIso` carries `y` to `d` when Tag 0DV5 (2) does
through the counits. -/
private lemma representationAbelianSheafSmallIso_comm_aux (R : Type) [Ring R] [Finite R]
    {N N' : FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1 x)}
    (y : representationAbelianSheafSmall B X x R N ⟶ representationAbelianSheafSmall B X x R N')
    (d : (finiteTypeContinuousModuleForgetAbelian R (EtaleFundamentalGroup X.1 x)).obj N ⟶
      (finiteTypeContinuousModuleForgetAbelian R (EtaleFundamentalGroup X.1 x)).obj N')
    (h : (finiteLocallyConstantAbelianSheafEquivalence B X x).functor.map y ≫
        (representationAbelianCounitIso B X x R N').hom =
      (representationAbelianCounitIso B X x R N).hom ≫ d) :
    y ≫ (representationAbelianSheafSmallIso B X x R N').hom =
      (representationAbelianSheafSmallIso B X x R N).hom ≫
        (finiteLocallyConstantAbelianSheafEquivalence B X x).inverse.map d := by
  have h₁ :=
    CommSq.mk ((finiteLocallyConstantAbelianSheafEquivalence B X x).unitIso.hom.naturality y)
  have h₂ := (CommSq.mk h).map (finiteLocallyConstantAbelianSheafEquivalence B X x).inverse
  exact (h₁.vert_comp h₂).w

/-- **`representationAbelianSheafSmallIso` is natural.** -/
lemma representationAbelianSheafSmallIso_naturality (R : Type) [Ring R] [Finite R]
    {N N' : FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1 x)}
    (g : N ⟶ N') :
    representationAbelianSheafSmallMap B X x R g ≫
        (representationAbelianSheafSmallIso B X x R N').hom =
      (representationAbelianSheafSmallIso B X x R N).hom ≫
        (finiteLocallyConstantAbelianSheafEquivalence B X x).inverse.map
          ((finiteTypeContinuousModuleForgetAbelian R (EtaleFundamentalGroup X.1 x)).map g) :=
  representationAbelianSheafSmallIso_comm_aux B X x R _ _
    (representationAbelianSheafSmallMap_counit B X x R g)

section Scalar

open Stacks.ModuleCatLift

omit [ConnectedSpace X.1] in
/-- `sheafComposeForgetUliftIso` commutes with multiplication by scalars. -/
lemma sheafComposeForgetUliftIso_smul (R : Type) [Ring R]
    (S : Sheaf (SmallEtale.topology B X.1 X.2) (ModuleCat.{u + 1} R)) (a : R) :
    sheafScalarEnd R (SmallEtale.topology B X.1 X.2)
        ((sheafCompose (SmallEtale.topology B X.1 X.2) (ModuleCat.uliftFunctor.{0, u + 1} R)).obj S)
        a ≫ (sheafComposeForgetUliftIso B X R S).hom =
      (sheafComposeForgetUliftIso B X R S).hom ≫
        sheafScalarEnd R (SmallEtale.topology B X.1 X.2) S a := by
  apply Sheaf.hom_ext
  ext U m
  rfl

/-- **`representationSheafForgetIso` commutes with multiplication by scalars**: on the abelian
sheaf underlying `ℱ_N`, multiplication by `a` corresponds to multiplication by `a` on the sheaf
of Tag 0DV5 (3) on the site of Stacks 021B. -/
lemma representationSheafForgetIso_smul (R : Type) [Ring R] [Finite R]
    (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1 x)) (a : R) :
    sheafScalarEnd R X.1.smallEtaleTopology ((representationSheaf B X x R).obj N) a ≫
        (representationSheafForgetIso B X x R N).hom =
      (representationSheafForgetIso B X x R N).hom ≫
        (SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor.map
          (sheafScalarEnd R (SmallEtale.topology B X.1 X.2)
            (representationModuleSheafSmall B X x R N).obj a) := by
  let := Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize.{u, u, 0, u + 1} R
  have h₁ := CommSq.mk (sheafScalarEnd_naturality R X.1.smallEtaleTopology
    ((sheafEquivFunctorIsoModuleLift B X R).hom.app
      ((sheafCompose (SmallEtale.topology B X.1 X.2) (ModuleCat.uliftFunctor.{0, u + 1} R)).obj
        (representationModuleSheafSmall B X x R N).obj)) a)
  have h₂ := (CommSq.mk (sheafComposeForgetUliftIso_smul B X R
    (representationModuleSheafSmall B X x R N).obj a)).map
    (SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor
  exact (h₁.vert_comp h₂).w

/-- The discrete module map underlying a morphism of finite `R`-`G`-modules commutes with
multiplication by scalars. -/
lemma finiteContinuousScalarFunctor_map_comp_map (R : Type) [Ring R] [Finite R] (G : Type (u + 1))
    [Group G] [TopologicalSpace G] {N N' : FiniteTypeContinuousModule.{0, u + 1, u + 1} R G}
    (φ : N ⟶ N') (a : R) :
    (finiteContinuousScalarFunctor R G N).map (show SingleObj.star R ⟶ SingleObj.star R from a) ≫
        (finiteTypeContinuousModuleForgetAbelian R G).map φ =
      (finiteTypeContinuousModuleForgetAbelian R G).map φ ≫
        (finiteContinuousScalarFunctor R G N').map
          (show SingleObj.star R ⟶ SingleObj.star R from a) := by
  apply finiteContinuousAbelianHom_ext
  exact AddMonoidHom.ext fun m ↦ φ.hom.hom.hom.hom.hom.map_smul a m

/-- Multiplication by a scalar on the abelian sheaf of `ℱ_N` on the site of Stacks 021B, as an
endomorphism of finite locally constant abelian sheaves. -/
abbrev representationAbelianSheafSmallSmul (R : Type) [Ring R] [Finite R]
    (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1 x)) (a : R) :
    representationAbelianSheafSmall B X x R N ⟶ representationAbelianSheafSmall B X x R N :=
  ObjectProperty.homMk (sheafScalarEnd R (SmallEtale.topology B X.1 X.2)
    (representationModuleSheafSmall B X x R N).obj a)

/-- **The counit of Tag 0DV5 (3) commutes with multiplication by scalars**, read on the
discrete `π₁(X, x)`-modules: Tag 0DV5 (2) carries multiplication by `a` on the abelian sheaf of
`ℱ_N` to multiplication by `a` on `N`. -/
lemma representationAbelianCounitIso_smul (R : Type) [Ring R] [Finite R]
    (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1 x)) (a : R) :
    (finiteLocallyConstantAbelianSheafEquivalence B X x).functor.map
        (representationAbelianSheafSmallSmul B X x R N a) ≫
        (representationAbelianCounitIso B X x R N).hom =
      (representationAbelianCounitIso B X x R N).hom ≫
        (finiteContinuousScalarFunctor R (EtaleFundamentalGroup X.1 x) N).map
          (show SingleObj.star R ⟶ SingleObj.star R from a) := by
  have h : representationAbelianSheafSmallSmul B X x R N a =
      (finiteModuleSheafScalarFunctor (SmallEtale.topology B X.1 X.2) R
        ((finiteTypeLocallyConstantModuleSheafBridge B X R).inverse.obj
          (representationModuleSheafSmall B X x R N))).map
        (show SingleObj.star R ⟶ SingleObj.star R from a) := by
    apply ObjectProperty.hom_ext
    apply Sheaf.hom_ext
    ext U m
    rfl
  rw [h]
  exact finiteContinuousScalarFunctor_map_comp_map R (EtaleFundamentalGroup X.1 x)
    ((finiteTypeLocallyConstantModuleSheafEquivalence B X x R).counitIso.hom.app N) a

end Scalar

/-- **`representationAbelianSheafSmallIso` commutes with compatible maps**: a map `y` of the
abelian sheaves of `ℱ_N` and `ℱ_{N'}` which Tag 0DV5 (2) carries to `d` through the counits. -/
lemma representationAbelianSheafSmallIso_comm (R : Type) [Ring R] [Finite R]
    {N N' : FiniteTypeContinuousModule.{0, u + 1, u + 1} R (EtaleFundamentalGroup X.1 x)}
    (y : representationAbelianSheafSmall B X x R N ⟶ representationAbelianSheafSmall B X x R N')
    (d : (finiteTypeContinuousModuleForgetAbelian R (EtaleFundamentalGroup X.1 x)).obj N ⟶
      (finiteTypeContinuousModuleForgetAbelian R (EtaleFundamentalGroup X.1 x)).obj N')
    (h : (finiteLocallyConstantAbelianSheafEquivalence B X x).functor.map y ≫
        (representationAbelianCounitIso B X x R N').hom =
      (representationAbelianCounitIso B X x R N).hom ≫ d) :
    y ≫ (representationAbelianSheafSmallIso B X x R N').hom =
      (representationAbelianSheafSmallIso B X x R N).hom ≫
        (finiteLocallyConstantAbelianSheafEquivalence B X x).inverse.map d :=
  representationAbelianSheafSmallIso_comm_aux B X x R y d h

section Small

variable (n : ℕ) [NeZero n] [Algebra (ZMod n) Λ]

/-- **`internalHomRepresentationSmallIso` is natural in `M`.** -/
lemma internalHomRepresentationSmallIso_naturality
    {M M' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (f : M' ⟶ M)
    (W : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 x)) :
    internalHomFiniteLocallyConstantMap (SmallEtale.topology B X.1 X.2)
        (representationAbelianSheafSmall B X x (ZMod n) W)
        (isFiniteLocallyConstantAbelianSheaf_internalHomSheaf_representation B X x Λ n M W)
        (isFiniteLocallyConstantAbelianSheaf_internalHomSheaf_representation B X x Λ n M' W)
        (representationAbelianSheafSmallMap B X x Λ f) ≫
        (internalHomRepresentationSmallIso B X x Λ n M' W).hom =
      (internalHomRepresentationSmallIso B X x Λ n M W).hom ≫
        (finiteLocallyConstantAbelianSheafEquivalence B X x).inverse.map
          (ContinuousGAddCommGrp.homIsFiniteMap
            ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).map f)
            (𝟙 _)) :=
  internalHomTransportCongrIso_naturality (SmallEtale.topology B X.1 X.2)
    (finiteLocallyConstantSetsEquivalence' B X x) (representationAbelianSheafSmall B X x (ZMod n) W)
    (isFiniteLocallyConstantAbelianSheaf_internalHomSheaf_representation B X x Λ n M W)
    (isFiniteLocallyConstantAbelianSheaf_internalHomSheaf_representation B X x Λ n M' W)
    (representationAbelianSheafSmallMap B X x Λ f)
    (representationAbelianCounitIso B X x Λ M) (representationAbelianCounitIso B X x Λ M')
    (representationAbelianCounitIso B X x (ZMod n) W) _
    (representationAbelianSheafSmallMap_counit B X x Λ f)

omit [Algebra (ZMod n) Λ] in
/-- **`homIsFiniteForgetAbelianIso` is natural in `M`.** -/
lemma homIsFiniteForgetAbelianIso_naturality
    {M M' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (f : M' ⟶ M)
    (W : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 x)) :
    ContinuousGAddCommGrp.homIsFiniteMap
        ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).map f) (𝟙 _) ≫
        (homIsFiniteForgetAbelianIso B X x Λ n M' W).hom =
      (homIsFiniteForgetAbelianIso B X x Λ n M W).hom ≫
        (finiteTypeContinuousModuleForgetAbelian Λᵐᵒᵖ (EtaleFundamentalGroup X.1 x)).map
          ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
            (EtaleFundamentalGroup X.1 x)).obj W.obj)).map f.op) := by
  apply finiteContinuousAbelianHom_ext
  exact AddMonoidHom.ext fun _ ↦ rfl

omit [Algebra (ZMod n) Λ] in
/-- **`homIsFiniteForgetAbelianIso` commutes with the actions of `Λᵐᵒᵖ`**: precomposition with
`r • -` on `Hom_ℤ(M, W)` is the action of `op r`. -/
lemma homIsFiniteForgetAbelianIso_smul
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (W : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 x))
    (r : Λ) :
    ContinuousGAddCommGrp.homIsFiniteMap
        ((finiteContinuousScalarFunctor Λ (EtaleFundamentalGroup X.1 x) M).map
          (show SingleObj.star Λ ⟶ SingleObj.star Λ from r)) (𝟙 _) ≫
        (homIsFiniteForgetAbelianIso B X x Λ n M W).hom =
      (homIsFiniteForgetAbelianIso B X x Λ n M W).hom ≫
        (finiteContinuousScalarFunctor Λᵐᵒᵖ (EtaleFundamentalGroup X.1 x)
          ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
            (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M))).map
          (show SingleObj.star Λᵐᵒᵖ ⟶ SingleObj.star Λᵐᵒᵖ from MulOpposite.op r) := by
  apply finiteContinuousAbelianHom_ext
  exact AddMonoidHom.ext fun _ ↦ rfl

/-- **`internalHomRepresentationSmallIso` commutes with compatible maps** `w` of the abelian
sheaves of `ℱ_{M'}` and `ℱ_M` and `ū : M' ⟶ M` of discrete modules. -/
lemma internalHomRepresentationSmallIso_comm
    {M M' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (W : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 x))
    (w : representationAbelianSheafSmall B X x Λ M' ⟶ representationAbelianSheafSmall B X x Λ M)
    (ū : (finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj M' ⟶
      (finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj M)
    (h₂ : (finiteLocallyConstantAbelianSheafEquivalence B X x).functor.map w ≫
        (representationAbelianCounitIso B X x Λ M).hom =
      (representationAbelianCounitIso B X x Λ M').hom ≫ ū) :
    internalHomFiniteLocallyConstantMap (SmallEtale.topology B X.1 X.2)
        (representationAbelianSheafSmall B X x (ZMod n) W)
        (isFiniteLocallyConstantAbelianSheaf_internalHomSheaf_representation B X x Λ n M W)
        (isFiniteLocallyConstantAbelianSheaf_internalHomSheaf_representation B X x Λ n M' W) w ≫
        (internalHomRepresentationSmallIso B X x Λ n M' W).hom =
      (internalHomRepresentationSmallIso B X x Λ n M W).hom ≫
        (finiteLocallyConstantAbelianSheafEquivalence B X x).inverse.map
          (ContinuousGAddCommGrp.homIsFiniteMap ū (𝟙 _)) :=
  internalHomTransportCongrIso_naturality (SmallEtale.topology B X.1 X.2)
    (finiteLocallyConstantSetsEquivalence' B X x) (representationAbelianSheafSmall B X x (ZMod n) W)
    (isFiniteLocallyConstantAbelianSheaf_internalHomSheaf_representation B X x Λ n M W)
    (isFiniteLocallyConstantAbelianSheaf_internalHomSheaf_representation B X x Λ n M' W) w
    (representationAbelianCounitIso B X x Λ M) (representationAbelianCounitIso B X x Λ M')
    (representationAbelianCounitIso B X x (ZMod n) W) ū h₂

/-- **`internalHomRepresentationSmallDualIso` commutes with compatible maps**, on the site of
Stacks 021B. -/
lemma internalHomRepresentationSmallDualIso_comm
    {M M' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (W : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 x))
    (w : representationAbelianSheafSmall B X x Λ M' ⟶ representationAbelianSheafSmall B X x Λ M)
    (ū : (finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj M' ⟶
      (finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj M)
    (d : (finiteTypeContinuousModuleForgetAbelian Λᵐᵒᵖ (EtaleFundamentalGroup X.1 x)).obj
        ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
          (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M)) ⟶
      (finiteTypeContinuousModuleForgetAbelian Λᵐᵒᵖ (EtaleFundamentalGroup X.1 x)).obj
        ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
          (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M')))
    (y : representationAbelianSheafSmall B X x Λᵐᵒᵖ
        ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
          (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M)) ⟶
      representationAbelianSheafSmall B X x Λᵐᵒᵖ
        ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
          (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M')))
    (h₂ : (finiteLocallyConstantAbelianSheafEquivalence B X x).functor.map w ≫
        (representationAbelianCounitIso B X x Λ M).hom =
      (representationAbelianCounitIso B X x Λ M').hom ≫ ū)
    (h₃ : ContinuousGAddCommGrp.homIsFiniteMap ū (𝟙 _) ≫
        (homIsFiniteForgetAbelianIso B X x Λ n M' W).hom =
      (homIsFiniteForgetAbelianIso B X x Λ n M W).hom ≫ d)
    (h₅ : (finiteLocallyConstantAbelianSheafEquivalence B X x).functor.map y ≫
        (representationAbelianCounitIso B X x Λᵐᵒᵖ
          ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
            (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M'))).hom =
      (representationAbelianCounitIso B X x Λᵐᵒᵖ
          ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
            (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M))).hom ≫ d) :
    Stacks.Sites.internalHomSheafPrecomp (SmallEtale.topology B X.1 X.2) w.hom _ ≫
        (internalHomRepresentationSmallDualIso B X x Λ n M' W).hom =
      (internalHomRepresentationSmallDualIso B X x Λ n M W).hom ≫ y.hom := by
  have q₁ := CommSq.mk (internalHomRepresentationSmallIso_comm B X x Λ n W w ū h₂)
  have q₂ := (CommSq.mk h₃).map (finiteLocallyConstantAbelianSheafEquivalence B X x).inverse
  have q₃ := (CommSq.mk (representationAbelianSheafSmallIso_comm B X x Λᵐᵒᵖ y d h₅)).vert_inv
  exact ((q₁.vert_comp (q₂.vert_comp q₃)).map (ObjectProperty.ι _)).w

/-- **`ℋom(ℱ_M, ℱ_W) ≅ ℱ_{Hom_ℤ(M, W)}` commutes with compatible maps of abelian sheaves.** Let
`u : ℱ_{M'} ⟶ ℱ_M` and `z : ℱ_{Hom(M, W)} ⟶ ℱ_{Hom(M', W)}` be maps of the underlying abelian
sheaves which correspond, through Tag 0DV5 on the site of Stacks 021B, to maps
`ū : M' ⟶ M` and `d : Hom_ℤ(M, W) ⟶ Hom_ℤ(M', W)` of discrete `π₁(X, x)`-modules with
`d = Hom(ū, W)`. Then the isomorphism carries precomposition with `u` to `z`. -/
theorem internalHomRepresentationSheafForgetIso_comm
    {M M' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (W : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 x))
    (u : (sheafCompose X.1.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((representationSheaf B X x Λ).obj M') ⟶
      (sheafCompose X.1.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((representationSheaf B X x Λ).obj M))
    (w : representationAbelianSheafSmall B X x Λ M' ⟶ representationAbelianSheafSmall B X x Λ M)
    (ū : (finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj M' ⟶
      (finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).obj M)
    (d : (finiteTypeContinuousModuleForgetAbelian Λᵐᵒᵖ (EtaleFundamentalGroup X.1 x)).obj
        ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
          (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M)) ⟶
      (finiteTypeContinuousModuleForgetAbelian Λᵐᵒᵖ (EtaleFundamentalGroup X.1 x)).obj
        ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
          (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M')))
    (z : (sheafCompose X.1.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λᵐᵒᵖ) AddCommGrpCat.{u + 1})).obj
        ((representationSheaf B X x Λᵐᵒᵖ).obj
          ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
            (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M))) ⟶
      (sheafCompose X.1.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λᵐᵒᵖ) AddCommGrpCat.{u + 1})).obj
        ((representationSheaf B X x Λᵐᵒᵖ).obj
          ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
            (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M'))))
    (y : representationAbelianSheafSmall B X x Λᵐᵒᵖ
        ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
          (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M)) ⟶
      representationAbelianSheafSmall B X x Λᵐᵒᵖ
        ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
          (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M')))
    (h₁ : u ≫ (representationSheafForgetIso B X x Λ M).hom =
      (representationSheafForgetIso B X x Λ M').hom ≫
        (SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor.map w.hom)
    (h₂ : (finiteLocallyConstantAbelianSheafEquivalence B X x).functor.map w ≫
        (representationAbelianCounitIso B X x Λ M).hom =
      (representationAbelianCounitIso B X x Λ M').hom ≫ ū)
    (h₃ : ContinuousGAddCommGrp.homIsFiniteMap ū (𝟙 _) ≫
        (homIsFiniteForgetAbelianIso B X x Λ n M' W).hom =
      (homIsFiniteForgetAbelianIso B X x Λ n M W).hom ≫ d)
    (h₄ : z ≫ (representationSheafForgetIso B X x Λᵐᵒᵖ
        ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
          (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M'))).hom =
      (representationSheafForgetIso B X x Λᵐᵒᵖ
        ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
          (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M))).hom ≫
        (SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor.map y.hom)
    (h₅ : (finiteLocallyConstantAbelianSheafEquivalence B X x).functor.map y ≫
        (representationAbelianCounitIso B X x Λᵐᵒᵖ
          ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
            (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M'))).hom =
      (representationAbelianCounitIso B X x Λᵐᵒᵖ
          ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
            (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M))).hom ≫ d) :
    Stacks.Sites.internalHomSheafPrecomp X.1.smallEtaleTopology u _ ≫
        (internalHomRepresentationSheafForgetIso B X x Λ n M' W).hom =
      (internalHomRepresentationSheafForgetIso B X x Λ n M W).hom ≫ z := by
  have q₁ := CommSq.mk (Stacks.Sites.internalHomSheafPrecomp_comp_internalHomSheafCongr
    X.1.smallEtaleTopology (representationSheafForgetIso B X x Λ M)
    (representationSheafForgetIso B X x Λ M') (representationSheafForgetIso B X x (ZMod n) W)
    u _ h₁)
  have q₂ := CommSq.mk (internalHomSheafEquivFunctorIso_naturality B X w.hom
    (representationAbelianSheafSmall B X x (ZMod n) W).obj)
  have q₃ := (CommSq.mk (internalHomRepresentationSmallDualIso_comm B X x Λ n W w ū d y h₂ h₃
    h₅)).map (SmallEtale.sheafEquiv B X.1 X.2 AddCommGrpCat.{u + 1}).functor
  have q₄ := (CommSq.mk h₄).vert_inv
  exact (q₁.vert_comp (q₂.vert_comp (q₃.vert_comp q₄))).w

/-- **`ℋom(ℱ_M, ℱ_W) ≅ ℱ_{Hom_ℤ(M, W)}` is natural in `M`**, as abelian sheaves on Mathlib's
small étale site. -/
theorem internalHomRepresentationSheafForgetIso_naturality
    {M M' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (f : M' ⟶ M)
    (W : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 x)) :
    Stacks.Sites.internalHomSheafPrecomp X.1.smallEtaleTopology
        ((sheafCompose X.1.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
          ((representationSheaf B X x Λ).map f)) _ ≫
        (internalHomRepresentationSheafForgetIso B X x Λ n M' W).hom =
      (internalHomRepresentationSheafForgetIso B X x Λ n M W).hom ≫
        (sheafCompose X.1.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λᵐᵒᵖ) AddCommGrpCat.{u + 1})).map
          ((representationSheaf B X x Λᵐᵒᵖ).map
            ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
              (EtaleFundamentalGroup X.1 x)).obj W.obj)).map f.op)) :=
  internalHomRepresentationSheafForgetIso_comm B X x Λ n W _
    (representationAbelianSheafSmallMap B X x Λ f)
    ((finiteTypeContinuousModuleForgetAbelian Λ (EtaleFundamentalGroup X.1 x)).map f)
    ((finiteTypeContinuousModuleForgetAbelian Λᵐᵒᵖ (EtaleFundamentalGroup X.1 x)).map
      ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
        (EtaleFundamentalGroup X.1 x)).obj W.obj)).map f.op)) _
    (representationAbelianSheafSmallMap B X x Λᵐᵒᵖ
      ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
        (EtaleFundamentalGroup X.1 x)).obj W.obj)).map f.op))
    (representationSheafForgetIso_naturality B X x Λ f)
    (representationAbelianSheafSmallMap_counit B X x Λ f)
    (homIsFiniteForgetAbelianIso_naturality B X x Λ n f W)
    (representationSheafForgetIso_naturality B X x Λᵐᵒᵖ _)
    (representationAbelianSheafSmallMap_counit B X x Λᵐᵒᵖ _)

/-- **`ℋom(ℱ_M, ℱ_W) ≅ ℱ_{Hom_ℤ(M, W)}` commutes with the actions of `Λᵐᵒᵖ`**: precomposition
with `r • -` on `ℱ_M` corresponds to multiplication by `op r` on `ℱ_{Hom_ℤ(M, W)}`. -/
theorem internalHomRepresentationSheafForgetIso_smul
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (W : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) (EtaleFundamentalGroup X.1 x))
    (r : Λ) :
    Stacks.Sites.internalHomSheafPrecomp X.1.smallEtaleTopology
        (Stacks.ModuleCatLift.sheafScalarEnd Λ X.1.smallEtaleTopology
          ((representationSheaf B X x Λ).obj M) r) _ ≫
        (internalHomRepresentationSheafForgetIso B X x Λ n M W).hom =
      (internalHomRepresentationSheafForgetIso B X x Λ n M W).hom ≫
        Stacks.ModuleCatLift.sheafScalarEnd Λᵐᵒᵖ X.1.smallEtaleTopology
          ((representationSheaf B X x Λᵐᵒᵖ).obj
            ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
              (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M))) (MulOpposite.op r) :=
  internalHomRepresentationSheafForgetIso_comm B X x Λ n W _
    (representationAbelianSheafSmallSmul B X x Λ M r)
    ((finiteContinuousScalarFunctor Λ (EtaleFundamentalGroup X.1 x) M).map
      (show SingleObj.star Λ ⟶ SingleObj.star Λ from r))
    ((finiteContinuousScalarFunctor Λᵐᵒᵖ (EtaleFundamentalGroup X.1 x)
      ((homDualFunctor Λ ((Stacks.ContinuousCohomology.continuousModuleForget (ZMod n)
        (EtaleFundamentalGroup X.1 x)).obj W.obj)).obj (op M))).map
      (show SingleObj.star Λᵐᵒᵖ ⟶ SingleObj.star Λᵐᵒᵖ from MulOpposite.op r)) _
    (representationAbelianSheafSmallSmul B X x Λᵐᵒᵖ _ (MulOpposite.op r))
    (representationSheafForgetIso_smul B X x Λ M r)
    (representationAbelianCounitIso_smul B X x Λ M r)
    (homIsFiniteForgetAbelianIso_smul B X x Λ n M W r)
    (representationSheafForgetIso_smul B X x Λᵐᵒᵖ _ (MulOpposite.op r))
    (representationAbelianCounitIso_smul B X x Λᵐᵒᵖ _ (MulOpposite.op r))

end Small

end AlgebraicGeometry

end
