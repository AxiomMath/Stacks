module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveBaseFieldLisse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantTwistComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusTwistStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparisonNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusElementDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePointUniverse
public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChangeFiber
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber

/-!
# The lisse sheaf of a module over the Galois group of a finite field, over `k̄`

Let `k` be a finite field with `q` elements, `k̄` an algebraic closure and `Q₀` a finite
`ℤ/m`-module with a continuous action of `π₁(Spec k)`. Over `k̄` the lisse sheaf `ℱ_{Q₀}` becomes
the constant sheaf `Q₀`, and under this identification the Frobenius twist
`ℱ_{Q₀}|_{k̄} ⟶ π̄_*(ℱ_{Q₀}|_{k̄})` is the action of the inverse `Φ⁻¹` of the Frobenius of `k`
followed by the twist of the constant sheaf.

On the sections over the `k̄`-point `ȳ` of `Spec k ×_k Spec k̄` the twist is the geometric
Frobenius on the stalk at the geometric point `Spec k̄ ⟶ Spec k`
(`Stacks.EtaleCohomology.rationalPointFrobeniusEndo_comp_rationalPointSectionsStalkIso_hom`),
which is the map of Tag 04FN along `Spec(σ⁻¹)`, `σ` the arithmetic Frobenius of `k̄`; on the stalk
of a lisse sheaf this is the action of the element `Φ⁻¹` of `π₁`
(`Stacks.EtaleCohomology.lisseSheafStalkAddEquiv_geometricPointStalkMap`), and paths between
fibre functors do not move `Φ`, which acts on every fibre through the Frobenius endomorphism of
the cover.

## Main results

* `Stacks.EtaleCohomology.isIso_of_isIso_app_etaleMk`: a morphism of étale sheaves which is an
  isomorphism on the sections over an étale geometric point meeting every point is an
  isomorphism.
* `Stacks.EtaleCohomology.etaleFundamentalGroupMulEquiv_finiteFieldFrobenius`: paths do not move
  the Frobenius of a finite field.
* `Stacks.EtaleCohomology.exists_isIso_twist_lisseEtaleSheaf_baseField`: over `k̄` the lisse
  sheaf of the descended module is the constant sheaf, carrying its Frobenius twist to the action
  of a lift of `Φ⁻¹` followed by the twist of the constant sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius Stacks.GroupCohomology

universe u r

namespace Stacks.EtaleCohomology

/-! ### Isomorphisms detected at one étale geometric point -/

section Conservative

variable (Λ : Type r) [Ring Λ]

/-- **A morphism of sheaves of modules on `Z_étale` which is an isomorphism on the sections over
an étale geometric point `s` meeting every point of `Z` is an isomorphism.** -/
theorem isIso_of_isIso_app_etaleMk {Z : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Z) [Etale s] (hs : Function.Surjective s)
    {F G : EtaleModules.{u, r} Λ Z} (γ : F ⟶ G)
    (hγ : IsIso (γ.hom.app (op (Scheme.Etale.mk s)))) : IsIso γ := by
  let _ := preservesFilteredColimits_forget_moduleCat.{max (u + 1) r} Λ
  have hcov : ⋃ _ : PUnit.{u + 1}, Set.range s = Set.univ := by
    rw [Set.iUnion_const]
    exact Set.range_eq_univ.2 hs
  have hP : (ObjectProperty.ofObj (fun _ : PUnit.{u + 1} ↦
      (Scheme.pointSmallEtale s).ulift.{max (u + 1) r})).IsConservativeFamilyOfPoints :=
    Scheme.isConservative_pointSmallEtale_ulift (fun _ : PUnit.{u + 1} => s) hcov
  have happ : ∀ q : (ObjectProperty.ofObj (fun _ : PUnit.{u + 1} ↦
      (Scheme.pointSmallEtale s).ulift.{max (u + 1) r})).FullSubcategory,
      IsIso (q.obj.sheafFiber.map γ) := by
    rintro ⟨_, ⟨i⟩⟩
    refine (NatIso.isIso_map_iff ((Scheme.pointSmallEtale s).sheafFiberUliftNatIso
      (ModuleCat.{max (u + 1) r} Λ)) γ).mpr ?_
    exact (NatIso.isIso_map_iff (presheafFiberSelfIso s (ModuleCat.{max (u + 1) r} Λ))
      γ.hom).mp hγ
  exact (hP.jointlyReflectIsomorphisms (ModuleCat.{max (u + 1) r} Λ)).isIso γ

end Conservative

/-! ### The Frobenius of a finite field and the geometric point over `k̄` -/

section FrobeniusElement

variable {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The Frobenius of a finite field acts on every geometric fibre through the Frobenius
endomorphism of the cover. -/
theorem finiteFieldFrobenius_hom_app (z : GeometricPoint (Spec (.of k)))
    (V : FiniteEtaleOver (Spec (.of k))) :
    (finiteFieldFrobenius p q hcard z).hom.app V =
      (finiteEtaleFiberFunctor z).map (frobeniusCoverEnd p q hcard V 1) := by
  ext w
  apply Subtype.ext
  have h := finiteFieldFrobenius_pow_app_coe p q hcard z 1 V w
  rw [pow_one] at h
  exact h

/-- **Paths do not move the Frobenius of a finite field**: every isomorphism of fibre functors
commutes with the Frobenius endomorphisms of the covers. -/
theorem etaleFundamentalGroupMulEquiv_finiteFieldFrobenius {z z' : GeometricPoint (Spec (.of k))}
    (t : finiteEtaleFiberFunctor z ≅ finiteEtaleFiberFunctor z') :
    etaleFundamentalGroupMulEquiv t (finiteFieldFrobenius p q hcard z) =
      finiteFieldFrobenius p q hcard z' := by
  apply Iso.ext
  apply NatTrans.ext
  funext V
  show t.inv.app V ≫ (finiteFieldFrobenius p q hcard z).hom.app V ≫ t.hom.app V =
    (finiteFieldFrobenius p q hcard z').hom.app V
  rw [finiteFieldFrobenius_hom_app, finiteFieldFrobenius_hom_app, t.hom.naturality,
    Iso.inv_hom_id_app_assoc]

variable [CharP kbar p]

/-- The geometric point `Spec k̄ ⟶ Spec k`. -/
abbrev baseFieldGeometricPoint : GeometricPoint (Spec (.of k)) :=
  rationalGeometricPoint kbar (𝟙 (Spec (.of k)))

/-- **The inverse of the Frobenius of `k` is precomposition with `Spec(σ⁻¹)`**, `σ` the arithmetic
Frobenius of `k̄`. -/
theorem inv_finiteFieldFrobenius_hom :
    ((finiteFieldFrobenius p q hcard (baseFieldGeometricPoint kbar))⁻¹).hom =
      finiteEtaleFiberMap (galoisPointHom kbar (arithmeticFrobenius k kbar p q hcard).symm
        (𝟙 (Spec (.of k)))) := by
  set σ := finiteFieldFrobenius p q hcard (baseFieldGeometricPoint kbar)
  apply NatTrans.ext
  funext V
  ext w
  have hinv' : ∀ v, σ.inv.app V (σ.hom.app V v) = v := fun v =>
    ConcreteCategory.congr_hom (σ.app V).hom_inv_id v
  show σ.inv.app V w = (finiteEtaleFiberMap _).app V w
  rw [← hinv' ((finiteEtaleFiberMap (galoisPointHom kbar (arithmeticFrobenius k kbar p q hcard).symm
    (𝟙 (Spec (.of k))))).app V w)]
  congr 1
  apply Subtype.ext
  symm
  show (frobeniusSourceIso p q (baseFieldGeometricPoint kbar)).hom ≫
      Spec.map (CommRingCat.ofHom (arithmeticFrobenius k kbar p q hcard).symm.toAlgHom.toRingHom) ≫
        w.1 = w.1
  rw [frobeniusSourceIso_hom, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hid : (iterateFrobenius kbar p q).comp
      (arithmeticFrobenius k kbar p q hcard).symm.toAlgHom.toRingHom = RingHom.id kbar := by
    ext a
    show ((arithmeticFrobenius k kbar p q hcard).symm a) ^ p ^ q = a
    rw [← hcard, ← arithmeticFrobenius_apply k kbar p q hcard, AlgEquiv.apply_symm_apply]
  rw [hid, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

end FrobeniusElement

/-! ### The twist on the sections over the `k̄`-point -/

section Sections

/-- The identity of `Spec k` is étale. -/
instance etale_baseFieldOver_hom (k : Type u) [Field k] : Etale (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (Etale (𝟙 (Spec (.of k))))

/-- The identity is a rational point of `Spec k` over itself. -/
theorem baseFieldOver_id_comp_hom (k : Type u) [Field k] :
    𝟙 (Spec (.of k)) ≫ (Over.mk (𝟙 (Spec (.of k)))).hom = 𝟙 _ :=
  Category.comp_id _

attribute [local instance] ModuleCat.hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (U : B.Scheme) {k : Type u} [Field k] [Fintype k]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (m : ℕ) [NeZero m]
  (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)
  (z' : GeometricPoint (Spec (.of k)))
  (P : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) (EtaleFundamentalGroup (Spec (.of k))
      z'))

/-- **The Frobenius twist of `ℱ_P` on the sections over the `k̄`-point `ȳ` is the action of the
inverse of the Frobenius of `k`**: the sections of `ℱ_P|_{k̄}` over `ȳ` are `P`, carrying the twist
at `ȳ` to `Φ⁻¹`. -/
theorem exists_iso_rationalPointSections_lisseEtaleSheaf :
    ∃ W : (etaleModuleInverseImage.{u, 0} (ZMod m) (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of
        k)))) kbar) ⋙
        sheafToPresheaf _ (ModuleCat.{u + 1} (ZMod m)) ⋙
          (CategoryTheory.evaluation _ (ModuleCat.{u + 1} (ZMod m))).obj
            (op (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
              (baseFieldOver_id_comp_hom k)))).obj
          ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) z' (ZMod m)).obj P) ≅
        P.obj.obj.obj.V,
      (rationalPointFrobeniusEndo (ZMod m) (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
          (baseFieldOver_id_comp_hom k) p q hcard).app
            ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) z' (ZMod m)).obj P) ≫ W.hom =
        W.hom ≫ P.obj.obj.obj.ρ (finiteFieldFrobenius p q hcard z')⁻¹ := by
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso (Spec (.of k))
    (baseFieldGeometricPoint (k := k) kbar) z'
  have R1 : (rationalPointFrobeniusEndo (ZMod m) (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
      (baseFieldOver_id_comp_hom k) p q hcard).app
        ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) z' (ZMod m)).obj P) ≫
      ((rationalPointSectionsStalkIso (ZMod m) (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
        (baseFieldOver_id_comp_hom k)).app
          ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) z' (ZMod m)).obj P)).hom =
      ((rationalPointSectionsStalkIso (ZMod m) (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
        (baseFieldOver_id_comp_hom k)).app
          ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) z' (ZMod m)).obj P)).hom ≫
        (GrothendieckTopology.Point.Hom.sheafFiber (smallEtalePointHom (Spec (.of k))
          (galoisPointHom kbar (arithmeticFrobenius k kbar p q hcard).symm
            (𝟙 (Spec (.of k)))))).app
          ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) z' (ZMod m)).obj P) :=
    rationalPointFrobeniusEndo_comp_rationalPointSectionsStalkIso_hom (ZMod m)
      (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _) (baseFieldOver_id_comp_hom k) p q hcard
      ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) z' (ZMod m)).obj P)
  have h₂ := sheafFiber_comp_lisseEtaleSheafFiberIso_hom B (BigEtaleSite.specField B U k) z' m t
    (galoisPointHom kbar (arithmeticFrobenius k kbar p q hcard).symm (𝟙 (Spec (.of k)))) _
    (inv_finiteFieldFrobenius_hom kbar p q hcard) P
  have htr : etaleFundamentalGroupMulEquiv t
      (finiteFieldFrobenius p q hcard (baseFieldGeometricPoint (k := k) kbar))⁻¹ =
      (finiteFieldFrobenius p q hcard z')⁻¹ := by
    rw [map_inv, etaleFundamentalGroupMulEquiv_finiteFieldFrobenius]
  rw [htr] at h₂
  exact ⟨_, iso_trans_hom_comm _ _ _ _ _ R1 h₂⟩

end Sections

/-! ### Maps out of a pulled back constant sheaf over `k̄` -/

section Construction

attribute [local instance] ModuleCat.hasLimitsOfSize

variable (Λ : Type) [Ring Λ]

variable {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar]

/-- The identity of `Spec k` is an isomorphism. -/
instance isIso_baseFieldOver_hom : IsIso (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (IsIso (𝟙 (Spec (.of k))))

omit [Fintype k] in
/-- The `k̄`-point of `Spec k ×_k Spec k̄` over the identity is an isomorphism. -/
instance isIso_rationalPointBaseChangeLift_baseFieldOver :
    IsIso (rationalPointBaseChangeLift (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
      (baseFieldOver_id_comp_hom k)) := by
  have h : rationalPointBaseChangeLift (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
      (baseFieldOver_id_comp_hom k) ≫
        pullback.snd (Over.mk (𝟙 (Spec (.of k)))).hom (specAlgebraMap k kbar) = 𝟙 _ :=
    pullback.lift_snd _ _ _
  have : IsIso (rationalPointBaseChangeLift (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
      (baseFieldOver_id_comp_hom k) ≫ pullback.snd (Over.mk (𝟙 (Spec (.of k)))).hom (specAlgebraMap
          k kbar)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (pullback.snd (Over.mk (𝟙 (Spec (.of k)))).hom (specAlgebraMap
      k kbar))

/-- The `k̄`-point of `Spec k ×_k Spec k̄` over the identity is a final object of the small étale
site. -/
def isTerminalRationalPointBaseChangeObj :
    IsTerminal (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
      (baseFieldOver_id_comp_hom k)) :=
  let _ : IsIso (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
      (baseFieldOver_id_comp_hom k)).hom :=
    isIso_rationalPointBaseChangeLift_baseFieldOver kbar
  isTerminalOfIsIsoHom _

omit [Fintype k] [IsAlgClosed kbar] in
/-- The `k̄`-point of `Spec k ×_k Spec k̄` over the identity meets every point. -/
theorem surjective_rationalPointBaseChangeLift_baseFieldOver :
    Function.Surjective (rationalPointBaseChangeLift (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
      (baseFieldOver_id_comp_hom k)) := fun z =>
  ⟨(inv (rationalPointBaseChangeLift (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
      (baseFieldOver_id_comp_hom k))) z, by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl⟩

/-- **The sections over an étale geometric point of a constant sheaf are its value.** -/
theorem isIso_constantSheafSection_etaleMk {Z : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ Z) [Etale s] (M : ModuleCat.{u + 1} Λ) :
    IsIso (constantSheafSection Λ M (Scheme.Etale.mk s)) := by
  let _ := preservesFilteredColimits_forget_moduleCat.{u + 1} Λ
  let E := (presheafFiberSelfIso s (ModuleCat.{u + 1} Λ)).app
    (etaleModuleConstantSheaf Λ M Z).obj ≪≫ Sites.constantSheafFiberIso (Scheme.pointSmallEtale s) M
  have h : constantSheafSection Λ M (Scheme.Etale.mk s) ≫ E.hom = 𝟙 M := by
    ext a
    exact Sites.constantSheafFiberIso_toSheafify_app (Scheme.pointSmallEtale s) M
      (Scheme.Etale.mk s) (pointSmallEtaleSelfElement s) a
  have : IsIso (constantSheafSection Λ M (Scheme.Etale.mk s) ≫ E.hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ E.hom

/-- **Pulled back constant sections are natural in the module.** -/
theorem pulledBackConstantSection_naturality {X X' : Scheme.{u}} (g : X' ⟶ X)
    {M N : ModuleCat.{u + 1} Λ} (b : M ⟶ N) :
    pulledBackConstantSection Λ M g ≫
        ((etaleModuleInverseImage.{u, 0} Λ g).map
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map b)).hom.app
          (op ((smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 X)))) =
      b ≫ pulledBackConstantSection Λ N g := by
  have h1 : b ≫ constantSheafSection Λ N (Scheme.Etale.mk (𝟙 X)) =
      constantSheafSection Λ M (Scheme.Etale.mk (𝟙 X)) ≫
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map b).hom.app
          (op (Scheme.Etale.mk (𝟙 X))) :=
    Stacks.ConstantSheaf.toSheafify_const_naturality_app X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) b (op (Scheme.Etale.mk (𝟙 X)))
  have h2 : ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map b).hom.app
        (op (Scheme.Etale.mk (𝟙 X))) ≫
      ((etaleModuleInverseImageAdj.{u, 0} Λ g).unit.app (etaleModuleConstantSheaf Λ N X)).hom.app
        (op (Scheme.Etale.mk (𝟙 X))) =
      ((etaleModuleInverseImageAdj.{u, 0} Λ g).unit.app (etaleModuleConstantSheaf Λ M X)).hom.app
        (op (Scheme.Etale.mk (𝟙 X))) ≫
      ((etaleModuleInverseImage.{u, 0} Λ g).map
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map b)).hom.app
          (op ((smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 X)))) :=
    congrArg (fun φ => φ.hom.app (op (Scheme.Etale.mk (𝟙 X))))
      ((etaleModuleInverseImageAdj.{u, 0} Λ g).unit.naturality
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map b))
  exact (Category.assoc _ _ _).trans ((congrArg (constantSheafSection Λ M (Scheme.Etale.mk (𝟙 X)) ≫
      ·)
    h2.symm).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫
      ((etaleModuleInverseImageAdj.{u, 0} Λ g).unit.app (etaleModuleConstantSheaf Λ N X)).hom.app
        (op (Scheme.Etale.mk (𝟙 X)))) h1.symm).trans (Category.assoc _ _ _))))

end Construction

/-! ### The twisted identification over `k̄` -/

section Twist

/-- A square with an isomorphism on top: the inverse square commutes. -/
theorem inv_comp_eq_of_hom_comp {C : Type*} [Category C] {A A' : C} (W : A ≅ A') (f : A ⟶ A)
    (g : A' ⟶ A') (h : f ≫ W.hom = W.hom ≫ g) : W.inv ≫ f = g ≫ W.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- In any category, `pbcs ≫ τC ≫ X' ≫ u' = B ≫ w ≫ Gρ` given `pbcs ≫ τC = pbcs ≫ mρ`, the
commuting squares `nX`, `nu` and `nB`, and `pbcs ≫ u = w`. -/
theorem constantTwistChase {C : Type*} [Category C] {M A A' Gt G' : C} (pbcs : M ⟶ A)
    (τC mρ : A ⟶ A') (X : A ⟶ A) (X' : A' ⟶ A') (u : A ⟶ Gt) (u' : A' ⟶ G') (Gρ : Gt ⟶ G')
    (B : M ⟶ M) (w : M ⟶ Gt) (hρ : pbcs ≫ τC = pbcs ≫ mρ) (nX : mρ ≫ X' = X ≫ mρ)
    (nu : mρ ≫ u' = u ≫ Gρ) (nB : pbcs ≫ X = B ≫ pbcs) (hu : pbcs ≫ u = w) :
    pbcs ≫ τC ≫ X' ≫ u' = B ≫ w ≫ Gρ := by
  rw [← Category.assoc, hρ, Category.assoc, ← Category.assoc mρ, nX, Category.assoc, nu,
    ← Category.assoc, nB, Category.assoc, ← Category.assoc pbcs, hu]

/-- In any category, `cs ≫ iC ≫ uO = Winv` given the commuting squares `h1` and `h2`,
`pbcs ≫ u = Winv ≫ Ginv` and `Ginv ≫ Gi = 𝟙`. -/
theorem constantSectionChase {C : Type*} [Category C] {M A A' Pt GT GO : C} (cs : M ⟶ A)
    (iC : A ⟶ A') (pbcs : M ⟶ Pt) (mi : Pt ⟶ A') (u : Pt ⟶ GT) (uO : A' ⟶ GO) (Gi : GT ⟶ GO)
    (Winv : M ⟶ GO) (Ginv : GO ⟶ GT) (h1 : cs ≫ iC = pbcs ≫ mi) (h2 : mi ≫ uO = u ≫ Gi)
    (hu : pbcs ≫ u = Winv ≫ Ginv) (hinv : Ginv ≫ Gi = 𝟙 GO) : cs ≫ iC ≫ uO = Winv := by
  rw [← Category.assoc, h1, Category.assoc, h2, ← Category.assoc, hu, Category.assoc, hinv,
    Category.comp_id]

/-- **The twist relation at the final object from the twist at a fixed final object**, for a
presheaf `P` on a category with a self-map `Φ` and a twist `τ : P ⟶ Φ^* P`: if `W⁻¹` carries `B`
to the twist at `O` followed by restriction along `l : O ⟶ Φ O`, then `W⁻¹` transported to the
final object `T` carries `B` followed by restriction along `ρ : Φ T ⟶ T` to the twist at `T`. -/
theorem twist_comp_of_isTerminal {C D : Type*} [Category C] [Category D] (P : Cᵒᵖ ⥤ D)
    (Φ : C ⥤ C) (τ : P ⟶ Φ.op ⋙ P) {O T : C} (hT : IsTerminal T) (i : O ⟶ T) [IsIso i]
    (l : O ⟶ Φ.obj O) (ρ : Φ.obj T ⟶ T) [IsIso (l ≫ Φ.map i)] {M : D} (Winv : M ⟶ P.obj (op O))
    (B : M ⟶ M) (hW : Winv ≫ τ.app (op O) ≫ P.map l.op = B ≫ Winv) :
    (Winv ≫ P.map (inv i).op) ≫ τ.app (op T) = B ≫ (Winv ≫ P.map (inv i).op) ≫ P.map ρ.op := by
  have hκρ : (l ≫ Φ.map i) ≫ ρ = i := hT.hom_ext _ _
  have : IsIso (P.map (l ≫ Φ.map i).op) := inferInstance
  refine (cancel_mono (P.map (l ≫ Φ.map i).op)).1 ?_
  have nτ := τ.naturality i.op
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op] at nτ
  have hinv : P.map (inv i).op ≫ P.map i.op = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, ← op_comp, IsIso.hom_inv_id, op_id,
      CategoryTheory.Functor.map_id]
  calc ((Winv ≫ P.map (inv i).op) ≫ τ.app (op T)) ≫ P.map (l ≫ Φ.map i).op
      = Winv ≫ P.map (inv i).op ≫ (τ.app (op T) ≫ P.map (Φ.map i).op) ≫ P.map l.op := by
        simp only [op_comp, Functor.map_comp, Category.assoc]
    _ = Winv ≫ P.map (inv i).op ≫ (P.map i.op ≫ τ.app (op O)) ≫ P.map l.op := by
        rw [← nτ]
    _ = B ≫ Winv := by
        simp only [Category.assoc, reassoc_of% hinv]
        exact hW
    _ = (B ≫ (Winv ≫ P.map (inv i).op) ≫ P.map ρ.op) ≫ P.map (l ≫ Φ.map i).op := by
        simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, ← op_comp]
        rw [reassoc_of% hκρ, IsIso.hom_inv_id, op_id, CategoryTheory.Functor.map_id,
          Category.comp_id]

attribute [local instance] ModuleCat.hasLimitsOfSize

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar]
  [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **A sheaf on `Spec k` whose sections over the `k̄`-point are a module `M`, carrying the twist
to an endomorphism `B`, becomes over `k̄` the constant sheaf `M`, carrying its twist to `B`
followed by the twist of the constant sheaf.** -/
theorem exists_isIso_twist_of_rationalPointSections
    (F₀ : EtaleModules.{u, 0} Λ (Spec (.of k))) (M : ModuleCat.{u + 1} Λ) (B : M ⟶ M)
    (W : (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar) ⋙
        sheafToPresheaf _ (ModuleCat.{u + 1} Λ) ⋙
          (CategoryTheory.evaluation _ (ModuleCat.{u + 1} Λ)).obj
            (op (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
              (baseFieldOver_id_comp_hom k)))).obj F₀ ≅ M)
    (hW : (rationalPointFrobeniusEndo Λ (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
        (baseFieldOver_id_comp_hom k) p q hcard).app F₀ ≫ W.hom = W.hom ≫ B) :
    ∃ u₀ : (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
        kbar)).obj
        (etaleModuleConstantSheaf Λ M (Spec (.of k))) ⟶
      (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
          kbar)).obj F₀,
      IsIso u₀ ∧ u₀ ≫ (frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk (𝟙 (Spec (.of k)))) kbar p q
          hcard).app F₀ =
        (frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard).app
            (etaleModuleConstantSheaf Λ M (Spec (.of k))) ≫
          (etaleModuleDirectImage.{u, 0} Λ
            (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard)).map
            ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
                kbar)).map
              ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).map B)) ≫
          (etaleModuleDirectImage.{u, 0} Λ
            (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard)).map u₀ := by
  have hT : IsTerminal ((smallEtaleBaseChange (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
      kbar)).obj
      (Scheme.Etale.mk (𝟙 (Over.mk (𝟙 (Spec (.of k)))).left))) :=
    (isTerminalEtaleMkId _).isTerminalObj _
  have hO := isTerminalRationalPointBaseChangeObj (k := k) kbar
  have hΦT : IsTerminal ((smallEtaleBaseChange (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of
      k)))) kbar p
      q hcard)).obj ((smallEtaleBaseChange (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
kbar)).obj
        (Scheme.Etale.mk (𝟙 (Over.mk (𝟙 (Spec (.of k)))).left)))) := hT.isTerminalObj _
  have hi : IsIso (hT.from (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
      (baseFieldOver_id_comp_hom k))) := ⟨⟨hO.from _, hO.hom_ext _ _, hT.hom_ext _ _⟩⟩
  have : IsIso (rationalPointFrobeniusLift (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
      (baseFieldOver_id_comp_hom k) p q hcard ≫
        (smallEtaleBaseChange (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of k)))) kbar p q
            hcard)).map
          (hT.from (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
            (baseFieldOver_id_comp_hom k)))) := ⟨⟨hO.from _, hO.hom_ext _ _, hΦT.hom_ext _ _⟩⟩
  obtain ⟨ρ, hρ⟩ := exists_pulledBackConstantSection_comp_frobeniusBaseChangeTwist Λ M
    (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard
  let adj := (constantSheafAdj (Over.mk (𝟙 (Spec (.of k)))).left.smallEtaleTopology (ModuleCat.{u +
      1} Λ)
    (isTerminalEtaleMkId (Over.mk (𝟙 (Spec (.of k)))).left)).comp
      (etaleModuleInverseImageAdj.{u, 0} Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar))
  let u₀ := (adj.homEquiv M ((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj F₀)).symm
    (W.inv ≫ ((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj F₀).obj.map
        (inv (hT.from (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
          (baseFieldOver_id_comp_hom k)))).op)
  have hu : pulledBackConstantSection Λ M (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar) ≫
      u₀.hom.app (op ((smallEtaleBaseChange (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
          kbar)).obj
        (Scheme.Etale.mk (𝟙 (Over.mk (𝟙 (Spec (.of k)))).left)))) =
      W.inv ≫ ((etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj F₀).obj.map
          (inv (hT.from (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
            (baseFieldOver_id_comp_hom k)))).op := by
    have h := (adj.homEquiv M ((etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj F₀)).apply_symm_apply
        (W.inv ≫ ((etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj F₀).obj.map
            (inv (hT.from (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
              (baseFieldOver_id_comp_hom k)))).op)
    simp only [adj, Adjunction.homEquiv_unit, Adjunction.comp_unit_app,
      Stacks.ConstantSheaf.constantSheafAdj_unit_app] at h
    exact (Category.assoc _ _ _).trans h
  refine ⟨u₀, ?_, ?_⟩
  · have : IsIso ((inverseImageEtaleModuleConstantSheafIso Λ M
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).inv ≫ u₀) := by
      refine isIso_of_isIso_app_etaleMk Λ (rationalPointBaseChangeLift (Over.mk (𝟙 (Spec (.of k))))
          kbar (𝟙 _)
        (baseFieldOver_id_comp_hom k)) (surjective_rationalPointBaseChangeLift_baseFieldOver kbar)
        _ ?_
      have := isIso_constantSheafSection_etaleMk Λ (rationalPointBaseChangeLift (Over.mk (𝟙 (Spec
          (.of k))))
        kbar (𝟙 _) (baseFieldOver_id_comp_hom k)) M
      have hc := constantSectionChase _ _ _ _ _ _ _ _ _
        (constantSheafSection_comp_inverseImageConstantIso_inv Λ M
          (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)
          (hT.from (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
            (baseFieldOver_id_comp_hom k))))
        (u₀.hom.naturality (hT.from (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar
            (𝟙 _)
            (baseFieldOver_id_comp_hom k))).op) hu (by
              rw [← CategoryTheory.Functor.map_comp, ← op_comp, IsIso.hom_inv_id, op_id,
                CategoryTheory.Functor.map_id])
      have : IsIso (constantSheafSection Λ M (Scheme.Etale.mk
          (rationalPointBaseChangeLift (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
              (baseFieldOver_id_comp_hom k))) ≫
          ((inverseImageEtaleModuleConstantSheafIso Λ M
              (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).inv ≫
            u₀).hom.app (op (Scheme.Etale.mk (rationalPointBaseChangeLift (Over.mk (𝟙 (Spec (.of
                k)))) kbar
              (𝟙 _) (baseFieldOver_id_comp_hom k))))) := by
        have e : constantSheafSection Λ M (Scheme.Etale.mk
            (rationalPointBaseChangeLift (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
              (baseFieldOver_id_comp_hom k))) ≫
            ((inverseImageEtaleModuleConstantSheafIso Λ M
                (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).inv ≫
              u₀).hom.app (op (Scheme.Etale.mk (rationalPointBaseChangeLift (Over.mk (𝟙 (Spec (.of
                  k)))) kbar
                (𝟙 _) (baseFieldOver_id_comp_hom k)))) = W.inv := hc
        rw [e]
        infer_instance
      exact IsIso.of_isIso_comp_left (constantSheafSection Λ M (Scheme.Etale.mk
        (rationalPointBaseChangeLift (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
            (baseFieldOver_id_comp_hom k)))) _
    exact IsIso.of_isIso_comp_left (inverseImageEtaleModuleConstantSheafIso Λ M
      (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).inv u₀
  · apply hom_ext_inverseImage_constant Λ M (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)
    have hW' := inv_comp_eq_of_hom_comp W _ B hW
    have key2 := twist_comp_of_isTerminal ((etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj F₀).obj
      (smallEtaleBaseChange (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of k)))) kbar p q
          hcard))
      ((frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard).app F₀).hom
          hT
      (hT.from (rationalPointBaseChangeObj (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
        (baseFieldOver_id_comp_hom k)))
      (rationalPointFrobeniusLift (Over.mk (𝟙 (Spec (.of k)))) kbar (𝟙 _)
          (baseFieldOver_id_comp_hom k) p q
        hcard) ρ W.inv B hW'
    have key := constantTwistChase _ _ _ _ _ _ _ _ B _ hρ
      (((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
          kbar)).map
        ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
            B)).hom.naturality
          ρ.op)
      (u₀.hom.naturality ρ.op)
      (pulledBackConstantSection_naturality Λ (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k))))
          kbar) B) hu
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hu).trans
      (key2.trans (key.symm.trans (Category.assoc _ _ _))))

end Twist

/-! ### The lisse sheaf of the descended module -/

section Lisse

variable (B : BigEtaleSite.{u}) (U : B.Scheme) [ConnectedSpace U.1] {k : Type u} [Field k]
  [Fintype k] (f : U.1 ⟶ Spec (.of k)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosed kbar] (m : ℕ) [NeZero m] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q) (x : GeometricPoint U.1)
  (hs : Function.Surjective (etaleFundamentalGroupMap f x))
  (Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) (EtaleFundamentalGroup U.1 x))
  (hQ : ∀ g, etaleFundamentalGroupMap f x g = 1 → Q.obj.obj.obj.ρ g = 1)

/-- **Over `k̄` the lisse sheaf `ℱ_{Q₀}` of the descended module is the constant sheaf `Q`,
carrying its Frobenius twist to the action of a lift `φ` of the inverse of the Frobenius of `k`
followed by the twist of the constant sheaf.** -/
theorem exists_isIso_twist_lisseEtaleSheaf_baseField (φ : EtaleFundamentalGroup U.1 x)
    (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p q hcard (x.map f))⁻¹) :
    ∃ (u₀ : (etaleModuleInverseImage.{u, 0} (ZMod m)
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj
          (etaleModuleConstantSheaf (ZMod m) Q.obj.obj.obj.V (Spec (.of k))) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod m)
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj
        ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) (x.map f) (ZMod m)).obj
          (lisseBaseFieldModule B U k f x hs (ZMod m) Q hQ))), IsIso u₀ ∧
      u₀ ≫ (frobeniusBaseChangeTwist.{u, 0} (ZMod m) (Over.mk (𝟙 (Spec (.of k)))) kbar p q
          hcard).app ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) (x.map f) (ZMod m)).obj
            (lisseBaseFieldModule B U k f x hs (ZMod m) Q hQ)) =
      (frobeniusBaseChangeTwist.{u, 0} (ZMod m) (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard).app
          (etaleModuleConstantSheaf (ZMod m) Q.obj.obj.obj.V (Spec (.of k))) ≫
        (etaleModuleDirectImage.{u, 0} (ZMod m)
          (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard)).map
          ((etaleModuleInverseImage.{u, 0} (ZMod m)
            (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).map
            ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod m))).map
              (Q.obj.obj.obj.ρ φ))) ≫
        (etaleModuleDirectImage.{u, 0} (ZMod m)
          (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard)).map u₀ := by
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  obtain ⟨W, hW⟩ := exists_iso_rationalPointSections_lisseEtaleSheaf B U kbar m p q hcard
    (x.map f) (lisseBaseFieldModule B U k f x hs (ZMod m) Q hQ)
  have hB : (lisseBaseFieldModule B U k f x hs (ZMod m) Q hQ).obj.obj.obj.ρ
      (finiteFieldFrobenius p q hcard (x.map f))⁻¹ = Q.obj.obj.obj.ρ φ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun v => ?_)
    rw [← hφ]
    exact lisseBaseFieldModule_ρ_apply B U k f x hs (ZMod m) Q hQ φ v
  rw [hB] at hW
  exact exists_isIso_twist_of_rationalPointSections (ZMod m) kbar p q hcard _ _ _ W hW

end Lisse

end Stacks.EtaleCohomology

end
