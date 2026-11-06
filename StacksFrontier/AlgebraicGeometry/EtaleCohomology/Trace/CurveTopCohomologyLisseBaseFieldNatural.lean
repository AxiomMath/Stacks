module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyLisseBaseField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyBaseFieldTwistNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologySmoothCompactificationNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseSheafPullbackNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseBaseFieldTwistNatural

/-!
# `H²_c` of a lisse sheaf with trivial geometric monodromy on a curve, naturally

For `Q` a finite `ℤ/m`-module with a continuous action of `π₁(U, x̄)` on which `π₁(U_k̄)` acts
trivially, the isomorphism `H²_c(U_k̄, ℱ_Q) ≅ Q` with `π_U^* = q · φ` of
`Stacks.EtaleCohomology.exists_addEquiv_compactSupportSheafCohomology_two_lisseEtaleSheaf_of_twist`
can be chosen natural in `Q`, once the identification `u₀` over `k̄` is.

## Main results

* `Stacks.EtaleCohomology.etaleModuleInverseImage_map_comp_eqToHom`: inverse image along equal
  morphisms commutes with the induced maps.
* `Stacks.EtaleCohomology.iso_inv_comp_chase`: a square through an isomorphism factored in two
  steps.
* `exists_addEquiv_compactSupportSheafCohomology_two_lisseEtaleSheaf_of_twist_natural`:
  `H²_c(U_k̄, ℱ_Q) ≅ Q` with `π_U^* = q · φ`, naturally in `Q`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (U : B.Scheme) [ConnectedSpace U.1] {k : Type u} [Field k]
  [Fintype k] (f : U.1 ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f)) (kbar : Type u)
  [Field kbar] [Algebra k kbar] [IsAlgClosed kbar] (m : ℕ) [NeZero m] (p q : ℕ) [Fact p.Prime]
  [CharP k p] (hcard : Fintype.card k = p ^ q) (x : GeometricPoint U.1)
  (hs : Function.Surjective (etaleFundamentalGroupMap f x))
  (Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) (EtaleFundamentalGroup U.1 x))
  (hQ : ∀ g, etaleFundamentalGroupMap f x g = 1 → Q.obj.obj.obj.ρ g = 1)

/-- Inverse image along equal morphisms commutes with the induced maps. -/
theorem etaleModuleInverseImage_map_comp_eqToHom (Λ : Type) [CommRing Λ] {Y Z : Scheme.{u}}
    {g g' : Y ⟶ Z} (h : g = g') {F G : EtaleModules.{u, 0} Λ Z} (s : F ⟶ G) :
    (etaleModuleInverseImage.{u, 0} Λ g).map s ≫
        eqToHom (congrArg (fun g => (etaleModuleInverseImage.{u, 0} Λ g).obj G) h) =
      eqToHom (congrArg (fun g => (etaleModuleInverseImage.{u, 0} Λ g).obj F) h) ≫
        (etaleModuleInverseImage.{u, 0} Λ g').map s := by
  subst h
  simp

/-- A square through an isomorphism factored in two steps, in an arbitrary category. -/
theorem iso_inv_comp_chase {𝒞 : Type*} [Category 𝒞] {A M D : 𝒞} (ι : A ≅ D) (a₂ : A ⟶ M)
    (a₁ : M ⟶ D) (hι : ι.hom = a₂ ≫ a₁) (x : D ⟶ D) (y : M ⟶ M) (z : A ⟶ A)
    (h₁ : y ≫ a₁ = a₁ ≫ x) (h₂ : a₂ ≫ y = z ≫ a₂) : x ≫ ι.inv = ι.inv ≫ z := by
  rw [Iso.eq_inv_comp]
  have h : ι.hom ≫ ι.inv = 𝟙 A := ι.hom_inv_id
  rw [hι] at h ⊢
  simp only [Category.assoc] at h ⊢
  rw [← reassoc_of% h₁, reassoc_of% h₂, h, Category.comp_id]

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
include hcard in
/-- **`H²_c(U_k̄, ℱ_Q) ≅ Q` with `π_U^* = q · φ`, naturally in `Q`**, for `Q` with trivial
geometric monodromy, given the identification over `k̄` of the descended sheaf `ℱ_{Q₀}` on
`Spec k` with the constant sheaf `Q`, carrying its Frobenius twist to the action of `φ` followed
by the twist of `Q`. -/
theorem exists_addEquiv_compactSupportSheafCohomology_two_lisseEtaleSheaf_of_twist_natural
    (hm : IsUnit (m : kbar)) (hgi : GeometricallyIrreducible f) (φ : EtaleFundamentalGroup U.1 x)
    (u₀ : (etaleModuleInverseImage.{u, 0} (ZMod m)
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj
          (etaleModuleConstantSheaf (ZMod m) Q.obj.obj.obj.V (Spec (.of k))) ⟶
      (etaleModuleInverseImage.{u, 0} (ZMod m)
        (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).obj
        ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) (x.map f) (ZMod m)).obj
          (lisseBaseFieldModule B U k f x hs (ZMod m) Q hQ))) [IsIso u₀]
    (h₀ : u₀ ≫ (frobeniusBaseChangeTwist.{u, 0} (ZMod m) (Over.mk (𝟙 (Spec (.of k)))) kbar p q
          hcard).app ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) (x.map f) (ZMod m)).obj
            (lisseBaseFieldModule B U k f x hs (ZMod m) Q hQ)) =
      (frobeniusBaseChangeTwist.{u, 0} (ZMod m) (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard).app
          (etaleModuleConstantSheaf (ZMod m) Q.obj.obj.obj.V (Spec (.of k))) ≫
        (etaleModuleDirectImage.{u, 0} (ZMod m)
          (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard)).map
          ((etaleModuleInverseImage.{u, 0} (ZMod m)
            (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).map
            ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod m))).map
              (Q.obj.obj.obj.ρ φ).asHom)) ≫
        (etaleModuleDirectImage.{u, 0} (ZMod m)
          (geometricFrobeniusBaseChange (Over.mk (𝟙 (Spec (.of k)))) kbar p q hcard)).map u₀)
    (hu₀ : ∀ g : Q ⟶ Q,
      (etaleModuleInverseImage.{u, 0} (ZMod m)
          (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).map
          ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod m))).map
            g.hom.hom.hom.hom) ≫ u₀ =
        u₀ ≫ (etaleModuleInverseImage.{u, 0} (ZMod m)
          (fieldBaseChangeProj (Over.mk (𝟙 (Spec (.of k)))) kbar)).map
          ((lisseEtaleSheaf B (BigEtaleSite.specField B U k) (x.map f) (ZMod m)).map
            (lisseBaseFieldModuleMap B U f m x hs Q hQ g))) :
    ∃ θ : (compactSupportSheafCohomology (ZMod m) f j kbar 2).obj
        ((lisseEtaleSheaf B U x (ZMod m)).obj Q) ≃+ Q.obj.obj.obj.V,
      (∀ t, θ (((compactSupportSheafFrobenius (ZMod m) f j kbar p q hcard 2).app
          ((lisseEtaleSheaf B U x (ZMod m)).obj Q)).hom t) =
        (p ^ q : ℕ) • (Q.obj.obj.obj.ρ φ).asHom.hom (θ t)) ∧
      ∀ (g : Q ⟶ Q) t, θ (((compactSupportSheafCohomology (ZMod m) f j kbar 2).map
          ((lisseEtaleSheaf B U x (ZMod m)).map g)).hom t) = g.hom.hom.hom.hom.hom (θ t) := by
  have : Finite Q.obj.obj.obj.V := (moduleCat_isFG_iff_finite (ZMod m) _).1 Q.property
  let F₀ := (lisseEtaleSheaf B (BigEtaleSite.specField B U k) (x.map f) (ZMod m)).obj
    (lisseBaseFieldModule B U k f x hs (ZMod m) Q hQ)
  let T := compactSupportSheafCohomology (ZMod m) f j kbar 2
  let π := compactSupportSheafFrobenius (ZMod m) f j kbar p q hcard 2
  have := compactSpace_etaleFundamentalGroup U.1 x
  have := t2Space_etaleFundamentalGroup (Spec (.of k)) (x.map f)
  obtain ⟨αN⟩ := nonempty_finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite_pullbackIso B
    (BigEtaleSite.specFieldHom B U k f) (ZMod m) x
  let α₁ : (etaleModuleInverseImage.{u, 0} (ZMod m) f).obj F₀ ≅
      (lisseEtaleSheaf B U x (ZMod m)).obj Q :=
    etaleModuleInverseImageLisseEtaleSheafIso B (BigEtaleSite.specFieldHom B U k f) x (ZMod m) αN
        (lisseBaseFieldModule B U k f x hs (ZMod m) Q hQ) ≪≫
      (lisseEtaleSheaf B U x (ZMod m)).mapIso
        (finiteTypeContinuousModuleDescentResIso (ZMod m) (etaleFundamentalGroupMap f x) hs Q hQ)
  obtain ⟨C⟩ := nonempty_coverCompactification k f j.toBase j.immersion
    (CompactificationOf.immersion_toBase j) (𝟙 U.1)
  have hjq : C.j ≫ C.q = f :=
    (C.j_comp_q f (CompactificationOf.immersion_toBase j)).trans (Category.id_comp f)
  have : GeometricallyIrreducible (C.j ≫ C.q) := by rw [hjq]; exact hgi
  have := C.isCurve_fieldBaseChange kbar inferInstance
  have := C.smooth_fieldBaseChange kbar
  have := C.isProper_fieldBaseChange kbar
  let α₂ : (etaleModuleRestriction.{u, 0} (ZMod m) C.j).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod m) C.q).obj F₀) ≅
      (etaleModuleInverseImage.{u, 0} (ZMod m) f).obj F₀ :=
    (etaleModuleInverseImageRestrictionIso (ZMod m) C.j).symm.app _ ≪≫
      (etaleModuleInverseImageCompIso (ZMod m) C.j C.q).symm.app F₀ ≪≫
      eqToIso (congrArg (fun g => (etaleModuleInverseImage.{u, 0} (ZMod m) g).obj F₀) hjq)
  obtain ⟨e₃, he₃, hn₃⟩ :=
    exists_linearEquiv_compactSupportSheafCohomology_two_coverCompactification_natural f j kbar m p
      q hcard C ((etaleModuleInverseImage.{u, 0} (ZMod m) C.q).obj F₀)
  obtain ⟨e₄, he₄, hn₄⟩ :=
    exists_addEquiv_compactSupportSheafCohomology_two_inverseImage_of_twist_natural C.q kbar m p q
      hcard hm F₀ Q.obj.obj.obj.V (Q.obj.obj.obj.ρ φ).asHom u₀ h₀
  let ι := α₂ ≪≫ α₁
  let e₁ : T.obj ((lisseEtaleSheaf B U x (ZMod m)).obj Q) ≃+
      T.obj ((etaleModuleRestriction.{u, 0} (ZMod m) C.j).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod m) C.q).obj F₀)) :=
    (T.mapIso ι).symm.toLinearEquiv.toAddEquiv
  refine ⟨(e₁.trans e₃.toAddEquiv).trans e₄, fun t => ?_, fun g t => ?_⟩
  swap
  · let s₀ := (lisseEtaleSheaf B (BigEtaleSite.specField B U k) (x.map f) (ZMod m)).map
      (lisseBaseFieldModuleMap B U f m x hs Q hQ g)
    let R := (etaleModuleRestriction.{u, 0} (ZMod m) C.j).map
      ((etaleModuleInverseImage.{u, 0} (ZMod m) C.q).map s₀)
    have hα₂ : ∀ s₀ : F₀ ⟶ F₀, α₂.hom ≫ (etaleModuleInverseImage.{u, 0} (ZMod m) f).map s₀ =
        (etaleModuleRestriction.{u, 0} (ZMod m) C.j).map
          ((etaleModuleInverseImage.{u, 0} (ZMod m) C.q).map s₀) ≫ α₂.hom := by
      intro s₀
      have n1 := (etaleModuleInverseImageRestrictionIso (ZMod m) C.j).inv.naturality
        ((etaleModuleInverseImage.{u, 0} (ZMod m) C.q).map s₀)
      have n2 : (etaleModuleInverseImage.{u, 0} (ZMod m) C.j).map
            ((etaleModuleInverseImage.{u, 0} (ZMod m) C.q).map s₀) ≫
          (etaleModuleInverseImageCompIso (ZMod m) C.j C.q).inv.app F₀ =
          (etaleModuleInverseImageCompIso (ZMod m) C.j C.q).inv.app F₀ ≫
            (etaleModuleInverseImage.{u, 0} (ZMod m) (C.j ≫ C.q)).map s₀ :=
        (etaleModuleInverseImageCompIso (ZMod m) C.j C.q).inv.naturality s₀
      have n3 := etaleModuleInverseImage_map_comp_eqToHom (ZMod m) hjq s₀
      simp only [α₂, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, eqToIso.hom, Category.assoc]
      rw [← n3, ← reassoc_of% n2, ← reassoc_of% n1]
    have p1 := etaleModuleInverseImageLisseEtaleSheafIso_hom_naturality B
      (BigEtaleSite.specFieldHom B U k f) x (ZMod m) αN
      (lisseBaseFieldModuleMap B U f m x hs Q hQ g)
    have p2 : (finiteTypeContinuousModuleRes (ZMod m) (etaleFundamentalGroupMap f x)).map
          (lisseBaseFieldModuleMap B U f m x hs Q hQ g) ≫
        (finiteTypeContinuousModuleDescentResIso (ZMod m) (etaleFundamentalGroupMap f x) hs Q
          hQ).hom =
        (finiteTypeContinuousModuleDescentResIso (ZMod m) (etaleFundamentalGroupMap f x) hs Q
          hQ).hom ≫ g := by
      ext
      rfl
    have hα₁ : (etaleModuleInverseImage.{u, 0} (ZMod m) f).map s₀ ≫ α₁.hom =
        α₁.hom ≫ (lisseEtaleSheaf B U x (ZMod m)).map g :=
      iso_comp_map_chase (lisseEtaleSheaf B U x (ZMod m)) _ _ _ _ _ _ _ p1 p2
    have hι : (lisseEtaleSheaf B U x (ZMod m)).map g ≫ ι.inv = ι.inv ≫ R :=
      iso_inv_comp_chase ι α₂.hom α₁.hom rfl _ _ _ hα₁ (hα₂ s₀)
    have he₁ : e₁ ((T.map ((lisseEtaleSheaf B U x (ZMod m)).map g)).hom t) = (T.map R).hom (e₁ t) :=
      congrArg (fun φ => φ.hom t)
        ((T.map_comp _ _).symm.trans ((congrArg T.map hι).trans (T.map_comp _ _)))
    exact (congrArg (fun z => e₄ (e₃ z)) he₁).trans
      ((congrArg e₄ (hn₃ ((etaleModuleInverseImage.{u, 0} (ZMod m) C.q).map s₀) (e₁ t))).trans
        (hn₄ g.hom.hom.hom.hom s₀ (hu₀ g) (e₃ (e₁ t))))
  have hnat : e₁ ((π.app _).hom t) = (π.app _).hom (e₁ t) :=
    congrArg (fun φ => φ.hom t) (π.naturality ι.inv).symm
  simp only [AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv]
  rw [hnat]
  exact (congrArg e₄ (he₃ (e₁ t))).trans (he₄ _)

end Stacks.EtaleCohomology

end
