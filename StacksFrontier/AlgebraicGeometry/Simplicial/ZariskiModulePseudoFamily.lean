module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiCartesianModuleFaces
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialPseudoFamily

/-!
# The pseudofunctorial family of modules on the degrees of a simplicial scheme

Let `X` be a simplicial scheme. The categories of sheaves of modules on the schemes `X_n`, the
pullbacks `(X φ)^*` along the scheme morphisms of `X`, the compositor
`(X φ)^* (X ψ)^* ≅ (X (ψ ≫ φ))^*` and the identification `(X 𝟙)^* ≅ 𝟭` form a
`CategoryTheory.SimplicialPseudoFamily`. The compositor and the unit are those of Mathlib's
pseudofunctor of modules on schemes, read through the equalities `X.map_comp` and `X.map_id`,
and the three laws of the family are its associativity and unit laws.

A cartesian sheaf of `𝒪_X`-modules on the total Zariski site of `X`, with its components and
its transitions, is a cartesian system of this family.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.pullbackPasteOfEq`: the compositor
  `f^* g^* M ≅ k^* M` attached to a factorization `f ≫ g = k` of a morphism of schemes.
* `AlgebraicGeometry.SimplicialScheme.zariskiModuleFamily`: the family.
* `AlgebraicGeometry.SimplicialScheme.cartesianModuleSystem`: the cartesian system of a cartesian
  module on the total Zariski site.

## Main results

* `AlgebraicGeometry.SimplicialScheme.homEquiv_symm_pushforwardComp`: the transpose of a
  composite of two maps into direct images is the composite of the two transposes, preceded by
  the inverse of the compositor of pullbacks.
* `AlgebraicGeometry.SimplicialScheme.componentModuleTransition_naturality`: the transition of
  Stacks 09WF is natural in the module.

## References

* [Stacks Project, Tag 07TH](https://stacks.math.columbia.edu/tag/07TH)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SimplicialScheme

/-! ### The compositor of pullbacks at a factorization -/

section Compositor

variable {A B C D : Scheme.{u}}

/-- The compositor `f^* g^* M ≅ k^* M` of pullbacks of modules attached to a factorization
`f ≫ g = k`. -/
noncomputable def pullbackPasteOfEq (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f ≫ g = k)
    (M : C.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ≅
      (Scheme.Modules.pullback k).obj M :=
  (Scheme.Modules.pullbackComp f g).app M ≪≫ (Scheme.Modules.pullbackCongr h).app M

/-- The compositor at a factorization is natural in the module. -/
theorem pullbackPasteOfEq_naturality (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f ≫ g = k)
    {M N : C.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map φ) ≫
        (pullbackPasteOfEq f g k h N).hom =
      (pullbackPasteOfEq f g k h M).hom ≫ (Scheme.Modules.pullback k).map φ := by
  subst h
  simp only [pullbackPasteOfEq, Iso.trans_hom, Iso.app_hom, Scheme.Modules.pullbackCongr,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
  exact (Scheme.Modules.pullbackComp f g).hom.naturality φ

/-- The associativity law for the compositor at factorizations. -/
theorem pullbackPasteOfEq_assoc (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (ab : A ⟶ C)
    (hab : a ≫ b = ab) (bc : B ⟶ D) (hbc : b ≫ c = bc) (abc₁ : A ⟶ D) (h₁ : ab ≫ c = abc₁)
    (abc₂ : A ⟶ D) (h₂ : a ≫ bc = abc₂) (e : abc₂ = abc₁) (M : D.Modules) :
    (pullbackPasteOfEq a b ab hab ((Scheme.Modules.pullback c).obj M)).hom ≫
        (pullbackPasteOfEq ab c abc₁ h₁ M).hom =
      (Scheme.Modules.pullback a).map (pullbackPasteOfEq b c bc hbc M).hom ≫
        (pullbackPasteOfEq a bc abc₂ h₂ M).hom ≫
          eqToHom (congrArg (fun t => (Scheme.Modules.pullback t).obj M) e) := by
  subst hab hbc h₁ h₂
  have h := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity a b c) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_app] at h
  simp only [pullbackPasteOfEq, Iso.trans_hom, Iso.app_hom, Scheme.Modules.pullbackCongr,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id]
  have h' : (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback c).obj M) ≫
      (Scheme.Modules.pullbackComp (a ≫ b) c).hom.app M =
      (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c).hom.app M) ≫
        (Scheme.Modules.pullbackComp a (b ≫ c)).hom.app M ≫
          ((Scheme.Modules.pullbackComp a (b ≫ c)).inv.app M ≫
            (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b c).inv.app M) ≫
            (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback c).obj M) ≫
              (Scheme.Modules.pullbackComp (a ≫ b) c).hom.app M) := by
    simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [h', h]

/-- The right unit law for the compositor at factorizations: a factorization through a morphism
equal to the identity of the target. -/
theorem pullbackPasteOfEq_comp_id (f : A ⟶ B) (e : A ⟶ A) (he : e = 𝟙 A) (k : A ⟶ B)
    (h : e ≫ f = k) (hk : k = f) (M : B.Modules) :
    (pullbackPasteOfEq e f k h M).hom ≫
        eqToHom (congrArg (fun t => (Scheme.Modules.pullback t).obj M) hk) =
      (Scheme.Modules.pullbackCongr he).hom.app ((Scheme.Modules.pullback f).obj M) ≫
        (Scheme.Modules.pullbackId A).hom.app ((Scheme.Modules.pullback f).obj M) := by
  subst he h
  have h := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality f) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_app] at h
  simp only [pullbackPasteOfEq, Iso.trans_hom, Iso.app_hom, Scheme.Modules.pullbackCongr,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id, Category.id_comp]
  rw [← cancel_epi ((Scheme.Modules.pullbackComp (𝟙 A) f).inv.app M),
    Iso.inv_hom_id_app_assoc]
  simpa using h.symm

/-- The left unit law for the compositor at factorizations: a factorization through a morphism
equal to the identity of the source of the second factor. -/
theorem pullbackPasteOfEq_id_comp (f : A ⟶ B) (e : B ⟶ B) (he : e = 𝟙 B) (k : A ⟶ B)
    (h : f ≫ e = k) (hk : k = f) (M : B.Modules) :
    (pullbackPasteOfEq f e k h M).hom ≫
        eqToHom (congrArg (fun t => (Scheme.Modules.pullback t).obj M) hk) =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackCongr he).hom.app M ≫
        (Scheme.Modules.pullbackId B).hom.app M) := by
  subst he h
  have h := NatTrans.congr_app (Scheme.Modules.pseudofunctor_left_unitality f) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    eqToHom_app] at h
  simp only [pullbackPasteOfEq, Iso.trans_hom, Iso.app_hom, Scheme.Modules.pullbackCongr,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id, Category.id_comp]
  rw [← cancel_epi ((Scheme.Modules.pullbackComp f (𝟙 B)).inv.app M),
    Iso.inv_hom_id_app_assoc]
  simpa using h.symm

end Compositor

/-! ### The family -/

variable (X : SimplicialObject Scheme.{u})

/-- The composite of the morphisms of a simplicial scheme attached to two simplex maps is the
morphism attached to their composite. -/
theorem map_op_comp_map_op {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    X.map φ.op ≫ X.map ψ.op = X.map (ψ ≫ φ).op := by
  rw [op_comp, X.map_comp]

/-- **The pseudofunctorial family of modules on the degrees of a simplicial scheme.** In degree
`n` it is the category of sheaves of modules on `X_n`, the functor attached to a simplex map `φ`
is the pullback along `X φ`, and the compositor and the unit are those of the pullback of
modules on schemes, read through `X.map_comp` and `X.map_id`. -/
noncomputable abbrev zariskiModuleFamily : SimplicialPseudoFamily.{u, u + 1} where
  obj n := (X.obj (op n)).Modules
  map φ := Scheme.Modules.pullback (X.map φ.op)
  paste ψ φ M := pullbackPasteOfEq (X.map φ.op) (X.map ψ.op) (X.map (ψ ≫ φ).op)
    (map_op_comp_map_op X ψ φ) M
  paste_naturality ψ φ _ _ f := pullbackPasteOfEq_naturality _ _ _ _ f
  unit n M := (Scheme.Modules.pullbackCongr (X.map_id (op n))).app M ≪≫
    (Scheme.Modules.pullbackId _).app M
  unit_naturality n _ _ f := by
    simp only [Iso.trans_hom, Iso.app_hom, Category.assoc]
    exact ((Scheme.Modules.pullbackCongr (X.map_id (op n))).hom.naturality_assoc f _).trans
      (congrArg (fun t => _ ≫ t) ((Scheme.Modules.pullbackId _).hom.naturality f))
  paste_assoc χ ψ φ M := by
    have := pullbackPasteOfEq_assoc (X.map φ.op) (X.map ψ.op) (X.map χ.op)
      (X.map (ψ ≫ φ).op) (map_op_comp_map_op X ψ φ) (X.map (χ ≫ ψ).op)
      (map_op_comp_map_op X χ ψ) (X.map (χ ≫ ψ ≫ φ).op)
      (map_op_comp_map_op X χ (ψ ≫ φ)) (X.map ((χ ≫ ψ) ≫ φ).op)
      (map_op_comp_map_op X (χ ≫ ψ) φ) (by rw [Category.assoc]) M
    exact this
  paste_comp_id φ M := pullbackPasteOfEq_comp_id _ _ (X.map_id _) _ _
    (by rw [Category.comp_id]) M
  paste_id_comp φ M := pullbackPasteOfEq_id_comp _ _ (X.map_id _) _ _
    (by rw [Category.id_comp]) M

/-! ### Transposes of composites of maps into direct images -/

section Mates

variable {A B C : Scheme.{u}}

/-- The identifications of direct images along a reflexive equality are identities. -/
private theorem pushforwardCongr_rfl_app (f : A ⟶ B) (N : A.Modules) :
    (Scheme.Modules.pushforwardCongr (rfl : f = f)).hom.app N = 𝟙 _ ∧
      (Scheme.Modules.pushforwardCongr (rfl : f = f)).inv.app N = 𝟙 _ := by
  have hself : ∀ {V : A.Opens} (e : V = V), N.presheaf.map (eqToHom e).op = 𝟙 _ := by
    intro V e
    obtain rfl : e = rfl := Subsingleton.elim _ _
    simp
  exact ⟨Scheme.Modules.hom_ext _ _ fun U =>
      (Scheme.Modules.pushforwardCongr_hom_app_app _ U).trans ((hself _).trans (by simp)),
    Scheme.Modules.hom_ext _ _ fun U =>
      (Scheme.Modules.pushforwardCongr_inv_app_app _ U).trans ((hself _).trans (by simp))⟩

/-- **The transpose of a composite of maps into direct images.** For `u : M ⟶ g_* N'` and
`v : N' ⟶ f_* N`, the transpose of `u ≫ g_* v`, read into `(f ≫ g)_* N` through the compositor
of direct images, is the inverse compositor of pullbacks followed by `f^*` of the transpose of
`u` and the transpose of `v`. -/
theorem homEquiv_symm_pushforwardComp (f : A ⟶ B) (g : B ⟶ C) {M : C.Modules}
    {N' : B.Modules} {N : A.Modules} (u : M ⟶ (Scheme.Modules.pushforward g).obj N')
    (v : N' ⟶ (Scheme.Modules.pushforward f).obj N) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv M N).symm
        ((u ≫ (Scheme.Modules.pushforward g).map v) ≫
          (Scheme.Modules.pushforwardComp f g).hom.app N) =
      (Scheme.Modules.pullbackComp f g).inv.app M ≫
        (Scheme.Modules.pullback f).map
          (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm u) ≫
          ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm v := by
  generalize hu' : ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm u = uh
  generalize hv' : ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm v = vh
  obtain rfl : u = (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _ uh := by
    rw [← hu', Equiv.apply_symm_apply]
  obtain rfl : v = (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ vh := by
    rw [← hv', Equiv.apply_symm_apply]
  have key := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at key
  rw [Equiv.symm_apply_eq]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% key, ← (Scheme.Modules.pushforwardComp f g).hom.naturality_assoc,
    ← (Scheme.Modules.pushforwardComp f g).hom.naturality]
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Category.assoc, Functor.comp_obj]
  congr 1
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  congr 2
  rw [Functor.map_comp, ← Category.assoc, ← Category.assoc]
  congr 1
  exact ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality uh)

/-- `homEquiv_symm_pushforwardComp`, with the composite of the two morphisms of schemes
presented as an equal morphism. -/
theorem homEquiv_symm_pushforwardComp_congr (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C)
    (h : f ≫ g = k) {M : C.Modules} {N' : B.Modules} {N : A.Modules}
    (u : M ⟶ (Scheme.Modules.pushforward g).obj N')
    (v : N' ⟶ (Scheme.Modules.pushforward f).obj N) :
    ((Scheme.Modules.pullbackPushforwardAdjunction k).homEquiv M N).symm
        ((u ≫ (Scheme.Modules.pushforward g).map v) ≫
          (Scheme.Modules.pushforwardComp f g).hom.app N ≫
            (Scheme.Modules.pushforwardCongr h).hom.app N) =
      (pullbackPasteOfEq f g k h M).inv ≫
        (Scheme.Modules.pullback f).map
          (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm u) ≫
          ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm v := by
  subst h
  have e := (pushforwardCongr_rfl_app (f ≫ g) N).1
  rw [e, Category.comp_id, homEquiv_symm_pushforwardComp]
  simp [pullbackPasteOfEq, Scheme.Modules.pullbackCongr]

/-- **The transpose of the unit of direct images.** For a morphism `e` equal to an identity, the
transpose of the identification `M ⟶ e_* M` is the identification `e^* M ⟶ M`. -/
theorem homEquiv_symm_pushforwardId {e : A ⟶ A} (he : e = 𝟙 A) (M : A.Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction e).homEquiv M M).symm
        ((Scheme.Modules.pushforwardId A).inv.app M ≫
          (Scheme.Modules.pushforwardCongr he).inv.app M) =
      (Scheme.Modules.pullbackCongr he).hom.app M ≫ (Scheme.Modules.pullbackId A).hom.app M := by
  subst he
  have e := (pushforwardCongr_rfl_app (𝟙 A) M).2
  rw [e, Category.comp_id, Equiv.symm_apply_eq]
  have key := unit_conjugateEquiv Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 A)) (Scheme.Modules.pullbackId A).hom M
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at key
  simp only [Adjunction.id_unit, NatTrans.id_app, Functor.id_obj, Category.id_comp] at key
  rw [Adjunction.homEquiv_unit]
  simpa [Scheme.Modules.pullbackCongr] using key

end Mates

/-! ### The transitions of a module on the total Zariski site -/

variable {X} in
/-- The transition of Stacks 09WF is natural in the module. -/
theorem componentModuleTransition_naturality {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
    {F G : Modules X} (g : F ⟶ G) :
    (Scheme.Modules.pullback (X.map φ)).map ((componentModule X m).map g) ≫
        componentModuleTransition X φ G =
      componentModuleTransition X φ F ≫ (componentModule X n).map g :=
  Adjunction.homEquiv_naturality_right_square
    (Scheme.Modules.pullbackPushforwardAdjunction (X.map φ))
    ((componentModule X m).map g) ((componentModuleDirectTransition X φ).app G)
    ((componentModuleDirectTransition X φ).app F) ((componentModule X n).map g)
    ((componentModuleDirectTransition X φ).naturality g)

variable {X} in
/-- The transition of Stacks 09WF along an identity map of simplicial degrees is the unit of the
family. -/
theorem componentModuleTransition_id_eq (n : SimplexCategoryᵒᵖ) (F : Modules X) :
    componentModuleTransition X (𝟙 n) F =
      (Scheme.Modules.pullbackCongr (X.map_id n)).hom.app ((componentModule X n).obj F) ≫
        (Scheme.Modules.pullbackId _).hom.app ((componentModule X n).obj F) := by
  rw [componentModuleTransition, ← componentModuleDirectTransition_id]
  exact homEquiv_symm_pushforwardId (X.map_id n) _

variable {X} in
/-- The transition of Stacks 09WF along a composite of maps of simplicial degrees, preceded by
the compositor of the family, is the composite of the transitions. -/
theorem pullbackPasteOfEq_comp_componentModuleTransition {n m l : SimplexCategoryᵒᵖ}
    (φ : n ⟶ m) (ψ : m ⟶ l) (F : Modules X) :
    (pullbackPasteOfEq (X.map φ) (X.map ψ) (X.map (φ ≫ ψ)) (X.map_comp φ ψ).symm
        ((componentModule X l).obj F)).hom ≫ componentModuleTransition X (φ ≫ ψ) F =
      (Scheme.Modules.pullback (X.map φ)).map (componentModuleTransition X ψ F) ≫
        componentModuleTransition X φ F := by
  rw [componentModuleTransition, ← componentModuleDirectTransition_comp]
  simp only [componentPushforwardCompIso, Iso.trans_hom, NatTrans.comp_app]
  rw [homEquiv_symm_pushforwardComp_congr, Iso.hom_inv_id_assoc]
  rfl

/-- **The cartesian system of a cartesian module.** The components `F_n` of a cartesian module on
the total Zariski site, with its transitions `(X φ)^* F_m ≅ F_n`, form a cartesian system of the
family of modules on the degrees of `X`. -/
noncomputable def cartesianModuleSystem (F : Modules X) (hF : IsCartesianModule X F) :
    (zariskiModuleFamily X).CartesianSystem where
  obj n := (componentModule X (op n)).obj F
  trans φ := @asIso _ _ _ _ (componentModuleTransition X φ.op F) (hF φ.op)
  trans_id n := componentModuleTransition_id_eq (op n) F
  trans_comp ψ φ := pullbackPasteOfEq_comp_componentModuleTransition φ.op ψ.op F

/-- The functors of the family of modules on the degrees of a simplicial scheme are the pullbacks
along the face and degeneracy morphisms. -/
@[simp]
theorem zariskiModuleFamily_map {m n : SimplexCategory} (φ : m ⟶ n) :
    (zariskiModuleFamily X).map φ = Scheme.Modules.pullback (X.map φ.op) := rfl

end AlgebraicGeometry.SimplicialScheme

end
