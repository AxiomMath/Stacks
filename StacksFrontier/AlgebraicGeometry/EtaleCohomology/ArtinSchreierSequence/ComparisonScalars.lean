module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FrobeniusComparison

/-!
# The comparison of [Stacks, Tag 03P2] for `𝐆_a` is linear over the base field

Let `X` be a scheme over a field `k`. The étale cohomology `Hⁿ(X_étale, 𝐆_a)` carries the action
of `k` through multiplication by scalars on `𝐆_a` (`Stacks.ArtinSchreier.additiveSmul`), and the
cohomology `Hⁿ(X, 𝒪_X)` is a `k`-vector space. The comparison
`Stacks.ArtinSchreier.etaleHAdditiveSheafAddEquiv` between the two intertwines these actions:
each of its steps is natural, and multiplication by a scalar on `𝐆_a` corresponds to
multiplication by the same scalar on `𝒪_X`.

## Main results

* `Stacks.ArtinSchreier.etaleHAdditiveSheafAddEquivObjectUniverse_map`: the comparison carries
  the map induced by an endomorphism of `𝐆_a` coming from an endomorphism of `𝒪_X` to the map
  induced by the latter.
* `Stacks.ArtinSchreier.topDegreeFrobeniusComparison_equiv_additiveSmul`: the comparison is
  `k`-linear.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe w u

namespace Stacks.ArtinSchreier

attribute [local instance] Stacks.Topology.hasExt_sheafOpens
  Stacks.Topology.enoughInjectives_sheafOpens
  Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous

attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt

attribute [local instance 3000] isGrothendieckAbelian_smallEtale_morphismUniverse
  enoughInjectives_smallEtale_morphismUniverse hasExt_smallEtale_morphismUniverse
  hasExt_smallEtale_objectUniverse

attribute [local instance] preservesSheafification_uliftFunctor_smallEtale
  additive_uliftSheafCompose_smallEtale preservesFiniteLimits_uliftSheafCompose_smallEtale
  preservesFiniteColimits_uliftSheafCompose_smallEtale

variable (X : Scheme.{u})

/-- **Multiplication by a global function on `𝐆_a` at coefficients `AddCommGrpCat.{u}`.** -/
def additiveSmulBase (a : Γ(X, ⊤)) : additiveSheafBase X ⟶ additiveSheafBase X :=
  ⟨{ app V := AddCommGrpCat.ofHom
        (X := (additiveSheafBase X).obj.obj V) (Y := (additiveSheafBase X).obj.obj V)
        (AddMonoidHom.mulLeft (etaleFunction V.unop a))
     naturality V W f := by
      ext (x : Γ(V.unop.left, ⊤))
      change etaleFunction W.unop a * f.unop.left.appTop.hom x =
        f.unop.left.appTop.hom (etaleFunction V.unop a * x)
      rw [map_mul, appTop_etaleFunction] }⟩

/-- **Raising the coefficients of multiplication by `a` gives
`Stacks.ArtinSchreier.additiveSmul`**, through `AlgebraicGeometry.additiveSheafBaseUliftIso`. -/
theorem additiveSheafBaseUliftIso_hom_comp_additiveSmul (a : Γ(X, ⊤)) :
    (additiveSheafBaseUliftIso X).hom ≫ additiveSmul.{u, u + 1} X a =
      (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map
        (additiveSmulBase X a) ≫ (additiveSheafBaseUliftIso X).hom := by
  ext U x
  rfl

/-- **The comparison `𝒪_X ≅ ε_* 𝐆_a` intertwines multiplication by `a` on both sides.** -/
theorem unitToPushforwardAdditiveSheafBase_comp_additiveSmulBase (a : Γ(X, ⊤)) :
    unitToPushforwardAdditiveSheafBase X ≫
        (smallEtaleZariskiPushforward X).map (additiveSmulBase X a) =
      (SheafOfModules.toSheaf X.ringCatSheaf).map
          (globalSmul a (SheafOfModules.unit X.ringCatSheaf)) ≫
        unitToPushforwardAdditiveSheafBase X := by
  ext V (x : Γ(X, V.unop))
  have h1 : (globalSmul a (SheafOfModules.unit X.ringCatSheaf)).app V.unop x =
      restrictTop a V.unop * x :=
    globalSmul_app a (SheafOfModules.unit X.ringCatSheaf) V.unop x
  show (id (etaleFunction ((opensToEtale X).obj V.unop) a) : Γ(V.unop, ⊤)) *
      (Scheme.Opens.ι V.unop).appLE V.unop ⊤ (Scheme.Opens.ι_preimage_self V.unop).ge x =
    (Scheme.Opens.ι V.unop).appLE V.unop ⊤ (Scheme.Opens.ι_preimage_self V.unop).ge
      ((globalSmul a (SheafOfModules.unit X.ringCatSheaf)).app V.unop x)
  rw [h1, map_mul]
  congr 1
  show (Scheme.Opens.ι V.unop).appTop.hom a = _
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.ι_appLE, restrictTop]
  exact (presheaf_map_map_eq_map _ _ _ a).symm

/-- If an additive equivalence intertwines `f` and `g`, its inverse intertwines `g` and `f`. -/
private theorem symm_apply_map_comm {α β : Type*} [Add α] [Add β] (e : α ≃+ β) {f : α → α}
    {g : β → β} (h : ∀ x, e (f x) = g (e x)) (y : β) : e.symm (g y) = f (e.symm y) := by
  rw [e.symm_apply_eq, h, e.apply_symm_apply]

/-- If `e.hom ≫ g = f ≫ e.hom`, then `e.inv ≫ f = g ≫ e.inv`. -/
private theorem inv_comp_eq_comp_inv_of_hom_comp_eq {C : Type*} [Category C] {A B : C}
    {e : A ≅ B} {f : A ⟶ A} {g : B ⟶ B} (h : e.hom ≫ g = f ≫ e.hom) :
    e.inv ≫ f = g ≫ e.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The comparison carries an endomorphism of `𝐆_a` coming from an endomorphism of `𝒪_X` to
the map that endomorphism induces on `Hⁿ(X, 𝒪_X)`.** -/
theorem etaleHAdditiveSheafAddEquivObjectUniverse_map (n : ℕ)
    (ψ : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (mBase : additiveSheafBase X ⟶ additiveSheafBase X)
    (m : additiveSheaf.{u, u + 1} X ⟶ additiveSheaf.{u, u + 1} X)
    (h₁ : (additiveSheafBaseUliftIso X).hom ≫ m =
      (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map mBase ≫
        (additiveSheafBaseUliftIso X).hom)
    (h₂ : unitToPushforwardAdditiveSheafBase X ≫ (smallEtaleZariskiPushforward X).map mBase =
      (SheafOfModules.toSheaf X.ringCatSheaf).map ψ ≫ unitToPushforwardAdditiveSheafBase X)
    (x : Sheaf.H.{u + 1, u + 1} (additiveSheaf.{u, u + 1} X) n) :
    etaleHAdditiveSheafAddEquivObjectUniverse X n (Sheaf.H.map m n x) =
      (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).map
        (((moduleGlobalSections X).rightDerived n).map ψ)
        (etaleHAdditiveSheafAddEquivObjectUniverse X n x) := by
  have h2 := symm_apply_map_comm (Stacks.Cohomology.CoefficientLift.sheafHIsoCongr.{u + 1, u + 1}
    (additiveSheafBaseUliftIso X) n) (sheafHIsoCongr_map _ h₁ n)
  have h3 := symm_apply_map_comm (smallEtaleSheafHUliftAddEquiv X (additiveSheafBase X) n)
    (smallEtaleSheafHUliftAddEquiv_map X mBase n)
  have h4 := inv_comp_eq_comp_inv_of_hom_comp_eq
    (abelianCohomologyIsoEtaleH_hom_naturality X
      ((SheafOfModules.toSheaf X.ringCatSheaf).map ψ) mBase h₂ n)
  have h5' := (inv_comp_eq_comp_inv_of_hom_comp_eq
    (moduleCohomologyIsoAbelian_hom_naturality X ψ n)).symm
  show (moduleCohomologyIsoAbelian X (SheafOfModules.unit X.ringCatSheaf) n).inv
      ((abelianCohomologyIsoEtaleH X n).inv
        ((smallEtaleSheafHUliftAddEquiv X (additiveSheafBase X) n).symm
          ((Stacks.Cohomology.CoefficientLift.sheafHIsoCongr.{u + 1, u + 1}
            (additiveSheafBaseUliftIso X) n).symm (Sheaf.H.map m n x)))) = _
  rw [h2, h3]
  set z := (smallEtaleSheafHUliftAddEquiv X (additiveSheafBase X) n).symm
    ((Stacks.Cohomology.CoefficientLift.sheafHIsoCongr.{u + 1, u + 1}
      (additiveSheafBaseUliftIso X) n).symm x)
  have h4' := ConcreteCategory.congr_hom h4 z
  have h5'' := ConcreteCategory.congr_hom h5' ((abelianCohomologyIsoEtaleH X n).inv z)
  show (moduleCohomologyIsoAbelian X (SheafOfModules.unit X.ringCatSheaf) n).inv
    ((AddCommGrpCat.ofHom (Sheaf.H.map mBase n) ≫ (abelianCohomologyIsoEtaleH X n).inv) z) = _
  rw [← h4']
  exact h5''

/-- **The comparison of [Stacks, Tag 03P2] for `𝐆_a` carries multiplication by a global
function on `𝐆_a` to multiplication by it on `Hⁿ(X, 𝒪_X)`**, in an arbitrary `Ext` universe. -/
theorem etaleHAdditiveSheafAddEquiv_additiveSmul
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] (n : ℕ) (a : Γ(X, ⊤))
    (x : Sheaf.H.{w, u + 1} (additiveSheaf.{u, u + 1} X) n) :
    etaleHAdditiveSheafAddEquiv X n (Sheaf.H.map (additiveSmul.{u, u + 1} X a) n x) =
      (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).map
        (((moduleGlobalSections X).rightDerived n).map
          (globalSmul a (SheafOfModules.unit X.ringCatSheaf)))
        (etaleHAdditiveSheafAddEquiv X n x) := by
  have h1 : extChgUnivAddEquiv.{w, u + 1} _ _ n
      (Sheaf.H.map (additiveSmul.{u, u + 1} X a) n x) =
      (extChgUnivAddEquiv.{w, u + 1} _ _ n x).comp
        (Ext.mk₀ (additiveSmul.{u, u + 1} X a)) (add_zero n) :=
    @ext_chgUniv_comp_mk₀ _ _ _ _ (hasExt_smallEtale_objectUniverse X) _ _ _ _ x _
  show etaleHAdditiveSheafAddEquivObjectUniverse X n (extChgUnivAddEquiv.{w, u + 1} _ _ n
    (Sheaf.H.map (additiveSmul.{u, u + 1} X a) n x)) = _
  rw [h1]
  exact etaleHAdditiveSheafAddEquivObjectUniverse_map X n _ (additiveSmulBase X a) _
    (additiveSheafBaseUliftIso_hom_comp_additiveSmul X a)
    (unitToPushforwardAdditiveSheafBase_comp_additiveSmulBase X a) _

variable {p : ℕ} (hp : p.Prime) (k : Type u) [Field k] [CharP k p] {X}
  (f : X ⟶ Spec (.of k))

/-- **The comparison of [Stacks, Tag 03P2] for `𝐆_a` is `k`-linear**: multiplication by the
image of `c ∈ k` on `𝐆_a` is carried to multiplication by `c` on the `k`-vector space
`Hⁿ(X, 𝒪_X)`. -/
theorem topDegreeFrobeniusComparison_equiv_additiveSmul
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] (n : ℕ) (c : k)
    (x : Sheaf.H.{w, u + 1} (additiveSheaf.{u, u + 1} X) n) :
    (topDegreeFrobeniusComparison.{w} hp k f n).equiv
        (Sheaf.H.map (additiveSmul.{u, u + 1} X (baseScalarSection k f c)) n x) =
      c • (topDegreeFrobeniusComparison.{w} hp k f n).equiv x := by
  have h := cohomologyOverFieldMap_globalSmul k f c (SheafOfModules.unit X.ringCatSheaf) n
    ((topDegreeFrobeniusComparison.{w} hp k f n).equiv x)
  rw [← h]
  have h2 := etaleHAdditiveSheafAddEquiv_additiveSmul X n (baseScalarSection k f c) x
  with_unfolding_all exact h2

end Stacks.ArtinSchreier

end
