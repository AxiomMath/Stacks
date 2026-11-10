module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.CounitFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Stalk
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization

/-!
# Isomorphisms and zero modules detected by flat pullbacks covering the scheme

A morphism of `𝒪_X`-modules is an isomorphism as soon as its pullbacks along two flat morphisms
whose images cover `X` are isomorphisms: the stalk of a pullback along a flat morphism is a
faithfully flat base change of the stalk. Also: a quasi-coherent module whose pullback to the
spectrum of the local ring at `y` is trivial has stalk at `y` free of rank one. These are used in
the proof of the second sentence of [Stacks, Tag 0EA2].

## Main results

* `AlgebraicGeometry.DualizingDivisor.isIso_of_isIso_pullback_map_of_cover`
* `AlgebraicGeometry.DualizingDivisor.isZero_of_isZero_pullback_of_cover`
* `AlgebraicGeometry.DualizingDivisor.nonempty_stalk_linearEquiv_of_pullback_fromSpecStalk_iso`
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe u

namespace AlgebraicGeometry.DualizingDivisor

variable {X Z₁ Z₂ : Scheme.{u}} (g₁ : Z₁ ⟶ X) (g₂ : Z₂ ⟶ X) [Flat g₁] [Flat g₂]

/-- **A morphism of modules is an isomorphism if its pullbacks along two flat morphisms whose
images cover the scheme are isomorphisms**: it is then an isomorphism on every stalk
(`AlgebraicGeometry.VectorBundleCodimensionOne.isIso_stalk_of_isIso_pullback_map`). -/
theorem isIso_of_isIso_pullback_map_of_cover
    (hcov : ∀ x : X, x ∈ Set.range g₁ ∨ x ∈ Set.range g₂) {F G : X.Modules} (φ : F ⟶ G)
    (h₁ : IsIso ((Scheme.Modules.pullback g₁).map φ))
    (h₂ : IsIso ((Scheme.Modules.pullback g₂).map φ)) : IsIso φ := by
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk φ fun x => ?_
  rcases hcov x with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · exact VectorBundleCodimensionOne.isIso_stalk_of_isIso_pullback_map g₁ φ h₁ z
  · exact VectorBundleCodimensionOne.isIso_stalk_of_isIso_pullback_map g₂ φ h₂ z

/-- **A module whose pullbacks along two flat morphisms with covering images vanish is zero.** -/
theorem isZero_of_isZero_pullback_of_cover
    (hcov : ∀ x : X, x ∈ Set.range g₁ ∨ x ∈ Set.range g₂) {F : X.Modules}
    (h₁ : IsZero ((Scheme.Modules.pullback g₁).obj F))
    (h₂ : IsZero ((Scheme.Modules.pullback g₂).obj F)) : IsZero F := by
  have hz : ∀ {Z : Scheme.{u}} (g : Z ⟶ X), IsZero ((Scheme.Modules.pullback g).obj F) →
      IsIso ((Scheme.Modules.pullback g).map (0 : F ⟶ 0)) := fun g hg =>
    have : (Scheme.Modules.pullback g).IsLeftAdjoint :=
      ⟨_, ⟨Scheme.Modules.pullbackPushforwardAdjunction g⟩⟩
    ⟨⟨0, hg.eq_of_src _ _, (Functor.map_isZero _ (isZero_zero _)).eq_of_src _ _⟩⟩
  have := isIso_of_isIso_pullback_map_of_cover g₁ g₂ hcov (0 : F ⟶ 0) (hz g₁ h₁) (hz g₂ h₂)
  exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))

/-- **A quasi-coherent module whose pullback to the spectrum of the local ring at `y` is trivial
has stalk at `y` free of rank one**: the global sections of that pullback are the stalk
(`AlgebraicGeometry.fromSpecStalkSectionsStalkEquiv`), and those of the structure sheaf of
`Spec 𝒪_{Y,y}` are `𝒪_{Y,y}`. -/
theorem nonempty_stalk_linearEquiv_of_pullback_fromSpecStalk_iso {Y : Scheme.{u}} (M : Y.Modules)
    [M.IsQuasicoherent] (y : Y)
    (e : (Scheme.Modules.pullback (Y.fromSpecStalk y)).obj M ≅
      SheafOfModules.unit (Spec (Y.presheaf.stalk y)).ringCatSheaf) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule M y
    Nonempty (M.presheaf.stalk y ≃ₗ[Y.presheaf.stalk y] Y.presheaf.stalk y) := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  let := fromSpecStalkPullbackModule M y
  let R := Spec (Y.presheaf.stalk y)
  let φ := Scheme.ΓSpecIso (Y.presheaf.stalk y)
  let : Module (Y.presheaf.stalk y) Γ(R, ⊤) := Module.compHom _ φ.inv.hom
  let E₂ : Γ((Scheme.Modules.pullback (Y.fromSpecStalk y)).obj M, ⊤) ≃ₗ[Y.presheaf.stalk y]
      Γ(R, ⊤) :=
    { toFun := fun a => (e.hom.val.app (Opposite.op ⊤)).hom a
      invFun := fun a => (e.inv.val.app (Opposite.op ⊤)).hom a
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a => (e.hom.val.app (Opposite.op ⊤)).hom.map_smul (φ.inv.hom r) a
      left_inv := fun a => by
        change ((e.hom ≫ e.inv).val.app (Opposite.op ⊤)).hom a = a
        rw [e.hom_inv_id]; rfl
      right_inv := fun a => by
        change ((e.inv ≫ e.hom).val.app (Opposite.op ⊤)).hom a = a
        rw [e.inv_hom_id]; rfl }
  let E₃ : Γ(R, ⊤) ≃ₗ[Y.presheaf.stalk y] Y.presheaf.stalk y :=
    { toFun := fun a => φ.hom.hom a
      invFun := fun a => φ.inv.hom a
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a => by
        change φ.hom.hom (φ.inv.hom r * a) = r * φ.hom.hom a
        rw [map_mul]
        change (φ.inv ≫ φ.hom).hom r * _ = _
        rw [φ.inv_hom_id]; rfl
      left_inv := fun a => by
        change (φ.hom ≫ φ.inv).hom a = a
        rw [φ.hom_inv_id]; rfl
      right_inv := fun a => by
        change (φ.inv ≫ φ.hom).hom a = a
        rw [φ.inv_hom_id]; rfl }
  exact ⟨(fromSpecStalkSectionsStalkEquiv M y hU hy).symm ≪≫ₗ E₂ ≪≫ₗ E₃⟩

end AlgebraicGeometry.DualizingDivisor

end
