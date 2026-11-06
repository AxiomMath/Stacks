module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheaf

/-!
# The free sheaf `𝐆_a^r` on the small étale site

For a scheme `X` and `r : ℕ`, `Stacks.ArtinSchreier.freeAdditiveSheaf X r` is the abelian sheaf on
the small étale site of `X` whose sections over an étale `X`-scheme `U` are, by definition, the
`r`-tuples of functions on `U`.

## Main definitions

* `Stacks.ArtinSchreier.freeAdditiveSheaf`: `𝐆_a^r`.
* `Stacks.ArtinSchreier.freeAdditiveProj`: the coordinate projections `𝐆_a^r ⟶ 𝐆_a`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.ArtinSchreier

variable (X : Scheme.{u}) (r : ℕ)

/-- The presheaf `U ↦ Γ(U)^r` on the small étale site. -/
def freeAdditivePresheaf : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj U := AddCommGrpCat.of (ULift.{u + 1} (Fin r → Γ(U.unop.left, ⊤)))
  map g := AddCommGrpCat.ofHom
    { toFun := fun b => ULift.up fun i => g.unop.left.appTop.hom (b.down i)
      map_zero' := ULift.ext (funext fun _ => map_zero _)
      map_add' := fun _ _ => ULift.ext (funext fun _ => map_add _ _ _) }
  map_id U := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun b => ULift.ext (funext fun i => ?_))
    change (𝟙 U.unop.left : U.unop.left ⟶ _).appTop.hom (b.down i) = b.down i
    rw [Scheme.Hom.id_appTop]
    rfl
  map_comp g h := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun b => ULift.ext (funext fun i => ?_))
    change (h.unop.left ≫ g.unop.left).appTop.hom (b.down i) =
      h.unop.left.appTop.hom (g.unop.left.appTop.hom (b.down i))
    rw [Scheme.Hom.comp_appTop]
    rfl

/-- The presheaf of sets underlying `freeAdditivePresheaf X r` is a sheaf. -/
theorem isSheaf_forget_freeAdditivePresheaf :
    Presieve.IsSheaf X.smallEtaleTopology
      (freeAdditivePresheaf X r ⋙ CategoryTheory.forget AddCommGrpCat) := by
  intro U R hR x hx
  have hG := isSheaf_forget_additivePresheaf.{u, 0} X R hR
  let xi : Fin r → Presieve.FamilyOfElements
      (additivePresheaf.{u, 0} X ⋙ CategoryTheory.forget AddCommGrpCat) R :=
    fun i _ g hg => ULift.up ((x g hg).down i)
  have hxi : ∀ i, (xi i).Compatible := fun i Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w =>
    ULift.ext (congrArg (fun b : ULift (Fin r → _) => b.down i) (hx g₁ g₂ h₁ h₂ w))
  let t : (freeAdditivePresheaf X r ⋙ CategoryTheory.forget AddCommGrpCat).obj (op U) :=
    ULift.up fun i => (hG.amalgamate (xi i) (hxi i)).down
  refine ⟨t, fun Y g hg => ?_, fun t' ht' => ?_⟩
  · exact ULift.ext (funext fun i => congrArg ULift.down (hG.isAmalgamation (hxi i) g hg))
  · refine ULift.ext (funext fun i => congrArg ULift.down ?_)
    exact hG.isSeparatedFor (xi i) (ULift.up (t'.down i)) (hG.amalgamate (xi i) (hxi i))
      (fun Y g hg => ULift.ext (congrArg (fun b : ULift (Fin r → _) => b.down i) (ht' g hg)))
      (hG.isAmalgamation (hxi i))

/-- The presheaf `U ↦ Γ(U)^r` is a sheaf on the small étale site. -/
theorem isSheaf_freeAdditivePresheaf :
    Presheaf.IsSheaf X.smallEtaleTopology (freeAdditivePresheaf X r) :=
  Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget _ _
    (isSheaf_forget_freeAdditivePresheaf X r)

/-- **`𝐆_a^r` on the small étale site**: sections over `U` are the `r`-tuples of functions. -/
def freeAdditiveSheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ⟨freeAdditivePresheaf X r, isSheaf_freeAdditivePresheaf X r⟩

/-- The `i`-th coordinate projection `𝐆_a^r ⟶ 𝐆_a`. -/
def freeAdditiveProj (i : Fin r) : freeAdditiveSheaf X r ⟶ additiveSheaf.{u, 0} X :=
  ⟨{ app _ := AddCommGrpCat.ofHom
       { toFun := fun b => ULift.up (b.down i)
         map_zero' := rfl
         map_add' := fun _ _ => rfl }
     naturality _ _ _ := rfl }⟩

/-- The `i`-th coordinate projection sends an `r`-tuple of functions to its `i`-th entry. -/
theorem freeAdditiveProj_app (i : Fin r) (U : X.Etaleᵒᵖ)
    (b : (freeAdditiveSheaf X r).obj.obj U) :
    ((freeAdditiveProj X r i).hom.app U b).down = b.down i :=
  rfl

end Stacks.ArtinSchreier

end
