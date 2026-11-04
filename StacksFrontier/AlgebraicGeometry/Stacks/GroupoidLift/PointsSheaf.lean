module

public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.Points

/-!
# The sheaf condition on the points over the spectra of small algebras

Let `X` be a sheaf on the big fppf site over `S` with a map `π : X ⟶ yoneda.obj T'`. Along a map
of small `Γ(T')`-algebras `N → N'` whose spectrum is surjective and étale, the points of `X` over
`T'` are separated (`relPoints_map_injective`) and satisfy the sheaf condition: a point over `N'`
whose two images over a pushout `N' ⊗_N N'` agree comes from a point over `N`
(`exists_relPoints_map_eq`).
-/

@[expose] public section

open CategoryTheory Opposite Limits
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : X ⟶ yoneda.obj T')

/-- A sheaf `X` on the big fppf site over `S` satisfies the sheaf condition for the singleton
presieve on `specOverMap f`, where `f : N ⟶ N'` is a map of small `Γ(T')`-algebras whose spectrum
is surjective and étale. -/
theorem isSheafFor_singleton_specOverMap (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    {N N' : SmallAlg (ringOf B S hS T') B.cutoff} (f : N ⟶ N')
    (hsurj : Surjective (Spec.map (CommRingCat.ofHom (f.hom.hom : N.obj →+* N'.obj))))
    (het : Etale (Spec.map (CommRingCat.ofHom (f.hom.hom : N.obj →+* N'.obj)))) :
    Presieve.IsSheafFor X (Presieve.singleton (specOverMap f)) := by
  rw [Presieve.isSheafFor_iff_generate]
  exact (isSheaf_iff_isSheaf_of_type _ _).mp hX _
    (Space.sieve_generate_singleton_mem_topology_over B S hS (specOverMap f) hsurj het)

/-- **Separatedness** of the points over `T'` along a surjective étale map of spectra. -/
theorem relPoints_map_injective (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    {N N' : SmallAlg (ringOf B S hS T') B.cutoff} (f : N ⟶ N')
    (hsurj : Surjective (Spec.map (CommRingCat.ofHom (f.hom.hom : N.obj →+* N'.obj))))
    (het : Etale (Spec.map (CommRingCat.ofHom (f.hom.hom : N.obj →+* N'.obj)))) :
    Function.Injective ((relPoints T' π).map f) := by
  intro x₁ x₂ h
  have hsep := (isSheafFor_singleton_specOverMap hX f hsurj het).isSeparatedFor
  rw [Presieve.isSeparatedFor_singleton] at hsep
  exact Subtype.ext (hsep (congrArg Subtype.val h))

/-- A functor preserves an equality of composites of two morphisms. -/
private theorem map_comp_eq_map_comp_of_comp_eq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {W Y Z : C} {a a' : W ⟶ Y} {b b' : Y ⟶ Z} (h : a ≫ b = a' ≫ b') :
    F.map a ≫ F.map b = F.map a' ≫ F.map b' := by
  simpa only [Functor.map_comp] using congrArg F.map h

/-- **The sheaf condition** for the points over `T'` along a surjective étale map of spectra:
a point over `N'` whose two images over a pushout `N' ⊗_N N'` agree comes from a point over `N`. -/
theorem exists_relPoints_map_eq (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    {N N' N₂ : SmallAlg (ringOf B S hS T') B.cutoff} (f : N ⟶ N') (i₁ i₂ : N' ⟶ N₂)
    (hpush : IsPushout (CommRingCat.ofHom (f.hom.hom : N.obj →+* N'.obj))
      (CommRingCat.ofHom (f.hom.hom : N.obj →+* N'.obj))
      (CommRingCat.ofHom (i₁.hom.hom : N'.obj →+* N₂.obj))
      (CommRingCat.ofHom (i₂.hom.hom : N'.obj →+* N₂.obj)))
    (hsurj : Surjective (Spec.map (CommRingCat.ofHom (f.hom.hom : N.obj →+* N'.obj))))
    (het : Etale (Spec.map (CommRingCat.ofHom (f.hom.hom : N.obj →+* N'.obj))))
    (z : (relPoints T' π).obj N') (hz : (relPoints T' π).map i₁ z = (relPoints T' π).map i₂ z) :
    ∃ x : (relPoints T' π).obj N, (relPoints T' π).map f x = z := by
  have hsheaf := isSheafFor_singleton_specOverMap hX f hsurj het
  rw [Presieve.isSheafFor_singleton] at hsheaf
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ hpush
  obtain ⟨x, hx, -⟩ := hsheaf z.1 (by
    intro Z p₁ p₂ hp
    let q₁ : (BigFppfOver.toScheme B S hS).obj Z ⟶ Spec (CommRingCat.of N'.obj) :=
      (BigFppfOver.toScheme B S hS).map p₁
    let q₂ : (BigFppfOver.toScheme B S hS).obj Z ⟶ Spec (CommRingCat.of N'.obj) :=
      (BigFppfOver.toScheme B S hS).map p₂
    have hp' : q₁ ≫ Spec.map (CommRingCat.ofHom (f.hom.hom : N.obj →+* N'.obj)) =
        q₂ ≫ Spec.map (CommRingCat.ofHom (f.hom.hom : N.obj →+* N'.obj)) := by
      exact map_comp_eq_map_comp_of_comp_eq _ hp
    have hw₁ : q₁ ≫ specToBase N' ≫ B.inclusion.map T'.hom = B.inclusion.map Z.hom := by
      have h := congrArg (fun k ↦ B.inclusion.map k) (Over.w p₁)
      simp only [Functor.map_comp] at h
      exact h
    have hbase : hpb.lift _ _ hp' ≫ specToBase N₂ ≫ B.inclusion.map T'.hom =
        B.inclusion.map Z.hom := by
      calc hpb.lift _ _ hp' ≫ specToBase N₂ ≫ B.inclusion.map T'.hom
          = hpb.lift _ _ hp' ≫ (Spec.map (CommRingCat.ofHom (i₁.hom.hom : N'.obj →+* N₂.obj)) ≫
              specToBase N') ≫ B.inclusion.map T'.hom := by rw [specMap_comp_specToBase]
        _ = (hpb.lift _ _ hp' ≫ Spec.map (CommRingCat.ofHom
              (i₁.hom.hom : N'.obj →+* N₂.obj))) ≫ specToBase N' ≫ B.inclusion.map T'.hom := by
            simp only [Category.assoc]
        _ = B.inclusion.map Z.hom := by rw [hpb.lift_fst, hw₁]
    let h : Z ⟶ specOver N₂ :=
      BigFppfOver.homMk B S hS (contains_spec N₂) _ (hpb.lift _ _ hp') hbase
    have h₁ : h ≫ specOverMap i₁ = p₁ := BigFppfOver.map_toScheme_injective B S hS (by
      dsimp only
      rw [Functor.map_comp]
      exact hpb.lift_fst q₁ q₂ hp')
    have h₂ : h ≫ specOverMap i₂ = p₂ := BigFppfOver.map_toScheme_injective B S hS (by
      dsimp only
      rw [Functor.map_comp]
      exact hpb.lift_snd q₁ q₂ hp')
    rw [← h₁, ← h₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    exact congrArg (X.map h.op) (congrArg Subtype.val hz))
  refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
  have : Flat (Spec.map (CommRingCat.ofHom (f.hom.hom : N.obj →+* N'.obj))) := inferInstance
  have hepi := Flat.epi_of_flat_of_surjective
    (Spec.map (CommRingCat.ofHom (f.hom.hom : N.obj →+* N'.obj)))
  have h1 := NatTrans.naturality_apply π (specOverMap f).op x
  rw [hx, show π.app _ z.1 = specOverToBase N' from z.2] at h1
  have h1' : specOverMap f ≫ π.app _ x = specOverMap f ≫ specOverToBase N := by
    rw [specOverMap_comp_toBase]
    exact h1.symm
  apply BigFppfOver.map_toScheme_injective B S hS
  exact (cancel_epi (Spec.map (CommRingCat.ofHom (f.hom.hom : N.obj →+* N'.obj)))).mp
    (map_comp_eq_map_comp_of_comp_eq (BigFppfOver.toScheme B S hS) h1')

end AlgebraicGeometry.Stack.GroupoidLift

end
