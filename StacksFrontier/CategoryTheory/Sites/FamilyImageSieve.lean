module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# The sieve on which a section lifts along one member of a jointly surjective family

Let `J` be a Grothendieck topology and let `f i : X i ⟶ X` be a family of morphisms of sheaves
whose induced morphism out of the coproduct is locally surjective. Then for every section `x`
of `X` the supremum, over the members of the family, of the sieves on which `x` lifts along
that member is a covering sieve: locally `x` comes from one of the `X i`, though not from a
single one globally.

## Main results

* `CategoryTheory.Sheaf.iSup_imageSieve_mem_of_isLocallySurjective_sigmaDesc`: the supremum of
  the image sieves of a jointly locally surjective family is a covering sieve.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Sheaf

/-- If the morphism out of the coproduct induced by `f i : X i ⟶ X` is locally surjective, then
for every section `x` of `X` over `U` the supremum of the sieves on which `x` lifts along some
`f i` is a covering sieve of `U`. -/
theorem iSup_imageSieve_mem_of_isLocallySurjective_sigmaDesc
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J (Type (max u v))]
    [HasColimitsOfSize.{max u v, max u v} (Sheaf J (Type (max u v)))]
    {I : Type (max u v)} (Xi : I → Sheaf J (Type (max u v)))
    (X : Sheaf J (Type (max u v))) (f : ∀ i, Xi i ⟶ X)
    (hf : Sheaf.IsLocallySurjective (Sigma.desc f))
    (U : C) (x : X.obj.obj (Opposite.op U)) :
    (⨆ i, Presheaf.imageSieve (f i).hom x) ∈ J U := by
  let Q : Cᵒᵖ ⥤ Type (max u v) :=
    { obj T := Σ i, (Xi i).obj.obj T
      map a := ↾fun s => ⟨s.1, (Xi s.1).obj.map a s.2⟩ }
  let q : Q ⟶ X.obj :=
    { app T := ↾fun s => (f s.1).hom.app T s.2
      naturality T T' a := by ext s; exact NatTrans.naturality_apply (f s.1).hom a s.2 }
  let incl (i : I) : (Xi i).obj ⟶ Q := { app T := ↾fun s => ⟨i, s⟩ }
  let A : Sheaf J (Type (max u v)) := (presheafToSheaf J _).obj Q
  let a (i : I) : Xi i ⟶ A := ⟨incl i ≫ toSheafify J Q⟩
  let d : A ⟶ X := ⟨sheafifyLift J q X.property⟩
  have had : Sigma.desc a ≫ d = Sigma.desc f := by
    refine Sigma.hom_ext _ _ fun i => ?_
    simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    apply Sheaf.hom_ext
    change (incl i ≫ toSheafify J Q) ≫ sheafifyLift J q X.property = (f i).hom
    rw [Category.assoc, toSheafify_sheafifyLift]
    rfl
  have _ : Sheaf.IsLocallySurjective d :=
    (Sheaf.isLocallySurjective_iff_epi d).mpr (epi_of_epi_fac had)
  have hq : Presheaf.IsLocallySurjective J q := by
    rw [← toSheafify_sheafifyLift J q X.property]
    exact Presheaf.isLocallySurjective_comp J _ d.hom
  refine J.superset_covering ?_ (hq.imageSieve_mem x)
  rintro V g ⟨⟨i, s⟩, hs⟩
  exact (le_iSup (fun i => Presheaf.imageSieve (f i).hom x) i) _ ⟨s, hs⟩

end CategoryTheory.Sheaf

end
