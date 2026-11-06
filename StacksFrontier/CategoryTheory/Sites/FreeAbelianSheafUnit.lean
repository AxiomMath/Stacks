module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# The unit of the free abelian sheaf adjunction

For a site `(C, J)` the free abelian group functor and the forgetful functor induce an adjunction
`ℤ[-] ⊣ U` between sheaves of sets and abelian sheaves (`CategoryTheory.Sheaf.adjunction` at
`AddCommGrpCat.adj`), whose left adjoint sheafifies the presheaf of free abelian groups. This file
proves the two facts about its unit `η_G : G ⟶ U ℤ[G]` that recover a sheaf of sets from abelian
sheaves:

* `η_G` is injective on sections (`Stacks.FreeAbelianSheaf.unit_injective`);
* its image is the equalizer of the two maps `η_{U ℤ[G]}` and `U ℤ[η_G]` from `U ℤ[G]` to
  `U ℤ[U ℤ[G]]` (`Stacks.FreeAbelianSheaf.exists_unit_eq_of_unit_eq`).

The first is the separatedness of `G` against the local injectivity of sheafification, together
with injectivity of `FreeAbelianGroup.of`. For the second, a section `y` of `U ℤ[G]` is locally the
image of a formal combination `p` of sections of `G`; the hypothesis says that, after a further
refinement, the generator `[y]` equals the image of `p` under `ℤ[η_G]`, so `y` is in the image of
`η_G` there (`Stacks.FreeAbelianSheaf.mem_range_of_of_eq_map`); the local preimages are unique by
the first fact and glue because `G` is a sheaf.

## Main results

* `Stacks.FreeAbelianSheaf.unit_app_apply` — the unit on sections is the generator.
* `Stacks.FreeAbelianSheaf.unit_injective` — the unit is injective on sections.
* `Stacks.FreeAbelianSheaf.exists_unit_eq_of_unit_eq` — the equalizer property.

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.FreeAbelianSheaf

/-- **A generator of a free abelian group in the image of a map of free abelian groups induced by
a map of sets is the generator of an element of the image.** -/
theorem mem_range_of_of_eq_map {α β : Type*} (φ : α → β) (a : β) (q : FreeAbelianGroup α)
    (h : FreeAbelianGroup.of a = FreeAbelianGroup.map φ q) : a ∈ Set.range φ := by
  classical
  by_contra hna
  let χ : FreeAbelianGroup β →+ ℤ := FreeAbelianGroup.lift fun b => if b = a then 1 else 0
  have h₁ : χ (FreeAbelianGroup.of a) = 1 := by simp [χ]
  have h₂ : ∀ q' : FreeAbelianGroup α, χ (FreeAbelianGroup.map φ q') = 0 := by
    intro q'
    induction q' using FreeAbelianGroup.induction_on with
    | zero => simp
    | of x =>
      have : φ x ≠ a := fun hx => hna ⟨x, hx⟩
      simp [χ, this]
    | neg x hx =>
      rw [map_neg, map_neg, neg_eq_zero]
      have : φ x ≠ a := fun h => hna ⟨x, h⟩
      simp [χ, this]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  rw [h, h₂] at h₁
  exact zero_ne_one h₁

/-- `Stacks.FreeAbelianSheaf.mem_range_of_of_eq_map` after a further map of generators. -/
theorem mem_range_of_map_of_eq_map_map {α β γ : Type*} (φ : α → β) (ψ : β → γ) (x : β)
    (q : FreeAbelianGroup α)
    (h : FreeAbelianGroup.map ψ (FreeAbelianGroup.of x) =
      FreeAbelianGroup.map ψ (FreeAbelianGroup.map φ q)) : ψ x ∈ Set.range (ψ ∘ φ) := by
  rw [FreeAbelianGroup.map_of_apply, ← FreeAbelianGroup.map_comp_apply] at h
  exact mem_range_of_of_eq_map _ _ _ h

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.PreservesSheafification (forget AddCommGrpCat.{max u v})]

/-- The free abelian sheaf on a sheaf of sets: the sheafification of the presheaf of free abelian
groups on its sections. -/
abbrev freeSheaf : Sheaf J (Type (max u v)) ⥤ Sheaf J AddCommGrpCat.{max u v} :=
  Sheaf.composeAndSheafify J AddCommGrpCat.free

/-- The underlying sheaf of sets of an abelian sheaf. -/
abbrev forgetSheaf : Sheaf J AddCommGrpCat.{max u v} ⥤ Sheaf J (Type (max u v)) :=
  sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max u v})

/-- **The free abelian sheaf is left adjoint to the underlying sheaf of sets.** -/
abbrev freeSheafAdj : freeSheaf J ⊣ forgetSheaf J :=
  Sheaf.adjunction J AddCommGrpCat.adj

omit [J.PreservesSheafification (forget AddCommGrpCat.{max u v})] in
/-- **The unit of the adjunction on sections is the generator**, followed by sheafification. -/
theorem unit_app_apply (G : Sheaf J (Type (max u v))) (V : Cᵒᵖ) (x : G.obj.obj V) :
    ((freeSheafAdj J).unit.app G).hom.app V x =
      (toSheafify J (G.obj ⋙ AddCommGrpCat.free)).app V (FreeAbelianGroup.of x) := by
  have h := Sheaf.adjunction_unit_app_hom J AddCommGrpCat.adj G
  exact (congrArg (fun φ => φ.app V x) h).trans rfl

/-- **The unit of the free abelian sheaf adjunction is injective on sections.** -/
theorem unit_injective (G : Sheaf J (Type (max u v))) (V : Cᵒᵖ) :
    Function.Injective (((freeSheafAdj J).unit.app G).hom.app V) := by
  intro x y hxy
  rw [unit_app_apply, unit_app_apply] at hxy
  have hS := Presheaf.equalizerSieve_mem J (toSheafify J (G.obj ⋙ AddCommGrpCat.free))
    (FreeAbelianGroup.of x) (FreeAbelianGroup.of y) hxy
  have hsep := ((isSheaf_iff_isSheaf_of_type J G.obj).mp G.property).isSeparated _ hS
  refine hsep.ext fun Y f hf => ?_
  have hf' : FreeAbelianGroup.map (G.obj.map f.op) (FreeAbelianGroup.of x) =
      FreeAbelianGroup.map (G.obj.map f.op) (FreeAbelianGroup.of y) := hf
  exact FreeAbelianGroup.of_injective (by simpa using hf')

/-- **The equalizer property of the unit.** A section `y` of `U ℤ[G]` on which the two maps
`η_{U ℤ[G]}` and `U ℤ[η_G]` agree is the image of a section of `G` under `η_G`. -/
theorem exists_unit_eq_of_unit_eq (G : Sheaf J (Type (max u v))) (V : C)
    (y : ((forgetSheaf J).obj ((freeSheaf J).obj G)).obj.obj (op V))
    (hy : ((freeSheafAdj J).unit.app ((forgetSheaf J).obj ((freeSheaf J).obj G))).hom.app (op V) y =
      ((forgetSheaf J).map ((freeSheaf J).map ((freeSheafAdj J).unit.app G))).hom.app (op V) y) :
    ∃ r : G.obj.obj (op V), ((freeSheafAdj J).unit.app G).hom.app (op V) r = y := by
  let H := (forgetSheaf J).obj ((freeSheaf J).obj G)
  let η := (freeSheafAdj J).unit.app G
  have nat : ∀ {Y Z : C} (g : Z ⟶ Y) (r : G.obj.obj (op Y)),
      η.hom.app (op Z) (G.obj.map g.op r) = H.obj.map g.op (η.hom.app (op Y) r) := by
    intro Y Z g r
    have h := ConcreteCategory.congr_hom (η.hom.naturality g.op) r
    simp only [ConcreteCategory.comp_apply] at h
    exact h
  have mapcomp : ∀ {Y Z : C} (g : Z ⟶ Y) (f : Y ⟶ V),
      H.obj.map g.op (H.obj.map f.op y) = H.obj.map (g ≫ f).op y := by
    intro Y Z g f
    rw [op_comp, H.obj.map_comp, ConcreteCategory.comp_apply]
  -- the sieve of the arrows along which `y` is in the image of `η`
  let S : Sieve V :=
    { arrows := fun Y f => ∃ r : G.obj.obj (op Y), η.hom.app (op Y) r = H.obj.map f.op y
      downward_closed := by
        rintro Y Z f ⟨r, hr⟩ g
        exact ⟨G.obj.map g.op r, (nat g r).trans ((congrArg (H.obj.map g.op) hr).trans
          (mapcomp g f))⟩ }
  have hS : S ∈ J V := by
    let P := G.obj ⋙ AddCommGrpCat.free
    refine J.transitive (Presheaf.imageSieve_mem J (toSheafify J P) y) S ?_
    rintro Y f ⟨p, hp⟩
    -- the two maps agree after restriction along `f`
    have hyf : ((freeSheafAdj J).unit.app H).hom.app (op Y) (H.obj.map f.op y) =
        ((forgetSheaf J).map ((freeSheaf J).map η)).hom.app (op Y) (H.obj.map f.op y) := by
      have n₁ := ConcreteCategory.congr_hom (((freeSheafAdj J).unit.app H).hom.naturality f.op) y
      have n₂ := ConcreteCategory.congr_hom
        (((forgetSheaf J).map ((freeSheaf J).map η)).hom.naturality f.op) y
      simp only [ConcreteCategory.comp_apply] at n₁ n₂
      exact n₁.trans ((congrArg (fun z => ((forgetSheaf J).obj ((freeSheaf J).obj H)).obj.map
        f.op z) hy).trans n₂.symm)
    rw [unit_app_apply] at hyf
    -- `U ℤ[η]` of a sheafified combination is the sheafified image combination
    have hmap : ((forgetSheaf J).map ((freeSheaf J).map η)).hom.app (op Y)
        ((toSheafify J P).app (op Y) p) =
        (toSheafify J (H.obj ⋙ AddCommGrpCat.free)).app (op Y)
          (FreeAbelianGroup.map (η.hom.app (op Y)) p) := by
      have hnat := toSheafify_naturality J (Functor.whiskerRight η.hom AddCommGrpCat.free)
      have h := ConcreteCategory.congr_hom (NatTrans.congr_app hnat (op Y)) p
      simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
      exact h.symm
    have hyf' : (toSheafify J (H.obj ⋙ AddCommGrpCat.free)).app (op Y)
          (FreeAbelianGroup.of ((toSheafify J P).app (op Y) p)) =
        (toSheafify J (H.obj ⋙ AddCommGrpCat.free)).app (op Y)
          (FreeAbelianGroup.map (η.hom.app (op Y)) p) := by
      have e : H.obj.map f.op y = (toSheafify J P).app (op Y) p := hp.symm
      rw [e] at hyf
      exact hyf.trans hmap
    have hE := Presheaf.equalizerSieve_mem J (toSheafify J (H.obj ⋙ AddCommGrpCat.free)) _ _
      hyf'
    refine J.superset_covering ?_ hE
    intro Z g hg
    obtain ⟨r, hr⟩ := mem_range_of_map_of_eq_map_map (η.hom.app (op Y)) (H.obj.map g.op)
      ((toSheafify J P).app (op Y) p) p hg
    refine ⟨G.obj.map g.op r, (nat g r).trans ?_⟩
    have e : (toSheafify J P).app (op Y) p = H.obj.map f.op y := hp
    rw [← mapcomp g f, ← e]
    exact hr
  -- the local preimages glue
  have hG := (isSheaf_iff_isSheaf_of_type J G.obj).mp G.property
  have hH := (isSheaf_iff_isSheaf_of_type J H.obj).mp H.property
  let fam : Presieve.FamilyOfElements G.obj S.arrows := fun Y f hf => hf.choose
  have hfam : ∀ (Y : C) (f : Y ⟶ V) (hf : S f), η.hom.app (op Y) (fam f hf) = H.obj.map f.op y :=
    fun Y f hf => hf.choose_spec
  have hcomp : fam.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hw
    apply unit_injective J G (op Z)
    refine (nat g₁ (fam f₁ h₁)).trans ?_
    refine Eq.trans ?_ (nat g₂ (fam f₂ h₂)).symm
    rw [hfam, hfam, mapcomp, mapcomp, hw]
  obtain ⟨r, hr, -⟩ := hG S hS fam hcomp
  refine ⟨r, (hH.isSeparated S hS).ext fun Y f hf => ?_⟩
  refine (nat f r).symm.trans ?_
  rw [hr f hf, hfam]

end Stacks.FreeAbelianSheaf

end
