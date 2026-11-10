module

public import Mathlib.CategoryTheory.Galois.Decomposition
public import Mathlib.CategoryTheory.Galois.GaloisObjects
public import Mathlib.GroupTheory.Coset.Card
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleConnectedObjects
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.FiberFunctorComplete

/-!
# Galois covers, and the Galois components of a torsor

A finite étale morphism `p : Z ⟶ Y` is a **Galois cover** ([Stacks, Section 03SF]) if `Z` is a
Galois object of the category `FÉt_Y` of finite étale `Y`-schemes: `Z` is connected and its
automorphism group over `Y` acts transitively on the geometric fibres. Its **group** is that
automorphism group.

If a finite group `M` acts on a finite étale cover `V` of a connected scheme, simply transitively
on one geometric fibre, then every connected component of `V` is a Galois cover whose group has
order dividing `|M|`: it is the stabilizer of the component. This is the "small detail omitted"
in the proof of [Stacks, Tag 0EYT].

## Main definitions

* `Stacks.EtaleCohomology.IsGaloisCover` — the notion of Galois cover.

## Main results

* `CategoryTheory.PreGaloisCategory.exists_isGalois_of_torsor` — in a Galois category, a
  connected component of an `M`-torsor object is Galois with automorphism group of order
  dividing `|M|`.
* `Stacks.EtaleCohomology.exists_isGaloisCover_of_torsor` — the same for finite étale covers of a
  connected scheme.

## References

* [Stacks Project, Section 03SF](https://stacks.math.columbia.edu/tag/03SF)
* [Stacks Project, Tag 0BN2](https://stacks.math.columbia.edu/tag/0BN2)
* [Stacks Project, Tag 0EYT](https://stacks.math.columbia.edu/tag/0EYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w v₁ v₂

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u} [Category.{v₁} C] [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- **A connected component of a torsor is Galois, with group of order dividing that of the
structure group.** Let a finite additive group `M` act on an object `X` of a Galois category,
by `m ↦ α m`, simply transitively on the fibre of `X`, and let `a` be a point of that fibre. Then
`X` has a connected subobject `A`, whose fibre contains a point over `a`, which is Galois and
whose automorphism group has order dividing `|M|`. -/
theorem exists_isGalois_of_torsor {M : Type*} [AddGroup M] [Finite M] (X : C) (α : M → (X ⟶ X))
    (hα : ∀ m m', α (m + m') = α m ≫ α m') (hα0 : α 0 = 𝟙 X)
    (htors : ∀ a b : F.obj X, ∃! m : M, F.map (α m) a = b) (a : F.obj X) :
    ∃ (A : C) (i : A ⟶ X) (c : F.obj A), Mono i ∧ F.map i c = a ∧ IsGalois A ∧
      Nat.card (Aut A) ∣ Nat.card M := by
  obtain ⟨A, i, c, hc, hA, hi⟩ := fiber_in_connected_component F X a
  have hiso : ∀ m, IsIso (α m) := fun m =>
    ⟨⟨α (-m), by rw [← hα, add_neg_cancel, hα0], by rw [← hα, neg_add_cancel, hα0]⟩⟩
  have hinj : Function.Injective (F.map i) := by
    have : Mono ((F ⋙ FintypeCat.incl).map i) := inferInstance
    exact (mono_iff_injective _).1 this
  -- every point of the fibre of `A` is the image of `c` under an automorphism, which moreover
  -- intertwines `i` with the action of the corresponding element of `M`
  have key : ∀ (m : M) (c' : F.obj A), F.map (α m) a = F.map i c' →
      ∃ φ : A ≅ A, F.map φ.hom c = c' ∧ i ≫ α m = φ.hom ≫ i := by
    intro m c' hm
    have : Mono (i ≫ α m) := by have := hiso m; infer_instance
    obtain ⟨φ, hφ⟩ := connected_component_unique F c c' (i ≫ α m) i
      (by simp [hc, hm])
    exact ⟨φ, hφ, evaluation_injective_of_isConnected F A X c (by simp [hc, hm, hφ])⟩
  -- every point of the fibre of `A` is `a` moved by some element of `M`, then pulled back by `i`
  have hex : ∀ c' : F.obj A, ∃ m, F.map (α m) a = F.map i c' := fun c' =>
    (htors a (F.map i c')).exists
  have htrans : MulAction.IsPretransitive (Aut A) (F.obj A) := by
    refine ⟨fun c₁ c₂ => ?_⟩
    obtain ⟨m₁, hm₁⟩ := hex c₁
    obtain ⟨m₂, hm₂⟩ := hex c₂
    obtain ⟨φ₁, hφ₁, -⟩ := key m₁ c₁ hm₁
    obtain ⟨φ₂, hφ₂, -⟩ := key m₂ c₂ hm₂
    refine ⟨Aut.of (φ₁.symm ≪≫ φ₂), ?_⟩
    change F.map (φ₁.symm ≪≫ φ₂).hom c₁ = c₂
    rw [← hφ₁, ← hφ₂]
    simp [← FintypeCat.comp_apply]
  have hgal : IsGalois A := (isGalois_iff_pretransitive F A).2 htrans
  -- the stabilizer of the component
  let G : AddSubgroup M :=
    { carrier := {m | F.map (α m) a ∈ Set.range (F.map i)}
      zero_mem' := ⟨c, by rw [hc, hα0, F.map_id]; rfl⟩
      add_mem' := by
        rintro m m' ⟨c₁, h₁⟩ ⟨c₂, h₂⟩
        obtain ⟨φ, -, hφ⟩ := key m' c₂ h₂.symm
        refine ⟨F.map φ.hom c₁, ?_⟩
        symm
        rw [hα, F.map_comp, FintypeCat.comp_apply, ← h₁, ← FintypeCat.comp_apply, ← F.map_comp,
          hφ]
        simp
      neg_mem' := by
        rintro m ⟨c₁, h₁⟩
        obtain ⟨φ, hφc, hφ⟩ := key m c₁ h₁.symm
        refine ⟨F.map φ.inv c, ?_⟩
        have : i = φ.hom ≫ i ≫ α (-m) := by
          rw [← Category.assoc, ← hφ, Category.assoc, ← hα, add_neg_cancel, hα0,
            Category.comp_id]
        have h3 : φ.inv ≫ i = i ≫ α (-m) := by
          conv_lhs => rw [this]
          simp
        rw [← FintypeCat.comp_apply, ← F.map_comp, h3, F.map_comp, FintypeCat.comp_apply, hc] }
  have hcard : Nat.card (Aut A) = Nat.card G := by
    have h1 : Nat.card (Aut A) = Nat.card (F.obj A) :=
      Nat.card_eq_of_bijective _ ⟨evaluation_aut_injective_of_isConnected F A c,
        fun c' => htrans.exists_smul_eq c c'⟩
    rw [h1]
    refine (Nat.card_eq_of_bijective
      (fun m : G => (m.2 : F.map (α m) a ∈ Set.range (F.map i)).choose)
      ⟨fun m m' h => ?_, fun c' => ?_⟩).symm
    · have hm := (m.2 : F.map (α m) a ∈ Set.range (F.map i)).choose_spec
      have hm' := (m'.2 : F.map (α m') a ∈ Set.range (F.map i)).choose_spec
      dsimp only at h
      rw [h] at hm
      exact Subtype.ext ((htors a _).unique hm.symm hm'.symm)
    · obtain ⟨m, hm⟩ := hex c'
      refine ⟨⟨m, c', hm.symm⟩, hinj ?_⟩
      exact ((⟨m, c', hm.symm⟩ : G).2 :
        F.map (α m) a ∈ Set.range (F.map i)).choose_spec.trans hm
  exact ⟨A, i, c, hi, hc, hgal, hcard ▸ G.card_addSubgroup_dvd_card⟩

end CategoryTheory.PreGaloisCategory


namespace Stacks.EtaleCohomology

open _root_.AlgebraicGeometry
open CategoryTheory.PreGaloisCategory

variable {Y : Scheme.{u}}

/-- **Stacks Project, Section 03SF: Galois covers.** A finite étale morphism `p : Z ⟶ Y` is a
*Galois cover* if `Z` is a Galois object of `FÉt_Y`: `Z` is connected and the automorphism group
of `Z` over `Y` acts transitively on the geometric fibre of `Z` at every geometric point of `Y`.
Its *group* is that automorphism group, `Aut (Over.mk p)`. -/
def IsGaloisCover {Z : Scheme.{u}} (p : Z ⟶ Y) : Prop :=
  IsFinite p ∧ Etale p ∧ ConnectedSpace Z ∧
    ∀ (y : GeometricPoint Y) (a b : {s : y.source ⟶ Z // s ≫ p = y.hom}),
      ∃ σ : Aut (Over.mk p), a.1 ≫ σ.asIso.hom.left = b.1

/-- The automorphisms of a finite étale cover in `FÉt_Y` are its automorphisms over `Y`. -/
def autEquivOverAut (A : FiniteEtaleOver Y) : (A ≅ A) ≃ Aut (Over.mk A.hom) :=
  (Functor.FullyFaithful.ofFullyFaithful
    (MorphismProperty.Over.forget (finiteEtale : MorphismProperty Scheme.{u}) ⊤ Y)).isoEquiv.trans
    Aut.isoEquiv.symm

/-- **A connected component of a torsor is a Galois cover.** Let `Y` be connected, let `x` be a
geometric point of `Y`, and let a finite additive group `M` act on a finite étale cover `V` of
`Y`, simply transitively on the geometric fibre at `x`, and let `a` be a point of that fibre. Then
`V` has a connected component `A` through `a` which is a Galois cover of `Y` whose group has order
dividing `|M|`. -/
theorem exists_isGaloisCover_of_torsor [ConnectedSpace Y] (x : GeometricPoint Y) {M : Type*}
    [AddGroup M] [Finite M] (V : FiniteEtaleOver Y) (α : M → (V ⟶ V))
    (hα : ∀ m m', α (m + m') = α m ≫ α m') (hα0 : α 0 = 𝟙 V)
    (htors : ∀ a b : finiteEtaleFiber x V, ∃! m : M, (finiteEtaleFiberFunctor x).map (α m) a = b)
    (a : finiteEtaleFiber x V) :
    ∃ (A : FiniteEtaleOver Y) (i : A ⟶ V) (c : finiteEtaleFiber x A), Mono i ∧
      c.1 ≫ i.left = a.1 ∧ IsGaloisCover A.hom ∧ Nat.card (Aut (Over.mk A.hom)) ∣ Nat.card M := by
  let : GaloisCategory (FiniteEtaleOver Y) :=
    IsGaloisCategory.toGaloisCategory (finiteEtaleFiberFunctor x)
  let : IsGaloisCategory (finiteEtaleFiberFintypeFunctor Y x ⋙ FintypeCat.incl) :=
    finiteEtaleFiberFunctor_isGaloisCategory Y x
  let : FiberFunctor (finiteEtaleFiberFintypeFunctor Y x) :=
    IsGaloisCategory.fiberFunctor (finiteEtaleFiberFintypeFunctor Y x)
  obtain ⟨A, i, c, hi, hc, hgal, hcard⟩ := exists_isGalois_of_torsor
    (finiteEtaleFiberFintypeFunctor Y x) V α hα hα0 htors a
  refine ⟨A, i, c, hi, congrArg Subtype.val hc, ⟨A.prop.1, A.prop.2,
    connectedSpace_left_of_isConnected A inferInstance, fun z a b => ?_⟩, ?_⟩
  · let : IsGaloisCategory (finiteEtaleFiberFintypeFunctor Y z ⋙ FintypeCat.incl) :=
      finiteEtaleFiberFunctor_isGaloisCategory Y z
    let : FiberFunctor (finiteEtaleFiberFintypeFunctor Y z) :=
      IsGaloisCategory.fiberFunctor (finiteEtaleFiberFintypeFunctor Y z)
    have := (isGalois_iff_pretransitive (finiteEtaleFiberFintypeFunctor Y z) A).1 hgal
    obtain ⟨σ, hσ⟩ := this.exists_smul_eq (a : finiteEtaleFiber z A) (b : finiteEtaleFiber z A)
    exact ⟨autEquivOverAut A σ.asIso, congrArg Subtype.val hσ⟩
  · rw [← Nat.card_congr (Aut.isoEquiv.trans (autEquivOverAut A))]
    exact hcard

end Stacks.EtaleCohomology

end
