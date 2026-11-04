module

public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Isomorphisms of sheaves detected on a covering family of objects

Let `J` be a Grothendieck topology on a category `C` and let `P` be a property of objects of `C`
such that every object is covered by objects with property `P`, in the sense that the sieve of
morphisms factoring through an object with property `P` is a covering sieve. A morphism of
sheaves of sets which is bijective on sections over every object with property `P` is then an
isomorphism: it is locally injective and locally surjective.

## Main results

* `CategoryTheory.Sheaf.isIso_of_bijective_of_mem`: the criterion.
-/

@[expose] public section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A morphism of sheaves of sets is an isomorphism as soon as it is bijective on sections over
every object with a property `P`, provided every object of the site is covered by objects with
property `P`. -/
theorem isIso_of_bijective_of_mem {F G : Sheaf J (Type w)} (f : F ⟶ G) (P : ObjectProperty C)
    (hP : ∀ U : C, Sieve.generate (fun (V : C) (_ : V ⟶ U) ↦ P V) ∈ J U)
    (hf : ∀ V : C, P V → Function.Bijective (f.hom.app (op V))) : IsIso f := by
  refine (isLocallyBijective_iff_isIso f).1 ⟨?_, ?_⟩
  · refine ⟨fun {U} x y h ↦ J.superset_covering ?_ (hP U.unop)⟩
    rintro V g ⟨W, a, b, hW, rfl⟩
    show F.obj.map (a ≫ b).op x = F.obj.map (a ≫ b).op y
    rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    congr 1
    apply (hf W hW).1
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
    exact congrArg (G.obj.map b.op) h
  · refine ⟨fun {U} s ↦ J.superset_covering ?_ (hP U)⟩
    rintro V g ⟨W, a, b, hW, rfl⟩
    obtain ⟨t, ht⟩ := (hf W hW).2 (G.obj.map b.op s)
    refine ⟨F.obj.map a.op t, ?_⟩
    rw [NatTrans.naturality_apply, ht, op_comp, Functor.map_comp_apply]

end CategoryTheory.Sheaf

end
