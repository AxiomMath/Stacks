/-
Copyright (c) 2026 the Stacks project formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.NumberTheory.Drinfeld.Shtuka.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport

/-!
# Level structures on shtukas

Let `i : N ⟶ X` be a morphism of `k`-schemes (in the application, the inclusion of a finite
closed subscheme `N` of the curve `X`, the *level*). Restricting along `i × id_S` the data of a
shtuka `E ↪ E' ↩ τ^* E` of rank `r` over `S` gives maps of modules on `N ×_k S`. A *level-`N`
structure* (Drinfeld) is a trivialisation `ι : E|_{N ×_k S} ≅ 𝒪^r` compatible with the shtuka
structure: with `ι' : E'|_{N ×_k S} ≅ 𝒪^r` the trivialisation `ι ∘ j|_N⁻¹`, the restriction of
`t` is `τ^* ι` followed by the identification `τ^* 𝒪^r ≅ 𝒪^r`. Equivalently `ι` is fixed by the
Frobenius-linear automorphism `j|_N⁻¹ ∘ t|_N` of `E|_{N ×_k S}`. Its existence forces `j` and
`t` to be isomorphisms over `N ×_k S`, i.e. the legs of the shtuka to avoid `N`; this is the
situation of the moduli `Sht_N` over `(X − N)²`.

## Main definitions

* `Stacks.Drinfeld.Shtuka.leftMap` — `i × id_S : N ×_k S ⟶ X ×_k S`.
* `Stacks.Drinfeld.Shtuka.restrictFrobeniusTwistIso` — `(i × id)^* τ^* ≅ τ^* (i × id)^*`.
* `Stacks.Drinfeld.Shtuka.freeModule` — the free module `𝒪_Y^I`.
* `Stacks.Drinfeld.Shtuka.pullbackFreeIso` — `g^* 𝒪^I ≅ 𝒪^I` for a morphism of schemes `g`.
* `Stacks.Drinfeld.Shtuka.LevelStructure` — level structures on a shtuka.
* `Stacks.Drinfeld.Shtuka.LevelStructure.ofHom` — level structures pull back along morphisms of
  shtukas which are isomorphisms over `N ×_k S`.

## Main results

* `Stacks.Drinfeld.Shtuka.frobeniusTwist_comp_leftMap` — `τ_N ≫ (i × id) = (i × id) ≫ τ_X`.
* `Stacks.Drinfeld.Shtuka.LevelStructure.isIso_j`, `isIso_t` — over `N ×_k S` the modifications
  of a shtuka with a level structure are isomorphisms.

## References

* V. G. Drinfeld, *Cohomology of compactified manifolds of modules of F-sheaves of rank 2*,
  J. Soviet Math. 46 (1989), §2.
* L. Lafforgue, *Chtoucas de Drinfeld et correspondance de Langlands*, Invent. Math. 147 (2002),
  §I.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Drinfeld.Shtuka

open Stacks.Frobenius

/-- The free module `𝒪_Y^I` on a scheme `Y`, as an object of `Y.Modules`. -/
abbrev freeModule (Y : Scheme.{u}) (I : Type u) : Y.Modules := SheafOfModules.free I

/-- **The pullback of a free module is free**: `g^* 𝒪^I ≅ 𝒪^I` for a morphism of schemes `g`. This
is `AlgebraicGeometry.Scheme.Modules.pullbackFreeIso`, restated as an isomorphism in the category
`Y.Modules` (whose morphisms are `Scheme.Modules.Hom`) rather than in `SheafOfModules`, so that it
composes with morphisms of `Y.Modules` under `simp` and `rw`. -/
def pullbackFreeIso {Y Z : Scheme.{u}} (g : Y ⟶ Z) (I : Type u) :
    (Scheme.Modules.pullback g).obj (freeModule Z I) ≅ freeModule Y I where
  hom := (Scheme.Modules.pullbackFreeIso g I).hom
  inv := (Scheme.Modules.pullbackFreeIso g I).inv
  hom_inv_id := (Scheme.Modules.pullbackFreeIso g I).hom_inv_id
  inv_hom_id := (Scheme.Modules.pullbackFreeIso g I).inv_hom_id

variable {k : Type u} [Field k] [Fintype k] (p f : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ f)

variable {X S N : Over (Spec (.of k))}

/-- The map `i × id_S : N ×_k S ⟶ X ×_k S` of a morphism `i : N ⟶ X` over `k`. -/
def leftMap (i : N ⟶ X) : product N S ⟶ product X S :=
  pullback.map N.hom S.hom X.hom S.hom i.left (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, Over.w]) (by simp)

@[reassoc (attr := simp)]
theorem leftMap_fst (i : N ⟶ X) :
    leftMap (S := S) i ≫ pullback.fst X.hom S.hom = pullback.fst N.hom S.hom ≫ i.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem leftMap_snd (i : N ⟶ X) :
    leftMap (S := S) i ≫ pullback.snd X.hom S.hom = pullback.snd N.hom S.hom :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- `τ` commutes with `i × id_S`. -/
theorem frobeniusTwist_comp_leftMap (i : N ⟶ X) :
    frobeniusTwist p f hcard N S ≫ leftMap i = leftMap i ≫ frobeniusTwist p f hcard X S := by
  apply pullback.hom_ext
  · simp only [Category.assoc, leftMap_fst, frobeniusTwist_fst, frobeniusTwist_fst_assoc]
  · simp only [Category.assoc, leftMap_snd, frobeniusTwist_snd, leftMap_snd_assoc]

/-- The natural isomorphism `(i × id)^* ∘ τ_X^* ≅ τ_N^* ∘ (i × id)^*`. -/
def restrictFrobeniusTwistIso (i : N ⟶ X) :
    Scheme.Modules.pullback (frobeniusTwist p f hcard X S) ⋙
        Scheme.Modules.pullback (leftMap i) ≅
      Scheme.Modules.pullback (leftMap i) ⋙
        Scheme.Modules.pullback (frobeniusTwist p f hcard N S) :=
  Scheme.Modules.pullbackComp _ _ ≪≫
    Scheme.Modules.pullbackCongr (frobeniusTwist_comp_leftMap p f hcard i).symm ≪≫
      (Scheme.Modules.pullbackComp _ _).symm

variable {p f hcard} {r : ℕ}

/-- A **level structure** on a shtuka `𝓔 = (E ↪ E' ↩ τ^* E)` along `i : N ⟶ X`:
trivialisations `ι : E|_{N ×_k S} ≅ 𝒪^r` and `ι' : E'|_{N ×_k S} ≅ 𝒪^r` (restriction along
`i × id_S`) such that `j|_N` becomes the identity, `ι' ∘ j|_N = ι`, and `t|_N` becomes the
canonical identification `τ^* 𝒪^r ≅ 𝒪^r`, `ι' ∘ t|_N = τ^* ι`. -/
structure LevelStructure (𝓔 : Shtuka p f hcard X S r) (i : N ⟶ X) where
  /-- The trivialisation of `E` over `N ×_k S`. -/
  ι : (Scheme.Modules.pullback (leftMap i)).obj 𝓔.E ≅
    freeModule (product N S) (ULift.{u} (Fin r))
  /-- The trivialisation of `E'` over `N ×_k S`. -/
  ι' : (Scheme.Modules.pullback (leftMap i)).obj 𝓔.E' ≅
    freeModule (product N S) (ULift.{u} (Fin r))
  j_comp : (Scheme.Modules.pullback (leftMap i)).map 𝓔.j ≫ ι'.hom = ι.hom
  t_comp : (Scheme.Modules.pullback (leftMap i)).map 𝓔.t ≫ ι'.hom =
    (restrictFrobeniusTwistIso p f hcard i).hom.app 𝓔.E ≫
      (Scheme.Modules.pullback (frobeniusTwist p f hcard N S)).map ι.hom ≫
        (pullbackFreeIso _ _).hom

namespace LevelStructure

variable {𝓔 𝓕 𝓖 : Shtuka p f hcard X S r} {i : N ⟶ X}

/-- Over `N ×_k S`, the modification `j` of a shtuka with a level structure is an
isomorphism. -/
theorem isIso_j (ℓ : LevelStructure 𝓔 i) :
    IsIso ((Scheme.Modules.pullback (leftMap i)).map 𝓔.j) := by
  have : IsIso ((Scheme.Modules.pullback (leftMap i)).map 𝓔.j ≫ ℓ.ι'.hom) := by
    rw [ℓ.j_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ℓ.ι'.hom

/-- Over `N ×_k S`, the modification `t` of a shtuka with a level structure is an
isomorphism. -/
theorem isIso_t (ℓ : LevelStructure 𝓔 i) :
    IsIso ((Scheme.Modules.pullback (leftMap i)).map 𝓔.t) := by
  have : IsIso ((Scheme.Modules.pullback (leftMap i)).map 𝓔.t ≫ ℓ.ι'.hom) := by
    rw [ℓ.t_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ℓ.ι'.hom

/-- **Level structures pull back along morphisms of shtukas**: a level structure on `𝓕` and an
morphism `α : 𝓔 ⟶ 𝓕` whose components restrict to isomorphisms over
`N ×_k S` give the level structure `ι_𝓕 ∘ α|_N` on `𝓔`. -/
def ofHom (α : 𝓔 ⟶ 𝓕) [IsIso ((Scheme.Modules.pullback (leftMap i)).map α.hom)]
    [IsIso ((Scheme.Modules.pullback (leftMap i)).map α.hom')] (ℓ : LevelStructure 𝓕 i) :
    LevelStructure 𝓔 i where
  ι := asIso ((Scheme.Modules.pullback (leftMap i)).map α.hom) ≪≫ ℓ.ι
  ι' := asIso ((Scheme.Modules.pullback (leftMap i)).map α.hom') ≪≫ ℓ.ι'
  j_comp := by
    simp only [Iso.trans_hom, asIso_hom]
    rw [← Functor.map_comp_assoc, α.j_comp, Functor.map_comp (Scheme.Modules.pullback (leftMap i)),
      Category.assoc, ℓ.j_comp]
  t_comp := by
    have hnat := (restrictFrobeniusTwistIso p f hcard i).hom.naturality α.hom
    simp only [Functor.comp_map] at hnat
    simp only [Iso.trans_hom, asIso_hom]
    rw [← Functor.map_comp_assoc, α.t_comp, Functor.map_comp (Scheme.Modules.pullback (leftMap i)),
      Category.assoc, ℓ.t_comp, reassoc_of% hnat,
      Functor.map_comp (Scheme.Modules.pullback (frobeniusTwist p f hcard N S)), Category.assoc]

@[simp] theorem ofHom_ι (α : 𝓔 ⟶ 𝓕) [IsIso ((Scheme.Modules.pullback (leftMap i)).map α.hom)]
    [IsIso ((Scheme.Modules.pullback (leftMap i)).map α.hom')] (ℓ : LevelStructure 𝓕 i) :
    (ofHom α ℓ).ι = asIso ((Scheme.Modules.pullback (leftMap i)).map α.hom) ≪≫ ℓ.ι := rfl

end LevelStructure

end Stacks.Drinfeld.Shtuka
