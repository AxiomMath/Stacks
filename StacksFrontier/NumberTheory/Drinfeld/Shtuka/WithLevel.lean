/-
Copyright (c) 2026 the Stacks project formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.NumberTheory.Drinfeld.Shtuka.LevelStructure.BaseChange

/-!
# Shtukas with level structure: the fibre categories of `Sht_N`

For a level `i : N ⟶ X` and a `k`-scheme `S`, the category `Sht_N(S)` has as objects the pairs
`(𝓔, ι)` of a rank-`r` shtuka over `S` and a level structure on it along `i`, and as morphisms
the morphisms of shtukas whose restrictions to `N ×_k S` carry the level structure of the source
to the level structure of the target. Base change of shtukas and of level structures makes
`S ↦ Sht_N(S)` functorial in `S` (`Stacks.Drinfeld.Shtuka.WithLevel.baseChangeFunctor`), and the
level group `Aut(𝒪_N^r)` acts on each fibre category by changing the level structure.

## Main definitions

* `Stacks.Drinfeld.Shtuka.WithLevel` — shtukas with a level structure along `i`, with their
  category structure.
* `Stacks.Drinfeld.Shtuka.WithLevel.forget` — the functor to shtukas.
* `Stacks.Drinfeld.Shtuka.WithLevel.baseChangeFunctor` — base change along `g : S' ⟶ S`.
* `Stacks.Drinfeld.Shtuka.WithLevel.levelGroupAction` — the action of `a ∈ Aut(𝒪_N^r)`.

## Main results

* `Stacks.Drinfeld.Shtuka.WithLevel.isIso_restrict_hom` — a morphism of shtukas with level
  structure restricts to an isomorphism over `N ×_k S`.
* `Stacks.Drinfeld.Shtuka.WithLevel.levelGroupAction_comp_baseChangeFunctor` — base change
  commutes with the level group action.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Drinfeld.Shtuka

variable {k : Type u} [Field k] [Fintype k] {p f : ℕ} [Fact p.Prime] [CharP k p]
  {hcard : Fintype.card k = p ^ f} {X S S' N : Over (Spec (.of k))} {r : ℕ}

variable (p f hcard X S r) in
/-- A **shtuka with level structure** along `i : N ⟶ X`: a rank-`r` shtuka over `S` together with
a level structure on it. These are the `S`-points of the moduli `Sht_N`. -/
structure WithLevel (i : N ⟶ X) where
  /-- The shtuka. -/
  shtuka : Shtuka p f hcard X S r
  /-- Its level structure. -/
  level : LevelStructure shtuka i

namespace WithLevel

variable {i : N ⟶ X}

/-- A morphism of shtukas with level structure: a morphism of shtukas carrying the level
structure of the source to that of the target over `N ×_k S`. -/
@[ext]
structure Hom (𝓐 𝓑 : WithLevel p f hcard X S r i) where
  /-- The underlying morphism of shtukas. -/
  hom : 𝓐.shtuka ⟶ 𝓑.shtuka
  ι_comp : (Scheme.Modules.pullback (leftMap i)).map hom.hom ≫ 𝓑.level.ι.hom = 𝓐.level.ι.hom
  ι'_comp : (Scheme.Modules.pullback (leftMap i)).map hom.hom' ≫ 𝓑.level.ι'.hom =
    𝓐.level.ι'.hom

attribute [reassoc] Hom.ι_comp Hom.ι'_comp

/-- Shtukas with level structure along `i` form a category, with morphisms `WithLevel.Hom` and
identities and composition those of the underlying shtukas. -/
instance : Category (WithLevel p f hcard X S r i) where
  Hom := Hom
  id 𝓐 := { hom := 𝟙 _, ι_comp := by simp, ι'_comp := by simp }
  comp α β :=
    { hom := α.hom ≫ β.hom
      ι_comp := by rw [comp_hom, Functor.map_comp, Category.assoc, β.ι_comp, α.ι_comp]
      ι'_comp := by rw [comp_hom', Functor.map_comp, Category.assoc, β.ι'_comp, α.ι'_comp] }

/-- Two morphisms of shtukas with level structure are equal if their underlying morphisms of
shtukas are equal. -/
@[ext]
theorem hom_ext {𝓐 𝓑 : WithLevel p f hcard X S r i} {α β : 𝓐 ⟶ 𝓑} (h : α.hom = β.hom) :
    α = β :=
  Hom.ext h

/-- The underlying morphism of shtukas of the identity is the identity. -/
@[simp] theorem id_hom (𝓐 : WithLevel p f hcard X S r i) : (𝟙 𝓐 : 𝓐 ⟶ 𝓐).hom = 𝟙 _ := rfl

/-- The underlying morphism of shtukas of a composite is the composite of the underlying
morphisms. -/
@[simp, reassoc] theorem comp_hom {𝓐 𝓑 𝓒 : WithLevel p f hcard X S r i} (α : 𝓐 ⟶ 𝓑)
    (β : 𝓑 ⟶ 𝓒) : (α ≫ β).hom = α.hom ≫ β.hom := rfl

variable (p f hcard X S r i) in
/-- The functor forgetting the level structure. -/
@[simps]
def forget : WithLevel p f hcard X S r i ⥤ Shtuka p f hcard X S r where
  obj 𝓐 := 𝓐.shtuka
  map α := α.hom

/-- **A morphism of shtukas with level structure is an isomorphism over `N ×_k S`**: its
restriction is `ι_𝓑⁻¹ ∘ ι_𝓐`. -/
theorem isIso_restrict_hom {𝓐 𝓑 : WithLevel p f hcard X S r i} (α : 𝓐 ⟶ 𝓑) :
    IsIso ((Scheme.Modules.pullback (leftMap i)).map α.hom.hom) := by
  have : (Scheme.Modules.pullback (leftMap i)).map α.hom.hom = 𝓐.level.ι.hom ≫ 𝓑.level.ι.inv := by
    rw [← α.ι_comp]
    simp
  rw [this]
  infer_instance

/-- **Level structures of a morphism.** The level structure of the source of a morphism of
shtukas with level structure is the pullback of that of the target. -/
theorem level_eq_ofHom {𝓐 𝓑 : WithLevel p f hcard X S r i} (α : 𝓐 ⟶ 𝓑)
    [IsIso ((Scheme.Modules.pullback (leftMap i)).map α.hom.hom)]
    [IsIso ((Scheme.Modules.pullback (leftMap i)).map α.hom.hom')] :
    𝓐.level = LevelStructure.ofHom α.hom 𝓑.level := by
  ext : 1
  · exact Iso.ext α.ι_comp.symm
  · exact Iso.ext α.ι'_comp.symm

/-- **The level group acts on `Sht_N(S)`**: `a ∈ Aut(𝒪_N^r)` changes the level structure to
`a • ι`, and acts trivially on morphisms. -/
@[simps]
def levelGroupAction (a : Aut (freeModule N.left (ULift.{u} (Fin r)))) :
    WithLevel p f hcard X S r i ⥤ WithLevel p f hcard X S r i where
  obj 𝓐 := ⟨𝓐.shtuka, a • 𝓐.level⟩
  map α :=
    { hom := α.hom
      ι_comp := by
        simp only [LevelStructure.smul_ι, Iso.trans_hom]
        rw [α.ι_comp_assoc]
      ι'_comp := by
        simp only [LevelStructure.smul_ι', Iso.trans_hom]
        rw [α.ι'_comp_assoc] }

variable [IsSeparated X.hom]

/-- **Base change of shtukas with level structure** along `g : S' ⟶ S`. -/
@[simps]
def baseChangeFunctor (g : S' ⟶ S) :
    WithLevel p f hcard X S r i ⥤ WithLevel p f hcard X S' r i where
  obj 𝓐 := ⟨𝓐.shtuka.baseChange g, 𝓐.level.baseChange g⟩
  map {𝓐 𝓑} α :=
    { hom := baseChangeMap g α.hom
      ι_comp := by
        have hnat := (leftMapBaseChangeIso i g).hom.naturality α.hom.hom
        dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
        dsimp only [Shtuka.baseChange, baseChangeMap]
        simp only [LevelStructure.baseChange_ι, Iso.trans_hom, Iso.app_hom,
          Functor.mapIso_hom]
        rw [reassoc_of% hnat, ← Functor.map_comp_assoc, α.ι_comp]
      ι'_comp := by
        have hnat := (leftMapBaseChangeIso i g).hom.naturality α.hom.hom'
        dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
        dsimp only [Shtuka.baseChange, baseChangeMap]
        simp only [LevelStructure.baseChange_ι', Iso.trans_hom, Iso.app_hom,
          Functor.mapIso_hom]
        rw [reassoc_of% hnat, ← Functor.map_comp_assoc, α.ι'_comp] }
  map_id _ := hom_ext (Shtuka.hom_ext (by simp [baseChangeMap]) (by simp [baseChangeMap]))
  map_comp _ _ := hom_ext (Shtuka.hom_ext (by simp [baseChangeMap]) (by simp [baseChangeMap]))

/-- **Base change commutes with the level group action.** -/
theorem levelGroupAction_comp_baseChangeFunctor (g : S' ⟶ S)
    (a : Aut (freeModule N.left (ULift.{u} (Fin r)))) (𝓐 : WithLevel p f hcard X S r i) :
    (baseChangeFunctor g).obj ((levelGroupAction a).obj 𝓐) =
      (levelGroupAction a).obj ((baseChangeFunctor g).obj 𝓐) := by
  show (⟨𝓐.shtuka.baseChange g, (a • 𝓐.level).baseChange g⟩ : WithLevel p f hcard X S' r i) =
    ⟨𝓐.shtuka.baseChange g, a • 𝓐.level.baseChange g⟩
  rw [LevelStructure.baseChange_smul]

end WithLevel

end Stacks.Drinfeld.Shtuka
