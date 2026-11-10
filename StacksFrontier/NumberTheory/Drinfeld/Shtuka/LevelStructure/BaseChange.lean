/-
Copyright (c) 2026 the Stacks project formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.NumberTheory.Drinfeld.Shtuka.LevelGroup
public import StacksFrontier.NumberTheory.Drinfeld.Shtuka.BaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.NormalizedPullback

/-!
# Base change of level structures on shtukas

A level structure `ι : E|_{N ×_k S} ≅ 𝒪^r` on a shtuka `𝓔` over `S` pulls back along a morphism
`g : S' ⟶ S` to a level structure on the base-changed shtuka `(id_X × g)^* 𝓔` over `S'`: restrict
along `i × id_{S'}` the module `(id_X × g)^* E`, identify the result with `(id_N × g)^*` of the
restriction of `E` along `i × id_S` (both are the pullback along the diagonal of the square
`(i × id_{S'}) ≫ (id_X × g) = (id_N × g) ≫ (i × id_S)`), and apply `(id_N × g)^*` to `ι`. This
is the transport which makes `S ↦ {(𝓔, ι)}` a prestack `Sht_N` over `k`-schemes.

The Frobenius compatibility of the base-changed level structure is a coherence: the three
commuting squares formed by `i × id`, `τ` and `id × g` on the cube of products
`{N, X} × {S', S}` give two identifications of the two ways round the cube, and they agree
(`Stacks.Modules.pullbackSquareIso_cube`). It is proved by reading every square comparison as a
ratio of comparisons with the pullback along the long diagonal and applying the associativity
coherence `Stacks.Picard.pullbackCompEq_assoc`.

## Main definitions

* `Stacks.Drinfeld.Shtuka.leftMapBaseChangeIso` — `(i × id_{S'})^* (id_X × g)^* ≅
  (id_N × g)^* (i × id_S)^*`.
* `Stacks.Drinfeld.Shtuka.LevelStructure.baseChange` — the base change of a level structure.

## Main results

* `Stacks.Modules.pullbackSquareIso_hom_app_comp_pullbackCompEq` — a square comparison is the
  ratio of the two comparisons with the pullback along the diagonal.
* `Stacks.Modules.pullbackSquareIso_cube` — **the cube coherence** of square comparisons.
* `Stacks.Modules.pullbackSquareIso_hom_app_free` — square comparisons are compatible with the
  identifications `h^* 𝒪^I ≅ 𝒪^I`.
* `Stacks.Drinfeld.Shtuka.LevelStructure.baseChange_smul` — base change commutes with the action
  of the level group.

## References

* L. Lafforgue, *Chtoucas de Drinfeld et correspondance de Langlands*, Invent. Math. 147 (2002),
  §I.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Modules

open Stacks.Picard

section Ratio

variable {X X' S S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)

/-- **A square comparison is a ratio of diagonal comparisons.** For a commuting square
`g' ≫ f = f' ≫ g` with diagonal `e`, the comparison `f'^* g^* ≅ g'^* f^*` followed by the
identification of `g'^* f^*` with `e^*` is the identification of `f'^* g^*` with `e^*`. -/
@[reassoc]
theorem pullbackSquareIso_hom_app_comp_pullbackCompEq (w : g' ≫ f = f' ≫ g) (e : X' ⟶ S)
    (h₁ : f' ≫ g = e) (h₂ : g' ≫ f = e) (M : S.Modules) :
    (pullbackSquareIso f f' g g' w).hom.app M ≫ (pullbackCompEq g' f e h₂).hom.app M =
      (pullbackCompEq f' g e h₁).hom.app M := by
  subst h₁
  simp [pullbackSquareIso, pullbackCompEq, Scheme.Modules.pullbackCongr]

/-- **Pullbacks along equal morphisms identify free modules compatibly.** -/
@[reassoc]
theorem pullbackCongr_hom_app_free {a b : X' ⟶ S} (h : a = b) (I : Type u) :
    (Scheme.Modules.pullbackCongr h).hom.app (Stacks.Drinfeld.Shtuka.freeModule S I) ≫
        (Stacks.Drinfeld.Shtuka.pullbackFreeIso b I).hom =
      (Stacks.Drinfeld.Shtuka.pullbackFreeIso a I).hom := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

/-- **Square comparisons are compatible with the free identifications**: for a commuting square
`g' ≫ f = f' ≫ g`, the comparison `f'^* g^* 𝒪^I ≅ g'^* f^* 𝒪^I` followed by the free
identifications is the free identification of `f'^* g^* 𝒪^I`. -/
@[reassoc]
theorem pullbackSquareIso_hom_app_free (w : g' ≫ f = f' ≫ g) (I : Type u) :
    (pullbackSquareIso f f' g g' w).hom.app (Stacks.Drinfeld.Shtuka.freeModule S I) ≫
        (Scheme.Modules.pullback g').map (Stacks.Drinfeld.Shtuka.pullbackFreeIso f I).hom ≫
          (Stacks.Drinfeld.Shtuka.pullbackFreeIso g' I).hom =
      (Scheme.Modules.pullback f').map (Stacks.Drinfeld.Shtuka.pullbackFreeIso g I).hom ≫
        (Stacks.Drinfeld.Shtuka.pullbackFreeIso f' I).hom := by
  erw [← Scheme.Modules.pullbackComp_hom_app_free_comp_pullbackFreeIso_hom f' g I,
    ← Scheme.Modules.pullbackComp_hom_app_free_comp_pullbackFreeIso_hom g' f I,
    ← pullbackCongr_hom_app_free w.symm]
  simp [pullbackSquareIso]
  rfl

end Ratio

section Cube

variable {O A B C AB AC BC T : Scheme.{u}}
  (a₀ : O ⟶ A) (a_b : B ⟶ AB) (a_c : C ⟶ AC) (a_bc : BC ⟶ T)
  (b₀ : O ⟶ B) (b_a : A ⟶ AB) (b_c : C ⟶ BC) (b_ac : AC ⟶ T)
  (c₀ : O ⟶ C) (c_a : A ⟶ AC) (c_b : B ⟶ BC) (c_ab : AB ⟶ T)

/-- **The cube coherence of square comparisons.** Consider a commutative cube of schemes with
initial vertex `O`, final vertex `T` and edges in three directions `a`, `b`, `c` (the edge in
direction `a` out of the vertex `B` is `a_b`, and so on). Its six faces give square comparisons,
and the two chains of three of them from `a₀^* b_a^* c_ab^*` to `c₀^* b_c^* a_bc^*` (going round
the cube in the two senses) agree. -/
theorem pullbackSquareIso_cube
    (wab₀ : b₀ ≫ a_b = a₀ ≫ b_a) (wab_c : b_c ≫ a_bc = a_c ≫ b_ac)
    (wac₀ : c₀ ≫ a_c = a₀ ≫ c_a) (wac_b : c_b ≫ a_bc = a_b ≫ c_ab)
    (wbc₀ : c₀ ≫ b_c = b₀ ≫ c_b) (wbc_a : c_a ≫ b_ac = b_a ≫ c_ab) (M : T.Modules) :
    (Scheme.Modules.pullback a₀).map ((pullbackSquareIso b_ac b_a c_ab c_a wbc_a).hom.app M) ≫
        (pullbackSquareIso a_c a₀ c_a c₀ wac₀).hom.app ((Scheme.Modules.pullback b_ac).obj M) ≫
          (Scheme.Modules.pullback c₀).map
            ((pullbackSquareIso a_bc a_c b_ac b_c wab_c).hom.app M) =
      (pullbackSquareIso a_b a₀ b_a b₀ wab₀).hom.app ((Scheme.Modules.pullback c_ab).obj M) ≫
        (Scheme.Modules.pullback b₀).map
            ((pullbackSquareIso a_bc a_b c_ab c_b wac_b).hom.app M) ≫
          (pullbackSquareIso b_c b₀ c_b c₀ wbc₀).hom.app
            ((Scheme.Modules.pullback a_bc).obj M) := by
  have hd : c₀ ≫ b_c ≫ a_bc = a₀ ≫ b_a ≫ c_ab := by
    rw [wab_c, ← Category.assoc, wac₀, Category.assoc, wbc_a]
  have hd₁ : (c₀ ≫ a_c) ≫ b_ac = a₀ ≫ b_a ≫ c_ab := by rw [Category.assoc, ← wab_c, hd]
  have hd₂ : (b₀ ≫ a_b) ≫ c_ab = a₀ ≫ b_a ≫ c_ab := by rw [wab₀, Category.assoc]
  have hd₃ : b₀ ≫ c_b ≫ a_bc = a₀ ≫ b_a ≫ c_ab := by rw [wac_b, ← Category.assoc, hd₂]
  have hd₄ : (c₀ ≫ b_c) ≫ a_bc = a₀ ≫ b_a ≫ c_ab := by rw [Category.assoc, hd]
  apply (cancel_mono ((Scheme.Modules.pullback c₀).map
      ((pullbackCompEq b_c a_bc (b_c ≫ a_bc) rfl).hom.app M) ≫
        (pullbackCompEq c₀ (b_c ≫ a_bc) (a₀ ≫ b_a ≫ c_ab) hd).hom.app M)).1
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc,
    pullbackSquareIso_hom_app_comp_pullbackCompEq a_bc a_c b_ac b_c wab_c _ wab_c.symm rfl,
    pullbackCompEq_assoc c₀ a_c b_ac (b_c ≫ a_bc) (c₀ ≫ a_c) _ wab_c.symm rfl hd hd₁,
    pullbackSquareIso_hom_app_comp_pullbackCompEq_assoc a_c a₀ c_a c₀ wac₀ _ wac₀.symm rfl,
    ← pullbackCompEq_assoc a₀ c_a b_ac (b_a ≫ c_ab) (c₀ ≫ a_c) _ wbc_a wac₀.symm rfl hd₁,
    ← Functor.map_comp_assoc,
    pullbackSquareIso_hom_app_comp_pullbackCompEq b_ac b_a c_ab c_a wbc_a _ rfl wbc_a]
  rw [pullbackCompEq_assoc c₀ b_c a_bc (b_c ≫ a_bc) (c₀ ≫ b_c) _ rfl rfl hd hd₄,
    pullbackSquareIso_hom_app_comp_pullbackCompEq_assoc b_c b₀ c_b c₀ wbc₀ _ wbc₀.symm rfl,
    ← pullbackCompEq_assoc b₀ c_b a_bc (c_b ≫ a_bc) (c₀ ≫ b_c) _ rfl wbc₀.symm hd₃ hd₄,
    ← Functor.map_comp_assoc,
    pullbackSquareIso_hom_app_comp_pullbackCompEq a_bc a_b c_ab c_b wac_b _ wac_b.symm rfl,
    pullbackCompEq_assoc b₀ a_b c_ab (c_b ≫ a_bc) (b₀ ≫ a_b) _ wac_b.symm rfl hd₃ hd₂,
    pullbackSquareIso_hom_app_comp_pullbackCompEq_assoc a_b a₀ b_a b₀ wab₀ _ wab₀.symm rfl,
    ← pullbackCompEq_assoc a₀ b_a c_ab (b_a ≫ c_ab) (b₀ ≫ a_b) _ rfl wab₀.symm rfl hd₂]

end Cube

end Stacks.Modules

namespace Stacks.Drinfeld.Shtuka

open Stacks.Modules

variable {k : Type u} [Field k] [Fintype k] {p f : ℕ} [Fact p.Prime] [CharP k p]
  {hcard : Fintype.card k = p ^ f} {X S S' N : Over (Spec (.of k))} {r : ℕ}

omit [Fintype k] in
/-- `i × id` commutes with base change: `(i × id_{S'}) ≫ (id_X × g) = (id_N × g) ≫ (i × id_S)`. -/
theorem leftMap_comp_productMap (i : N ⟶ X) (g : S' ⟶ S) :
    leftMap (S := S') i ≫ productMap g = productMap g ≫ leftMap (S := S) i := by
  apply pullback.hom_ext
  · simp only [Category.assoc, productMap_fst, leftMap_fst, productMap_fst_assoc]
  · simp only [Category.assoc, productMap_snd, leftMap_snd, leftMap_snd_assoc, productMap_snd]

/-- The natural isomorphism `(i × id_{S'})^* (id_X × g)^* ≅ (id_N × g)^* (i × id_S)^*`. -/
abbrev leftMapBaseChangeIso (i : N ⟶ X) (g : S' ⟶ S) :
    Scheme.Modules.pullback (productMap g) ⋙ Scheme.Modules.pullback (leftMap (S := S') i) ≅
      Scheme.Modules.pullback (leftMap (S := S) i) ⋙ Scheme.Modules.pullback (productMap g) :=
  pullbackSquareIso (leftMap i) (leftMap i) (productMap g) (productMap g)
    (leftMap_comp_productMap i g).symm

/-- `restrictFrobeniusTwistIso` is the square comparison isomorphism of the square formed by
`i × id_S` and the Frobenius twists of `X × S` and `N × S`. -/
theorem restrictFrobeniusTwistIso_eq (i : N ⟶ X) :
    restrictFrobeniusTwistIso p f hcard (S := S) i =
      pullbackSquareIso (leftMap i) (leftMap i) (frobeniusTwist p f hcard X S)
        (frobeniusTwist p f hcard N S) (frobeniusTwist_comp_leftMap p f hcard i) := rfl

/-- `frobeniusTwistBaseChangeIso` is the square comparison isomorphism of the square formed by
`id_Y × g` and the Frobenius twists of `Y × S` and `Y × S'`. -/
theorem frobeniusTwistBaseChangeIso_eq (Y : Over (Spec (.of k))) (g : S' ⟶ S) :
    frobeniusTwistBaseChangeIso p f hcard Y g =
      pullbackSquareIso (frobeniusTwist p f hcard Y S) (frobeniusTwist p f hcard Y S')
        (productMap g) (productMap g) (frobeniusTwist_comp_productMap p f hcard g).symm := rfl

namespace LevelStructure

variable [IsSeparated X.hom] {𝓔 : Shtuka p f hcard X S r} {i : N ⟶ X}

/-- **Base change of a level structure** along `g : S' ⟶ S`: the level structure
`(id_N × g)^* ι` on the base-changed shtuka `(id_X × g)^* 𝓔`, read through
`(i × id_{S'})^* (id_X × g)^* ≅ (id_N × g)^* (i × id_S)^*` and `(id_N × g)^* 𝒪^r ≅ 𝒪^r`. -/
def baseChange (g : S' ⟶ S) (ℓ : LevelStructure 𝓔 i) : LevelStructure (𝓔.baseChange g) i where
  ι := (leftMapBaseChangeIso i g).app 𝓔.E ≪≫
    (Scheme.Modules.pullback (productMap g)).mapIso ℓ.ι ≪≫ pullbackFreeIso _ _
  ι' := (leftMapBaseChangeIso i g).app 𝓔.E' ≪≫
    (Scheme.Modules.pullback (productMap g)).mapIso ℓ.ι' ≪≫ pullbackFreeIso _ _
  j_comp := by
    have hnat := (leftMapBaseChangeIso i g).hom.naturality 𝓔.j
    dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
    dsimp only [Shtuka.baseChange]
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    rw [reassoc_of% hnat, ← Functor.map_comp_assoc, ℓ.j_comp]
  t_comp := by
    have hnat := (leftMapBaseChangeIso i g).hom.naturality 𝓔.t
    dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
    have hnatN := (frobeniusTwistBaseChangeIso p f hcard N g).hom.naturality ℓ.ι.hom
    dsimp only [Functor.comp_obj, Functor.comp_map] at hnatN
    have hcube := pullbackSquareIso_cube
      (leftMap (S := S') i) (leftMap (S := S') i) (leftMap (S := S) i) (leftMap (S := S) i)
      (frobeniusTwist p f hcard N S') (frobeniusTwist p f hcard X S')
      (frobeniusTwist p f hcard N S) (frobeniusTwist p f hcard X S)
      (productMap g) (productMap g) (productMap g) (productMap g)
      (frobeniusTwist_comp_leftMap p f hcard i) (frobeniusTwist_comp_leftMap p f hcard i)
      (leftMap_comp_productMap i g).symm (leftMap_comp_productMap i g).symm
      (frobeniusTwist_comp_productMap p f hcard g).symm
      (frobeniusTwist_comp_productMap p f hcard g).symm 𝓔.E
    have hfree := pullbackSquareIso_hom_app_free (frobeniusTwist p f hcard N S)
      (frobeniusTwist p f hcard N S') (productMap g) (productMap g)
      (frobeniusTwist_comp_productMap p f hcard g).symm (ULift.{u} (Fin r))
    rw [← frobeniusTwistBaseChangeIso_eq, ← restrictFrobeniusTwistIso_eq,
      ← restrictFrobeniusTwistIso_eq, ← frobeniusTwistBaseChangeIso_eq] at hcube
    rw [← frobeniusTwistBaseChangeIso_eq] at hfree
    dsimp only [Shtuka.baseChange]
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    rw [reassoc_of% hnat, ← Functor.map_comp_assoc (Scheme.Modules.pullback (productMap g)),
      ℓ.t_comp]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hcube, ← reassoc_of% hnatN, hfree]

/-- The isomorphism `ι` of the base change of `ℓ` along `g` is the composite of the base change
isomorphism for `i × id`, the pullback of `ℓ.ι` along `id_N × g`, and `pullbackFreeIso`. -/
@[simp]
theorem baseChange_ι (g : S' ⟶ S) (ℓ : LevelStructure 𝓔 i) :
    (ℓ.baseChange g).ι = (leftMapBaseChangeIso i g).app 𝓔.E ≪≫
      (Scheme.Modules.pullback (productMap g)).mapIso ℓ.ι ≪≫ pullbackFreeIso _ _ := rfl

/-- The isomorphism `ι'` of the base change of `ℓ` along `g` is the composite of the base change
isomorphism for `i × id`, the pullback of `ℓ.ι'` along `id_N × g`, and `pullbackFreeIso`. -/
@[simp]
theorem baseChange_ι' (g : S' ⟶ S) (ℓ : LevelStructure 𝓔 i) :
    (ℓ.baseChange g).ι' = (leftMapBaseChangeIso i g).app 𝓔.E' ≪≫
      (Scheme.Modules.pullback (productMap g)).mapIso ℓ.ι' ≪≫ pullbackFreeIso _ _ := rfl

/-- **Base change commutes with the level group action**: for `a ∈ Aut(𝒪_N^r)`, the base change
of `a • ℓ` is `a • ` the base change of `ℓ`, because `(id_N × g)^* pr_N^* a = pr_N^* a`. -/
theorem baseChange_smul (g : S' ⟶ S) (a : Aut (freeModule N.left (ULift.{u} (Fin r))))
    (ℓ : LevelStructure 𝓔 i) : (a • ℓ).baseChange g = a • ℓ.baseChange g := by
  ext : 1 <;> refine Iso.ext ?_ <;>
    simp only [baseChange_ι, baseChange_ι', smul_ι, smul_ι', Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, Functor.map_comp, Category.assoc, levelAut_hom] <;>
    rw [pullback_map_pullbackFreeEnd, productMap_fst] <;> rfl

end LevelStructure

end Stacks.Drinfeld.Shtuka
