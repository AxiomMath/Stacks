/-
Copyright (c) 2026 the Stacks project formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.NumberTheory.Drinfeld.Shtuka.LevelStructure
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.PullbackFreeIsoComp

/-!
# The level group acts on level structures of shtukas

Let `i : N ⟶ X` be a level (in the application, a finite closed subscheme `N` of the curve `X`)
and `𝓔` a shtuka of rank `r` over `S`. The *level group* is the automorphism group
`Aut(𝒪_N^r)` of the free `𝒪_N`-module of rank `r`, that is `GL_r(Γ(N, 𝒪_N))`; for `N` the
closed subscheme of an effective divisor `D` it is `GL_r(O_D)`, the quotient of `GL_r(O)` whose
action on `Sht_N` makes `Sht_N ⟶ Sht` a `GL_r(O_D)`-torsor over the locus where the legs avoid
`N` (Drinfeld).

An automorphism `g` of `𝒪_N^r` acts on a level structure `ι : E|_{N ×_k S} ≅ 𝒪^r` through its
pullback `pr_N^* g` to `N ×_k S`. The compatibility of the level structure with the Frobenius
`τ = id_N × Frob_S` survives because `pr_N^* g` is *constant along `S`*: since
`τ ≫ pr_N = pr_N`, the pullback of `pr_N^* g` along `τ` is again `pr_N^* g`.

## Main definitions

* `Stacks.Drinfeld.Shtuka.pullbackFreeEnd` — the pullback `h^* g` of an endomorphism `g` of a
  free module, read as an endomorphism of the free module through
  `Stacks.Drinfeld.Shtuka.pullbackFreeIso`.
* `Stacks.Drinfeld.Shtuka.pullbackFreeAut` — the group homomorphism
  `Aut(𝒪_Z^I) →* Aut(𝒪_Y^I)` it induces.
* `Stacks.Drinfeld.Shtuka.LevelStructure.instMulAction` — the action of the level group
  `Aut(𝒪_N^r)` on the level structures of a shtuka.

## Main results

* `Stacks.Drinfeld.Shtuka.pullback_map_pullbackFreeEnd` — pulling back once more:
  `a^* (h^* g) = (a ≫ h)^* g` through the free identifications.
* `Stacks.Drinfeld.Shtuka.LevelStructure.ofHom_smul` — the action commutes with pulling back level
  structures along morphisms of shtukas.

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

section FreeEnd

variable {W Y Z : Scheme.{u}} {I : Type u}

/-- The pullback `h^* g` of an endomorphism `g` of the free module `𝒪_Z^I` along `h : Y ⟶ Z`, as
an endomorphism of `𝒪_Y^I` through the identification `h^* 𝒪_Z^I ≅ 𝒪_Y^I`. -/
def pullbackFreeEnd (h : Y ⟶ Z) (g : freeModule Z I ⟶ freeModule Z I) :
    freeModule Y I ⟶ freeModule Y I :=
  (pullbackFreeIso h I).inv ≫ (Scheme.Modules.pullback h).map g ≫
    (pullbackFreeIso h I).hom

/-- The pullback of the identity endomorphism is the identity. -/
@[simp]
theorem pullbackFreeEnd_id (h : Y ⟶ Z) :
    pullbackFreeEnd h (𝟙 (freeModule Z I)) = 𝟙 _ := by
  simp [pullbackFreeEnd]

/-- Pulling back endomorphisms of a free module respects composition. -/
theorem pullbackFreeEnd_comp (h : Y ⟶ Z) (g g' : freeModule Z I ⟶ freeModule Z I) :
    pullbackFreeEnd h (g ≫ g') = pullbackFreeEnd h g ≫ pullbackFreeEnd h g' := by
  simp [pullbackFreeEnd]

/-- Through `h^* 𝒪_Z^I ≅ 𝒪_Y^I`, the pullback `h^* g` of an endomorphism `g` corresponds to
`(Scheme.Modules.pullback h).map g`. -/
@[reassoc]
theorem pullbackFreeIso_hom_comp_pullbackFreeEnd (h : Y ⟶ Z)
    (g : freeModule Z I ⟶ freeModule Z I) :
    (pullbackFreeIso h I).hom ≫ pullbackFreeEnd h g =
      (Scheme.Modules.pullback h).map g ≫ (pullbackFreeIso h I).hom := by
  simp [pullbackFreeEnd]

/-- **Pulling back a pulled-back endomorphism of a free module.** Through the free
identifications, `a^* (h^* g) = (a ≫ h)^* g`. -/
@[reassoc]
theorem pullback_map_pullbackFreeEnd (a : W ⟶ Y) (h : Y ⟶ Z)
    (g : freeModule Z I ⟶ freeModule Z I) :
    (Scheme.Modules.pullback a).map (pullbackFreeEnd h g) ≫
        (pullbackFreeIso a I).hom =
      (pullbackFreeIso a I).hom ≫ pullbackFreeEnd (a ≫ h) g := by
  have hc : (Scheme.Modules.pullbackComp a h).hom.app (freeModule Z I) ≫
      (pullbackFreeIso (a ≫ h) I).hom =
        (Scheme.Modules.pullback a).map (pullbackFreeIso h I).hom ≫ (pullbackFreeIso a I).hom :=
    Scheme.Modules.pullbackComp_hom_app_free_comp_pullbackFreeIso_hom a h I
  have hnat := (Scheme.Modules.pullbackComp a h).hom.naturality g
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
  have hc' : (Scheme.Modules.pullback a).map (pullbackFreeIso h I).inv ≫
      (Scheme.Modules.pullbackComp a h).hom.app (freeModule Z I) =
        (pullbackFreeIso a I).hom ≫ (pullbackFreeIso (a ≫ h) I).inv := by
    rw [← cancel_epi ((Scheme.Modules.pullback a).map (pullbackFreeIso h I).hom),
      ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
      ← reassoc_of% hc, Iso.hom_inv_id, Category.comp_id]
  simp only [pullbackFreeEnd, Functor.map_comp, Category.assoc]
  rw [← hc, reassoc_of% hnat, reassoc_of% hc']

/-- The pullback of an automorphism of a free module, as an automorphism of the free module. -/
def pullbackFreeAut (h : Y ⟶ Z) : Aut (freeModule Z I) →* Aut (freeModule Y I) where
  toFun g :=
    { hom := pullbackFreeEnd h g.hom
      inv := pullbackFreeEnd h g.inv
      hom_inv_id := by rw [← pullbackFreeEnd_comp, g.hom_inv_id, pullbackFreeEnd_id]
      inv_hom_id := by rw [← pullbackFreeEnd_comp, g.inv_hom_id, pullbackFreeEnd_id] }
  map_one' := Iso.ext (pullbackFreeEnd_id h)
  map_mul' g g' := Iso.ext (pullbackFreeEnd_comp h g'.hom g.hom)

/-- The underlying endomorphism of the pullback of an automorphism `g` is `h^* g.hom`. -/
@[simp]
theorem pullbackFreeAut_hom (h : Y ⟶ Z) (g : Aut (freeModule Z I)) :
    (pullbackFreeAut h g).hom = pullbackFreeEnd h g.hom := rfl

end FreeEnd

variable {k : Type u} [Field k] [Fintype k] {p f : ℕ} [Fact p.Prime] [CharP k p]
  {hcard : Fintype.card k = p ^ f} {X S N : Over (Spec (.of k))} {r : ℕ}

/-- The automorphism `pr_N^* g` of `𝒪^r` on `N ×_k S` attached to an element `g` of the level
group `Aut(𝒪_N^r)`. -/
def levelAut (S : Over (Spec (.of k))) (g : Aut (freeModule N.left (ULift.{u} (Fin r)))) :
    freeModule (product N S) (ULift.{u} (Fin r)) ≅ freeModule (product N S) (ULift.{u} (Fin r)) :=
  pullbackFreeAut (pullback.fst N.hom S.hom) g

omit [Fintype k] in
/-- The underlying endomorphism of `levelAut S g` is `pr_N^* g.hom`. -/
@[simp]
theorem levelAut_hom (S : Over (Spec (.of k))) (g : Aut (freeModule N.left (ULift.{u} (Fin r)))) :
    (levelAut S g).hom = pullbackFreeEnd (pullback.fst N.hom S.hom) g.hom := rfl

variable (p f hcard) in
/-- **Elements of the level group are constant along `S`**: the pullback along
`τ = id_N × Frob_S` of `pr_N^* g` is `pr_N^* g`, through `τ^* 𝒪^r ≅ 𝒪^r`. -/
@[reassoc]
theorem pullback_frobeniusTwist_map_levelAut (g : Aut (freeModule N.left (ULift.{u} (Fin r)))) :
    (Scheme.Modules.pullback (frobeniusTwist p f hcard N S)).map (levelAut S g).hom ≫
        (pullbackFreeIso _ _).hom =
      (pullbackFreeIso _ _).hom ≫ (levelAut S g).hom := by
  rw [levelAut_hom, pullback_map_pullbackFreeEnd, frobeniusTwist_fst]

namespace LevelStructure

variable {𝓔 𝓕 : Shtuka p f hcard X S r} {i : N ⟶ X}

/-- Two level structures are equal when their isomorphisms `ι` and `ι'` are. -/
@[ext]
theorem ext {ℓ ℓ' : LevelStructure 𝓔 i} (h : ℓ.ι = ℓ'.ι) (h' : ℓ.ι' = ℓ'.ι') : ℓ = ℓ' := by
  cases ℓ
  cases ℓ'
  cases h
  cases h'
  rfl

/-- **The level group acts on level structures**: `g ∈ Aut(𝒪_N^r)` sends `(ι, ι')` to
`(pr_N^* g ∘ ι, pr_N^* g ∘ ι')`. -/
instance instMulAction :
    MulAction (Aut (freeModule N.left (ULift.{u} (Fin r)))) (LevelStructure 𝓔 i) where
  smul g ℓ :=
    { ι := ℓ.ι ≪≫ levelAut S g
      ι' := ℓ.ι' ≪≫ levelAut S g
      j_comp := by simp only [Iso.trans_hom, ← Category.assoc, ℓ.j_comp]
      t_comp := by
        simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
        rw [reassoc_of% ℓ.t_comp, pullback_frobeniusTwist_map_levelAut] }
  one_smul ℓ := by
    ext : 1 <;> refine Iso.ext ?_ <;>
      exact (congrArg (_ ≫ ·) (pullbackFreeEnd_id _)).trans (Category.comp_id _)
  mul_smul g g' ℓ := by
    ext : 1 <;> refine Iso.ext ?_ <;>
      exact (congrArg (_ ≫ ·) (pullbackFreeEnd_comp _ g'.hom g.hom)).trans
        (Category.assoc _ _ _).symm

/-- The isomorphism `ι` of `g • ℓ` is `ℓ.ι` followed by `pr_N^* g`. -/
@[simp]
theorem smul_ι (g : Aut (freeModule N.left (ULift.{u} (Fin r)))) (ℓ : LevelStructure 𝓔 i) :
    (g • ℓ).ι = ℓ.ι ≪≫ levelAut S g := rfl

/-- The isomorphism `ι'` of `g • ℓ` is `ℓ.ι'` followed by `pr_N^* g`. -/
@[simp]
theorem smul_ι' (g : Aut (freeModule N.left (ULift.{u} (Fin r)))) (ℓ : LevelStructure 𝓔 i) :
    (g • ℓ).ι' = ℓ.ι' ≪≫ levelAut S g := rfl

/-- **The level group action commutes with pulling back level structures** along morphisms of
shtukas which are isomorphisms over `N ×_k S`. -/
theorem ofHom_smul (α : 𝓔 ⟶ 𝓕) [IsIso ((Scheme.Modules.pullback (leftMap i)).map α.hom)]
    [IsIso ((Scheme.Modules.pullback (leftMap i)).map α.hom')]
    (g : Aut (freeModule N.left (ULift.{u} (Fin r)))) (ℓ : LevelStructure 𝓕 i) :
    ofHom α (g • ℓ) = g • ofHom α ℓ := by
  ext : 1 <;> exact (Iso.trans_assoc (asIso _) _ _).symm

end LevelStructure

end Stacks.Drinfeld.Shtuka
