module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Base change for right adjoints of the vertical functors of a square of adjunctions

Consider four categories and functors

```
        Lg'                     Rg'
   DX ------> DX'          DX <------ DX'
   |  ^        |  ^
 Rf|  |a    Rf'|  |a'
   v  |        v  |
   DY ------> DY'          DY <------ DY'
        Lg                      Rg
```

with adjunctions `Lg ⊣ Rg`, `Lg' ⊣ Rg'`, `Rf ⊣ a`, `Rf' ⊣ a'` and a base change
transformation `β : Rf ⋙ Lg ⟶ Lg' ⋙ Rf'`, i.e. `Lg ∘ Rf ⟶ Rf' ∘ Lg'`. This is the shape of
Stacks 0E5B: `Rf`, `Rf'` are derived pushforwards along the vertical arrows of a cartesian square,
`a`, `a'` their right adjoints, `Lg`, `Lg'` derived pullbacks along the horizontal arrows.

The transformation `β` has a mate `ξ : Rg' ∘ a' ⟶ a ∘ Rg` between the composite right adjoints.
When `ξ` is invertible, the composite

`Lg' ∘ a ⟶ Lg' ∘ a ∘ Rg ∘ Lg ⟵ Lg' ∘ Rg' ∘ a' ∘ Lg ⟶ a' ∘ Lg`

of the unit of `Lg ⊣ Rg`, the inverse of `ξ` and the counit of `Lg' ⊣ Rg'` is the base change
map `α : Lg' ∘ a ⟶ a' ∘ Lg` of Stacks 0E5D. The trace `Rf ∘ a ⟶ 1` and the unit `1 ⟶ a ∘ Rf`
are compatible with `α` and `β` (Stacks 0E5L and 0E5M); these are statements about adjunctions
alone and are proved here.

## Main definitions

* `CategoryTheory.RightAdjointBaseChange.rightAdjointMate`: the mate `ξ : Rg' ∘ a' ⟶ a ∘ Rg`.
* `CategoryTheory.RightAdjointBaseChange.map`: the base change map `α : Lg' ∘ a ⟶ a' ∘ Lg`.

## Main results

* `CategoryTheory.RightAdjointBaseChange.map_counit`: `Lg ⋆ Tr_f` agrees with
  `(Tr_{f'} ⋆ Lg) ∘ (Rf' ⋆ α) ∘ (β ⋆ a)`.
* `CategoryTheory.RightAdjointBaseChange.unit_map`: `(a' ⋆ β) ∘ (α ⋆ Rf) ∘ (Lg' ⋆ η_f)` is
  `η_{f'} ⋆ Lg'`.
* `CategoryTheory.RightAdjointBaseChange.map_app_horizontal` and
  `CategoryTheory.RightAdjointBaseChange.map_app_vertical`: the base change maps of two squares
  sharing an edge compose to that of the rectangle (the abstract content of Stacks 0E5F and
  0E5E).
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.RightAdjointBaseChange

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {DX : Type u₁} {DY : Type u₂} {DX' : Type u₃} {DY' : Type u₄}
  [Category.{v₁} DX] [Category.{v₂} DY] [Category.{v₃} DX'] [Category.{v₄} DY']
  {Rf : DX ⥤ DY} {a : DY ⥤ DX} {Rf' : DX' ⥤ DY'} {a' : DY' ⥤ DX'}
  {Lg : DY ⥤ DY'} {Rg : DY' ⥤ DY} {Lg' : DX ⥤ DX'} {Rg' : DX' ⥤ DX}
  (adjF : Rf ⊣ a) (adjF' : Rf' ⊣ a') (adjG : Lg ⊣ Rg) (adjG' : Lg' ⊣ Rg')
  (β : Rf ⋙ Lg ⟶ Lg' ⋙ Rf')

/-- The mate `ξ : Rg' ∘ a' ⟶ a ∘ Rg` of the base change transformation `β : Lg ∘ Rf ⟶ Rf' ∘ Lg'`
under the composite adjunctions `Rf' ∘ Lg' ⊣ Rg' ∘ a'` and `Lg ∘ Rf ⊣ a ∘ Rg`. -/
def rightAdjointMate : a' ⋙ Rg' ⟶ Rg ⋙ a :=
  conjugateEquiv (adjG'.comp adjF') (adjF.comp adjG) β

/-- The mate of an invertible base change transformation is invertible. -/
instance isIso_rightAdjointMate [IsIso β] : IsIso (rightAdjointMate adjF adjF' adjG adjG' β) := by
  unfold rightAdjointMate
  infer_instance

/-- The defining property of the mate: `Lg ∘ Rf` of `ξ` followed by the counit of
`Lg ∘ Rf ⊣ a ∘ Rg` is `β` followed by the counit of `Rf' ∘ Lg' ⊣ Rg' ∘ a'`. -/
theorem map_rightAdjointMate_app_comp_counit (K : DY') :
    Lg.map (Rf.map ((rightAdjointMate adjF adjF' adjG adjG' β).app K)) ≫
        Lg.map (adjF.counit.app (Rg.obj K)) ≫ adjG.counit.app K =
      β.app (Rg'.obj (a'.obj K)) ≫ Rf'.map (adjG'.counit.app (a'.obj K)) ≫
        adjF'.counit.app K := by
  have h := conjugateEquiv_counit (adjG'.comp adjF') (adjF.comp adjG) β K
  simpa [rightAdjointMate] using h

/-- The unit of `Rf' ∘ Lg' ⊣ Rg' ∘ a'` followed by `ξ` is the unit of `Lg ∘ Rf ⊣ a ∘ Rg`
followed by `a ∘ Rg` of `β`. -/
theorem unit_comp_rightAdjointMate_app (K : DX) :
    adjG'.unit.app K ≫ Rg'.map (adjF'.unit.app (Lg'.obj K)) ≫
        (rightAdjointMate adjF adjF' adjG adjG' β).app (Rf'.obj (Lg'.obj K)) =
      adjF.unit.app K ≫ a.map (adjG.unit.app (Rf.obj K)) ≫ a.map (Rg.map (β.app K)) := by
  have h := unit_conjugateEquiv (adjG'.comp adjF') (adjF.comp adjG) β K
  simpa [rightAdjointMate] using h

variable [IsIso (rightAdjointMate adjF adjF' adjG adjG' β)]

/-- **The base change map `α : Lg' ∘ a ⟶ a' ∘ Lg`** (Stacks 0E5D), the composite of the unit of
`Lg ⊣ Rg`, the inverse of the mate `ξ : Rg' ∘ a' ⟶ a ∘ Rg`, and the counit of `Lg' ⊣ Rg'`. -/
def map : a ⋙ Lg' ⟶ Lg ⋙ a' :=
  Functor.whiskerRight (a.leftUnitor.inv ≫ Functor.whiskerRight adjG.unit a) Lg' ≫
    Functor.whiskerRight ((Functor.associator Lg Rg a).hom ≫
        Functor.whiskerLeft Lg (inv (rightAdjointMate adjF adjF' adjG adjG' β)) ≫
        (Functor.associator Lg a' Rg').inv) Lg' ≫
    ((Functor.associator (Lg ⋙ a') Rg' Lg').hom ≫
      Functor.whiskerLeft (Lg ⋙ a') adjG'.counit ≫ (Lg ⋙ a').rightUnitor.hom)

/-- The component of the base change map `α` at `K` is `Lg'` of `a` of the unit of `Lg ⊣ Rg`,
followed by `Lg'` of the inverse of `ξ` at `Lg K` and the counit of `Lg' ⊣ Rg'` at `a' (Lg K)`. -/
theorem map_app (K : DY) :
    (map adjF adjF' adjG adjG' β).app K =
      Lg'.map (a.map (adjG.unit.app K)) ≫
        Lg'.map ((inv (rightAdjointMate adjF adjF' adjG adjG' β)).app (Lg.obj K)) ≫
        adjG'.counit.app (a'.obj (Lg.obj K)) := by
  simp [map]

/-- **Trace and base change** (the abstract content of Stacks 0E5L): `Lg` of the trace
`Rf (a K) ⟶ K` equals `β` at `a K`, followed by `Rf'` of the base change map `α` and the trace
`Rf' (a' (Lg K)) ⟶ Lg K`. -/
theorem map_counit (K : DY) :
    β.app (a.obj K) ≫ Rf'.map ((map adjF adjF' adjG adjG' β).app K) ≫
        adjF'.counit.app (Lg.obj K) =
      Lg.map (adjF.counit.app K) := by
  let ξ := rightAdjointMate adjF adjF' adjG adjG' β
  have hβ₁ : Lg.map (Rf.map (a.map (adjG.unit.app K))) ≫ β.app (a.obj (Rg.obj (Lg.obj K))) =
      β.app (a.obj K) ≫ Rf'.map (Lg'.map (a.map (adjG.unit.app K))) :=
    β.naturality (a.map (adjG.unit.app K))
  have hβ₂ : Lg.map (Rf.map ((inv ξ).app (Lg.obj K))) ≫ β.app (Rg'.obj (a'.obj (Lg.obj K))) =
      β.app (a.obj (Rg.obj (Lg.obj K))) ≫ Rf'.map (Lg'.map ((inv ξ).app (Lg.obj K))) :=
    β.naturality ((inv ξ).app (Lg.obj K))
  have hξ := map_rightAdjointMate_app_comp_counit adjF adjF' adjG adjG' β (Lg.obj K)
  have hT : Rf.map (a.map (adjG.unit.app K)) ≫ adjF.counit.app (Rg.obj (Lg.obj K)) =
      adjF.counit.app K ≫ adjG.unit.app K :=
    adjF.counit.naturality (adjG.unit.app K)
  have e : ∀ {Z : DY'} (h : Lg.obj (Rf.obj (a.obj (Rg.obj (Lg.obj K)))) ⟶ Z),
      Lg.map (Rf.map ((inv ξ).app (Lg.obj K))) ≫ Lg.map (Rf.map (ξ.app (Lg.obj K))) ≫ h = h := by
    intro Z h
    rw [← Lg.map_comp_assoc, ← Rf.map_comp, ← NatTrans.comp_app, IsIso.inv_hom_id,
      NatTrans.id_app, Rf.map_id, Lg.map_id, Category.id_comp]
  rw [map_app, Rf'.map_comp, Rf'.map_comp, Category.assoc, Category.assoc,
    ← reassoc_of% hβ₁, ← reassoc_of% hβ₂, ← hξ, e, ← Lg.map_comp_assoc, hT,
    Lg.map_comp_assoc]
  simp

/-- **Unit and base change** (the abstract content of Stacks 0E5M): `Lg'` of the unit
`K ⟶ a (Rf K)`, followed by the base change map `α` at `Rf K` and by `a'` of `β`, is the unit
`Lg' K ⟶ a' (Rf' (Lg' K))`. -/
theorem unit_map (K : DX) :
    Lg'.map (adjF.unit.app K) ≫ (map adjF adjF' adjG adjG' β).app (Rf.obj K) ≫
        a'.map (β.app K) =
      adjF'.unit.app (Lg'.obj K) := by
  let ξ := rightAdjointMate adjF adjF' adjG adjG' β
  have hε : adjG'.counit.app (a'.obj (Lg.obj (Rf.obj K))) ≫ a'.map (β.app K) =
      Lg'.map (Rg'.map (a'.map (β.app K))) ≫ adjG'.counit.app (a'.obj (Rf'.obj (Lg'.obj K))) :=
    (adjG'.counit.naturality (a'.map (β.app K))).symm
  have hξ : a.map (Rg.map (β.app K)) ≫ (inv ξ).app (Rf'.obj (Lg'.obj K)) =
      (inv ξ).app (Lg.obj (Rf.obj K)) ≫ Rg'.map (a'.map (β.app K)) :=
    (inv ξ).naturality (β.app K)
  have hu := unit_comp_rightAdjointMate_app adjF adjF' adjG adjG' β K
  have key : adjF.unit.app K ≫ a.map (adjG.unit.app (Rf.obj K)) ≫
      (inv ξ).app (Lg.obj (Rf.obj K)) ≫ Rg'.map (a'.map (β.app K)) =
      adjG'.unit.app K ≫ Rg'.map (adjF'.unit.app (Lg'.obj K)) := by
    rw [← hξ, ← reassoc_of% hu]
    simp [ξ]
  have hε' : Lg'.map (Rg'.map (adjF'.unit.app (Lg'.obj K))) ≫
      adjG'.counit.app (a'.obj (Rf'.obj (Lg'.obj K))) =
      adjG'.counit.app (Lg'.obj K) ≫ adjF'.unit.app (Lg'.obj K) :=
    adjG'.counit.naturality (adjF'.unit.app (Lg'.obj K))
  rw [map_app, Category.assoc, Category.assoc, hε]
  have := congrArg Lg'.map key
  simp only [Functor.map_comp] at this
  simp only [← Category.assoc] at this ⊢
  rw [this]
  simp only [Category.assoc]
  rw [hε']
  simp

/-- **The base change map on Yoneda functors**: when `β` is invertible, `α` at `K` is the
morphism `Lg' (a K) ⟶ a' (Lg K)` corresponding under `Rf' ⊣ a'` to the inverse of `β` at `a K`
followed by `Lg` of the trace `Rf (a K) ⟶ K`. This is the description of Stacks 0E5D on
`Hom(-, a(K))`, and it determines `α`. -/
theorem map_app_eq_homEquiv [IsIso β] (K : DY) :
    (map adjF adjF' adjG adjG' β).app K =
      adjF'.homEquiv _ _ (inv (β.app (a.obj K)) ≫ Lg.map (adjF.counit.app K)) := by
  rw [← map_counit adjF adjF' adjG adjG' β K, IsIso.inv_hom_id_assoc]
  exact ((adjF'.homEquiv _ _).apply_symm_apply _).symm

/-- `α` is the unique morphism whose transpose under `Rf' ⊣ a'`, precomposed with `β`, is `Lg` of
the trace: a morphism `φ : Lg' (a K) ⟶ a' (Lg K)` with
`β (a K) ≫ Rf' φ ≫ Tr_{f'} (Lg K) = Lg (Tr_f K)` is `α` at `K`. -/
theorem eq_map_app_of_counit [IsIso β] (K : DY) (φ : Lg'.obj (a.obj K) ⟶ a'.obj (Lg.obj K))
    (hφ : β.app (a.obj K) ≫ Rf'.map φ ≫ adjF'.counit.app (Lg.obj K) =
      Lg.map (adjF.counit.app K)) :
    φ = (map adjF adjF' adjG adjG' β).app K := by
  rw [map_app_eq_homEquiv, ← hφ, IsIso.inv_hom_id_assoc]
  exact ((adjF'.homEquiv _ _).apply_symm_apply _).symm

end CategoryTheory.RightAdjointBaseChange

namespace CategoryTheory.RightAdjointBaseChange

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

/-! ### Pasting along a vertical edge (the abstract content of Stacks 0E5F) -/

section Horizontal

variable {DX : Type u₁} {DY : Type u₂} {DX' : Type u₃} {DY' : Type u₄} {DX'' : Type u₅}
  {DY'' : Type u₆} [Category.{v₁} DX] [Category.{v₂} DY] [Category.{v₃} DX'] [Category.{v₄} DY']
  [Category.{v₅} DX''] [Category.{v₆} DY'']
  {Rf : DX ⥤ DY} {a : DY ⥤ DX} {Rf' : DX' ⥤ DY'} {a' : DY' ⥤ DX'}
  {Rf'' : DX'' ⥤ DY''} {a'' : DY'' ⥤ DX''}
  {Lh : DY ⥤ DY'} {Rh : DY' ⥤ DY} {Lg : DX ⥤ DX'} {Rg : DX' ⥤ DX}
  {Lh' : DY' ⥤ DY''} {Rh' : DY'' ⥤ DY'} {Lg' : DX' ⥤ DX''} {Rg' : DX'' ⥤ DX'}
  {Lm : DY ⥤ DY''} {Rm : DY'' ⥤ DY} {Lk : DX ⥤ DX''} {Rk : DX'' ⥤ DX}
  (adjF : Rf ⊣ a) (adjF' : Rf' ⊣ a') (adjF'' : Rf'' ⊣ a'')
  (adjH : Lh ⊣ Rh) (adjG : Lg ⊣ Rg) (adjH' : Lh' ⊣ Rh') (adjG' : Lg' ⊣ Rg')
  (adjM : Lm ⊣ Rm) (adjK : Lk ⊣ Rk)
  (β₁ : Rf ⋙ Lh ⟶ Lg ⋙ Rf') (β₂ : Rf' ⋙ Lh' ⟶ Lg' ⋙ Rf'') (β : Rf ⋙ Lm ⟶ Lk ⋙ Rf'')
  (em : Lh ⋙ Lh' ≅ Lm) (ek : Lg ⋙ Lg' ≅ Lk)
  [IsIso β₁] [IsIso β₂] [IsIso β]

/-- **Base change maps compose along a vertical edge** (the abstract content of Stacks 0E5F).
For two squares sharing the vertical edge `Rf'`, if the base change transformation of the
rectangle is the pasting of those of the two squares through `Lh ⋙ Lh' ≅ Lm` and
`Lg ⋙ Lg' ≅ Lk`, then so is the base change map `α` of the rectangle:
`α_rect = (a'' ⋆ e_m) ∘ (α_left ⋆ Lh) ∘ (Lg' ⋆ α_right) ∘ (e_k⁻¹ ⋆ a)`. -/
theorem map_app_horizontal
    (hβ : ∀ K, β.app K = em.inv.app (Rf.obj K) ≫ Lh'.map (β₁.app K) ≫ β₂.app (Lg.obj K) ≫
      Rf''.map (ek.hom.app K)) (K : DY) :
    (map adjF adjF'' adjM adjK β).app K =
      ek.inv.app (a.obj K) ≫ Lg'.map ((map adjF adjF' adjH adjG β₁).app K) ≫
        (map adjF' adjF'' adjH' adjG' β₂).app (Lh.obj K) ≫ a''.map (em.hom.app K) := by
  symm
  apply eq_map_app_of_counit
  have h₁ := map_counit adjF adjF' adjH adjG β₁ K
  have h₂ := map_counit adjF' adjF'' adjH' adjG' β₂ (Lh.obj K)
  have n₁ : β₂.app (Lg.obj (a.obj K)) ≫ Rf''.map (Lg'.map ((map adjF adjF' adjH adjG β₁).app K)) =
      Lh'.map (Rf'.map ((map adjF adjF' adjH adjG β₁).app K)) ≫
        β₂.app (a'.obj (Lh.obj K)) :=
    (β₂.naturality _).symm
  have n₂ : Rf''.map (a''.map (em.hom.app K)) ≫ adjF''.counit.app (Lm.obj K) =
      adjF''.counit.app (Lh'.obj (Lh.obj K)) ≫ em.hom.app K :=
    adjF''.counit.naturality _
  have n₃ : em.inv.app (Rf.obj (a.obj K)) ≫ Lh'.map (Lh.map (adjF.counit.app K)) ≫
      em.hom.app K = Lm.map (adjF.counit.app K) := by
    have hn : Lm.map (adjF.counit.app K) ≫ em.inv.app K =
        em.inv.app (Rf.obj (a.obj K)) ≫ Lh'.map (Lh.map (adjF.counit.app K)) :=
      em.inv.naturality (adjF.counit.app K)
    rw [← reassoc_of% hn, Iso.inv_hom_id_app, Category.comp_id]
  rw [hβ, Category.assoc, Category.assoc, Category.assoc, ← Rf''.map_comp_assoc,
    Iso.hom_inv_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% n₁, n₂, reassoc_of% h₂, ← n₃]
  simp only [← Lh'.map_comp_assoc, h₁]

end Horizontal


/-! ### Pasting along a horizontal edge (the abstract content of Stacks 0E5E) -/

section Vertical

variable {DX : Type u₁} {DY : Type u₂} {DZ : Type u₃} {DX' : Type u₄} {DY' : Type u₅}
  {DZ' : Type u₆} [Category.{v₁} DX] [Category.{v₂} DY] [Category.{v₃} DZ] [Category.{v₄} DX']
  [Category.{v₅} DY'] [Category.{v₆} DZ']
  {Rf : DX ⥤ DY} {a : DY ⥤ DX} {Rf' : DX' ⥤ DY'} {a' : DY' ⥤ DX'}
  {Rg : DY ⥤ DZ} {b : DZ ⥤ DY} {Rg' : DY' ⥤ DZ'} {b' : DZ' ⥤ DY'}
  {Rh : DX ⥤ DZ} {c : DZ ⥤ DX} {Rh' : DX' ⥤ DZ'} {c' : DZ' ⥤ DX'}
  {Lk : DX ⥤ DX'} {Rk : DX' ⥤ DX} {Ll : DY ⥤ DY'} {Rl : DY' ⥤ DY}
  {Lm : DZ ⥤ DZ'} {Rm : DZ' ⥤ DZ}
  (adjF : Rf ⊣ a) (adjF' : Rf' ⊣ a') (adjG : Rg ⊣ b) (adjG' : Rg' ⊣ b')
  (adjH : Rh ⊣ c) (adjH' : Rh' ⊣ c')
  (adjK : Lk ⊣ Rk) (adjL : Ll ⊣ Rl) (adjM : Lm ⊣ Rm)
  (β₁ : Rf ⋙ Ll ⟶ Lk ⋙ Rf') (β₂ : Rg ⋙ Lm ⟶ Ll ⋙ Rg') (β : Rh ⋙ Lm ⟶ Lk ⋙ Rh')
  (eh : Rf ⋙ Rg ≅ Rh) (eh' : Rf' ⋙ Rg' ≅ Rh')

/-- The right adjoint of a composite, identified with the composite of the right adjoints:
for `Rf ⊣ a`, `Rg ⊣ b`, `Rh ⊣ c` and `Rf ⋙ Rg ≅ Rh`, the isomorphism `a ∘ b ≅ c`. -/
def rightAdjointCompIso : b ⋙ a ≅ c :=
  ((adjF.comp adjG).ofNatIsoLeft eh).rightAdjointUniq adjH

/-- The trace of `Rh ⊣ c` read through `a ∘ b ≅ c` is the composite of the traces of
`Rf ⊣ a` and `Rg ⊣ b`. -/
theorem map_rightAdjointCompIso_hom_app_comp_counit (K : DZ) :
    Rh.map ((rightAdjointCompIso adjF adjG adjH eh).hom.app K) ≫ adjH.counit.app K =
      eh.inv.app (a.obj (b.obj K)) ≫ Rg.map (adjF.counit.app (b.obj K)) ≫ adjG.counit.app K := by
  simp [rightAdjointCompIso, Adjunction.ofNatIsoLeft]

variable [IsIso β₁] [IsIso β₂] [IsIso β]

/-- **Base change maps compose along a horizontal edge** (the abstract content of Stacks 0E5E).
For two squares sharing the horizontal edge `Ll`, if the base change transformation of the
rectangle is the pasting of those of the two squares through `Rf ⋙ Rg ≅ Rh` and
`Rf' ⋙ Rg' ≅ Rh'`, then the base change map `α` of the rectangle is
`α_rect = (b' ⋙ a' ≅ c') ∘ (a' ⋆ α_bot) ∘ (α_top ⋆ b) ∘ (c ≅ b ⋙ a)`. -/
theorem map_app_vertical
    (hβ : ∀ K, β.app K = Lm.map (eh.inv.app K) ≫ β₂.app (Rf.obj K) ≫ Rg'.map (β₁.app K) ≫
      eh'.hom.app (Lk.obj K)) (K : DZ) :
    (map adjH adjH' adjM adjK β).app K =
      Lk.map ((rightAdjointCompIso adjF adjG adjH eh).inv.app K) ≫
        (map adjF adjF' adjL adjK β₁).app (b.obj K) ≫
        a'.map ((map adjG adjG' adjM adjL β₂).app K) ≫
        (rightAdjointCompIso adjF' adjG' adjH' eh').hom.app (Lm.obj K) := by
  symm
  apply eq_map_app_of_counit
  set e := rightAdjointCompIso adjF adjG adjH eh
  set α₁ := map adjF adjF' adjL adjK β₁
  set α₂ := map adjG adjG' adjM adjL β₂
  have hc' := map_rightAdjointCompIso_hom_app_comp_counit adjF' adjG' adjH' eh' (Lm.obj K)
  have hc := map_rightAdjointCompIso_hom_app_comp_counit adjF adjG adjH eh K
  have h₁ := map_counit adjF adjF' adjL adjK β₁ (b.obj K)
  have h₂ := map_counit adjG adjG' adjM adjL β₂ K
  -- naturality of `eh'.inv`
  have nat : ∀ {X Y : DX'} (f : X ⟶ Y),
      Rh'.map f ≫ eh'.inv.app Y = eh'.inv.app X ≫ Rg'.map (Rf'.map f) :=
    fun f => eh'.inv.naturality f
  -- naturality of the trace of `Rf' ⊣ a'`
  have n₄ : Rf'.map (a'.map (α₂.app K)) ≫ adjF'.counit.app (b'.obj (Lm.obj K)) =
      adjF'.counit.app (Ll.obj (b.obj K)) ≫ α₂.app K :=
    adjF'.counit.naturality _
  -- naturality of `β₁` and `β₂`
  have n₅ : β₁.app (c.obj K) ≫ Rf'.map (Lk.map (e.inv.app K)) =
      Ll.map (Rf.map (e.inv.app K)) ≫ β₁.app (a.obj (b.obj K)) :=
    (β₁.naturality _).symm
  have n₆ : β₂.app (Rf.obj (c.obj K)) ≫
      Rg'.map (Ll.map (Rf.map (e.inv.app K) ≫ adjF.counit.app (b.obj K))) =
      Lm.map (Rg.map (Rf.map (e.inv.app K) ≫ adjF.counit.app (b.obj K))) ≫ β₂.app (b.obj K) :=
    (β₂.naturality _).symm
  -- naturality of `eh.inv`
  have n₇ : Rh.map (e.inv.app K) ≫ eh.inv.app (a.obj (b.obj K)) =
      eh.inv.app (c.obj K) ≫ Rg.map (Rf.map (e.inv.app K)) :=
    eh.inv.naturality _
  have hH : adjH.counit.app K = Rh.map (e.inv.app K) ≫ eh.inv.app (a.obj (b.obj K)) ≫
      Rg.map (adjF.counit.app (b.obj K)) ≫ adjG.counit.app K := by
    rw [← hc, ← Rh.map_comp_assoc, Iso.inv_hom_id_app, Rh.map_id, Category.id_comp]
  have e' : ∀ {Z : DZ'} (h : Rg'.obj (Rf'.obj (Lk.obj (c.obj K))) ⟶ Z),
      eh'.hom.app (Lk.obj (c.obj K)) ≫ eh'.inv.app (Lk.obj (c.obj K)) ≫ h = h := by
    intro Z h
    rw [Iso.hom_inv_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [hc', reassoc_of% (nat (a'.map (α₂.app K))),
    reassoc_of% (nat (α₁.app (b.obj K))), reassoc_of% (nat (Lk.map (e.inv.app K))), hβ,
    Category.assoc, Category.assoc, Category.assoc, e', ← Rg'.map_comp_assoc,
    ← Rg'.map_comp_assoc, ← Rg'.map_comp_assoc, ← Rg'.map_comp_assoc]
  simp only [Category.assoc]
  have h₁' : Ll.map (Rf.map (e.inv.app K)) ≫ β₁.app (a.obj (b.obj K)) ≫
      Rf'.map (α₁.app (b.obj K)) ≫ adjF'.counit.app (Ll.obj (b.obj K)) ≫ α₂.app K =
      Ll.map (Rf.map (e.inv.app K) ≫ adjF.counit.app (b.obj K)) ≫ α₂.app K := by
    rw [reassoc_of% h₁, Ll.map_comp_assoc]
  rw [n₄, reassoc_of% n₅, h₁', Rg'.map_comp, Category.assoc, reassoc_of% n₆, h₂, hH,
    reassoc_of% n₇]
  simp only [Functor.map_comp, Category.assoc]

end Vertical

end CategoryTheory.RightAdjointBaseChange

end
